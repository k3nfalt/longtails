import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.InnerProductSpace.ProdL2

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.RidgeClockTwoTapLogistic

open TwoSampleQuadraticPerceptron (Features Space margin direction)

structure Input where
  d : ℕ
  n : ℕ+
  x₀ : Space .conv d
  η : ℝ

abbrev Rows (u : Input) := Fin u.n → Features u.d

noncomputable def vote (m : ℝ) : ℝ := 1 / (1 + Real.exp m)

noncomputable def descent {u : Input} (X : Rows u) (z : Space .conv u.d) : Space .conv u.d :=
  (u.n : ℝ)⁻¹ • ∑ i, vote (margin .conv u.d (X i) z) • direction .conv u.d (X i) z

noncomputable def step {u : Input} (X : Rows u) (z : Space .conv u.d) : Space .conv u.d :=
  z + u.η • descent X z

noncomputable def radius {d : ℕ} (z : Space .conv d) : ℝ :=
  (z.1.1 ^ 2 + z.1.2 ^ 2 + ‖z.2‖ ^ 2) / 2

noncomputable def size {d : ℕ} (z : Space .conv d) : ℝ := Real.sqrt (2 * radius z)

noncomputable def work {u : Input} (X : Rows u) (z : Space .conv u.d) : ℝ :=
  (u.n : ℝ)⁻¹ * ∑ i, let m := margin .conv u.d (X i) z; vote m * m

def separates {u : Input} (X : Rows u) (z : Space .conv u.d) : Prop :=
  ∀ i, 0 < margin .conv u.d (X i) z

noncomputable def fit {u : Input} (X : Rows u) (z : Space .conv u.d) : Bool := by
  classical
  exact decide (separates X z)

noncomputable def answer {u : Input} (X : Rows u) (z : Space .conv u.d) : Space .conv u.d × Bool :=
  (descent X z, fit X z)

def family (u : Input) (A : Algorithm (Space .conv u.d) (Space .conv u.d × Bool) (Space .conv u.d)) : Prop :=
  ∃ point : A.State → Space .conv u.d,
    (∀ ω, point (A.initial ω) = u.x₀) ∧ (∀ s, A.query s = (0,point s)) ∧
    (∀ s q, point (A.update s q) = if q.2 then point s else point s + u.η • q.1) ∧
    ∀ s, A.output s = point s

structure Params where
  d : ℕ
  n : ℕ+
  x₀ : Space .conv d
  η : ℝ
  burn : ℕ
  block : ℕ+
  bins : ℕ
  knots : ℕ+
  lam : Fin knots → ℝ
  factor : ℝ
  filter : ℝ × ℝ
  R₀ : ℝ
  width : Fin bins → ℝ
  c : Fin bins → ℝ
  W : Fin bins → ℝ

def Params.input (p : Params) : Input := ⟨p.d,p.n,p.x₀,p.η⟩

def Params.atBin (p : Params) (f : Fin p.bins → ℝ) (i : ℕ) : ℝ :=
  if h : i < p.bins then f ⟨i,h⟩ else 0

noncomputable def Params.edge (p : Params) : ℕ → ℝ
  | 0 => p.R₀
  | i+1 => p.edge i + p.atBin p.width i

noncomputable def speed (p : Params) (i : ℕ) : ℝ :=
  2 * p.input.η * p.block * p.atBin p.c i * p.atBin p.W i

noncomputable def epochs (p : Params) : ℕ :=
  ⌈∑ i ∈ Finset.range p.bins, (p.edge (i+1)-p.edge i) / speed p i⌉₊

def valid (p : Params) : Prop :=
  0 < p.input.η ∧ 0 < p.factor ∧ p.filter.1^2 + p.filter.2^2 = 1 ∧ Monotone p.edge ∧ ∀ i < p.bins, 0 < p.atBin p.c i ∧ 0 < p.atBin p.W i

structure Source (u : Input) where
  cells : ℕ+
  degree : ℕ
  cell : ℕ → Fin cells
  left : Fin cells → ℝ
  width : Fin cells → ℝ
  coeff : Fin cells → Fin (degree+1) → Space .conv u.d
  r : ℕ → ℝ
  linear : ℕ → Space .conv u.d →ₗ[ℝ] Space .conv u.d
  error : ℕ → ℝ
  w : ℕ → ℝ
  e : ℕ → ℝ
  lo : ℕ → ℝ
  hi : ℕ → ℝ
  scoreError : ℕ → Fin u.n → ℝ

noncomputable def Source.point {u : Input} (s : Source u) (t : ℕ) : Space .conv u.d :=
  let i := s.cell t
  let a := ((t : ℝ)-s.left i)/s.width i
  ∑ k : Fin (s.degree+1), a ^ (k : ℕ) • s.coeff i k

noncomputable def Source.response {u : Input} (s : Source u) (X : Rows u)
    (a : ℕ) (v : Space .conv u.d) (err : ℕ → Space .conv u.d) : ℕ → Space .conv u.d
  | 0 => v
  | k+1 => s.linear (a+k) (s.response X a v err k) + (step X (s.point (a+k))-s.point (a+k+1)) + err (a+k)

def Source.encloses {u : Input} (s : Source u) (X : Rows u) (T : ℕ) : Prop :=
  size (u.x₀-s.point 0) ≤ s.r 0 ∧ ∀ j < T,
    (∀ v, size v ≤ s.r j → size (step X (s.point j+v)-s.point (j+1)) ≤ s.r (j+1)) ∨
    ∃ a ≤ j, (∀ l ∈ Finset.Icc a j, ∀ v, size v ≤ s.r l →
        size (step X (s.point l+v)-step X (s.point l)-s.linear l v) ≤ s.error l) ∧
      ∀ v, size v ≤ s.r a → ∀ err, (∀ l ∈ Finset.Icc a j, size (err l) ≤ s.error l) →
        size (s.response X a v err ((j+1)-a)) ≤ s.r (j+1)

noncomputable def mass {u : Input} (X : Rows u) (r : Features u.d) : ℝ :=
  (u.n : ℝ)⁻¹ * ∑ i, let m := ⟪X i,r⟫; vote m * m

noncomputable def ridgeCheck {u : Input} (Y : Rows u) (c r : Features u.d) (lam : ℝ) : Prop :=
  0 < lam ∧ (1 + ‖r‖)⁻¹ *
    ‖lam • (r-c) - (u.n : ℝ)⁻¹ • ∑ i, vote ⟪Y i,r⟫ • Y i‖ ≤ lam / 1000000

noncomputable def filtered {u : Input} (X : Rows u) (ab : ℝ × ℝ) : Rows u :=
  fun i => ab.1 • X i + ab.2 • TwoSampleQuadraticPerceptron.shift (X i)

noncomputable def profileRadius {u : Input} (r : Features u.d) : ℝ :=
  let D := (‖u.x₀.2‖^2-u.x₀.1.1^2-u.x₀.1.2^2)/2
  Real.sqrt (‖r‖^2 + D^2)

noncomputable def profileMargin {u : Input} (Y : Rows u) (r : Features u.d) : ℝ :=
  (Finset.univ : Finset (Fin u.n)).inf' Finset.univ_nonempty (fun i => ⟪Y i,r⟫)

noncomputable def interpolate (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | [a] => a.2
  | a :: b :: tail =>
    if x ≤ a.1 then a.2 else if x < b.1 then a.2+(x-a.1)*(b.2-a.2)/(b.1-a.1)
    else interpolate x (b::tail)

noncomputable def firstCrossing : List (ℝ × ℝ) → Option ℝ
  | [] => none
  | [a] => if 0 ≤ a.2 then some a.1 else none
  | a :: b :: tail =>
    if 0 ≤ a.2 then some a.1 else if 0 ≤ b.2 then some (a.1-a.2*(b.1-a.1)/(b.2-a.2))
    else firstCrossing (b::tail)

structure RidgeProfile (p : Params) where
  raw : Fin p.knots → Features p.input.d
  sections : ℕ+
  filteredAnchor : Fin sections → Features p.input.d
  penalty : Fin sections → ℝ
  causal : Bool

noncomputable def RidgeProfile.center {p : Params} (q : RidgeProfile p) (i : Fin q.sections) :
    Features p.input.d :=
  if h : i.val = 0 then 0 else if q.causal then
    let prev := q.filteredAnchor ⟨i.val-1, by omega⟩
    (2 * ‖q.filteredAnchor i‖ / (‖q.filteredAnchor i‖ + ‖prev‖)) • prev
  else 0

noncomputable def RidgeProfile.checked {p : Params} (q : RidgeProfile p) (X : Rows p.input) : Prop :=
  let Y := filtered X p.filter
  let rawData := List.ofFn (fun i => (profileRadius (u := p.input) (q.raw i), mass X (q.raw i)))
  let gates := List.ofFn (fun i => (profileRadius (u := p.input) (q.filteredAnchor i),
    profileMargin Y (q.filteredAnchor i)))
  (∀ i, ridgeCheck X 0 (q.raw i) (p.lam i)) ∧
  (∀ i, ridgeCheck Y (q.center i) (q.filteredAnchor i) (q.penalty i)) ∧
  StrictMono (fun i => ‖q.raw i‖) ∧ StrictMono (fun i => ‖q.filteredAnchor i‖) ∧
  (∀ i < p.bins, p.atBin p.W i = min (interpolate (p.edge i) rawData) (interpolate (p.edge (i+1)) rawData)) ∧
  ∃ R, firstCrossing gates = some R ∧ p.edge p.bins = p.factor*R

noncomputable def Source.gain {u : Input} (s : Source u) (t B : ℕ) : ℝ :=
  ∑ j ∈ Finset.range B, (2*u.η*s.w (t+j) + u.η^2*s.e (t+j))

def Source.dataBounds {u : Input} (s : Source u) (X : Rows u) (T : ℕ) : Prop :=
  ∀ t ≤ T, ∀ z, size (z-s.point t) ≤ s.r t →
    s.lo t ≤ radius z ∧ radius z ≤ s.hi t ∧ s.w t ≤ work X z ∧ s.e t ≤ radius (descent X z) ∧
    ∀ i, |margin .conv u.d (X i) z-margin .conv u.d (X i) (s.point t)| ≤ s.scoreError t i

noncomputable def scoreDrift {u : Input} (X : Rows u) (i : Fin u.n)
    (z : Space .conv u.d) : ℝ :=
  let d := descent X z
  let a := direction .conv u.d (X i) z
  u.η * (a.1.1*d.1.1 + a.1.2*d.1.2 + ⟪a.2,d.2⟫) +
    u.η^2 * margin .conv u.d (X i) d

structure ScoreWork (u : Input) where
  start : ℕ
  β : ℝ
  height : ℝ
  credit : ℕ → ℝ
  lower : ℕ → Fin u.n → ℝ

noncomputable def RidgeProfile.marginAt {p : Params} (q : RidgeProfile p) (X : Rows p.input)
    (R : ℝ) : ℝ :=
  let Y := filtered X p.filter
  interpolate R (List.ofFn (fun i => (profileRadius (u := p.input) (q.filteredAnchor i),
    profileMargin Y (q.filteredAnchor i))))

noncomputable def ScoreWork.ceiling {p : Params} (g : ScoreWork p.input) (q : RidgeProfile p)
    (X : Rows p.input) (s : Source p.input) (k : ℕ) : ℝ :=
  Real.exp (g.β*(g.height-q.marginAt X (s.lo (p.burn+p.block*k))-g.credit k))

noncomputable def ScoreWork.upper {u : Input} (g : ScoreWork u) (s : Source u) (X : Rows u)
    (t : ℕ) (i : Fin u.n) : ℝ :=
  Real.exp (-g.β*(margin .conv u.d (X i) (s.point t)-s.scoreError t i))

noncomputable def ScoreWork.lowerMass {u : Input} (g : ScoreWork u) (s : Source u) (X : Rows u)
    (t : ℕ) (i : Fin u.n) : ℝ :=
  Real.exp (-g.β*(margin .conv u.d (X i) (s.point t)+s.scoreError t i))

def ScoreWork.checked {p : Params} (g : ScoreWork p.input) (s : Source p.input)
    (q : RidgeProfile p) (X : Rows p.input) (L : ℕ) : Prop :=
  let t := fun k : ℕ => p.burn+p.block*k
  let C := g.ceiling q X s
  0 < g.β ∧ g.start ≤ L ∧ g.credit g.start = 0 ∧ (∀ k, 0 ≤ g.credit k) ∧
  (∑ i, g.upper s X (t g.start) i) ≤ C g.start ∧
  (∀ j ∈ Finset.Ico (t g.start) (t L), ∀ z, size (z-s.point j) ≤ s.r j →
    ∀ i, g.lower j i ≤ scoreDrift X i z) ∧
  (∀ k ∈ Finset.Ico g.start L,
    (∑ i, let d := ∑ j ∈ Finset.range p.block, g.lower (t k+j) i
          let b := Real.exp (-g.β*d)-C (k+1)/C k
          max (g.lowerMass s X (t k) i*b) (g.upper s X (t k) i*b)) ≤ 0) ∧
  ∀ k ≤ L, p.edge p.bins ≤ s.hi (t k) → g.start ≤ k ∧ 0 < q.marginAt X (s.lo (t k)) ∧ C k < 1

def geometry (p : Params) (X : Rows p.input) : Prop :=
  let B : ℕ := p.block
  let K := epochs p
  let t := fun k : ℕ => p.burn+B*k
  ∃ s : Source p.input, ∃ q : RidgeProfile p, ∃ L ≤ K,
    (L = K ∨ p.edge p.bins ≤ p.edge 0 + s.gain (t 0) (t L - t 0)) ∧ q.checked X ∧
    (∀ j, 0 < s.width j) ∧ (∀ j ≤ t L, let i := s.cell j
      s.left i ≤ (j : ℝ) ∧ (j : ℝ) ≤ s.left i+s.width i) ∧
    s.encloses X (t L) ∧ s.dataBounds X (t L) ∧ p.edge 0 ≤ s.lo (t 0) ∧
    (∀ k < L, 0 < s.gain (t k) B ∧
      ∀ R ∈ Set.Icc (s.lo (t k)) (s.hi (t k)), ∀ i < p.bins,
        p.edge i < R+s.gain (t k) B → R < p.edge (i+1) → speed p i ≤ s.gain (t k) B) ∧
    ((∀ k ≤ L, p.edge p.bins ≤ s.hi (t k) →
      ∀ i, s.scoreError (t k) i < margin .conv p.input.d (X i) (s.point (t k))) ∨
      ∃ g : ScoreWork p.input, g.checked s q X L)

noncomputable def spec : Setup where
  Params := Params
  Public := Input
  Instance := Rows
  publicInput := Params.input
  Query u := Space .conv u.d
  Reply u := Space .conv u.d × Bool
  Output u := Space .conv u.d
  valid := valid
  admissible p X o := geometry p X ∧ ∀ h q ξ, o.answer h (0,q) ξ = answer X q
  allowedAlgorithm := family
  successful _ X out _ := ∀ ω, separates X (out ω)

end LongTails.Setups.RidgeClockTwoTapLogistic
