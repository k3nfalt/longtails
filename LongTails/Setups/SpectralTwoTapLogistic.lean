import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.SpectralTwoTapLogistic

open TwoSampleQuadraticPerceptron (Features shift)

abbrev Taps := WithLp 2 (ℝ × ℝ)
abbrev State (d : ℕ) := WithLp 2 (Taps × Features d)

noncomputable def score {d : ℕ} (x : Features d) (z : State d) : ℝ :=
  TwoSampleQuadraticPerceptron.margin .conv d x ((z.fst.fst,z.fst.snd),z.snd)

noncomputable def action {d : ℕ} (x : Features d) (z : State d) : State d :=
  let u := TwoSampleQuadraticPerceptron.direction .conv d x ((z.fst.fst,z.fst.snd),z.snd)
  WithLp.toLp 2 (WithLp.toLp 2 u.1,u.2)

structure Input where
  d : ℕ
  n : ℕ+
  start : State d
  η : ℝ

abbrev Images (u : Input) := Fin u.n → Features u.d

noncomputable def risk {u : Input} (X : Images u) (z : State u.d) : ℝ :=
  (u.n : ℝ)⁻¹ * ∑ i, Real.log (1 + Real.exp (-score (X i) z))

noncomputable def descent {u : Input} (X : Images u) (z : State u.d) : State u.d :=
  (u.n : ℝ)⁻¹ • ∑ i, Real.sigmoid (-score (X i) z) • action (X i) z

noncomputable def hessian {u : Input} (X : Images u) (z v : State u.d) : State u.d :=
  (u.n : ℝ)⁻¹ • ∑ i,
    let q := Real.sigmoid (-score (X i) z)
    let j := action (X i) z
    (q*(1-q)*⟪j,v⟫) • j - q • action (X i) v

def correct {u : Input} (X : Images u) (z : State u.d) : Prop :=
  ∀ i, 0 < score (X i) z

def family {E : Type} [Add E] [SMul ℝ E] (z₀ : E) (A : Algorithm E E E) : Prop :=
  ∃ (η : ℝ) (point : A.State → E), 0 < η ∧
    (∀ ω, point (A.initial ω) = z₀) ∧
    (∀ s, A.query s = (0,point s)) ∧
    (∀ s r, point (A.update s r) = point s + η • r) ∧
    (∀ s, A.output s = point s)

structure Params where
  input : Input
  K : ℕ
  d : ℝ
  W : ℝ

def valid (p : Params) : Prop :=
  0 < p.input.η ∧ 0 < p.d ∧ 0 < p.W ∧ p.W ≤ 4*p.d

abbrev Modes (u : Input) := Fin (u.d+2)

structure Spectrum {u : Input} (X : Images u) where
  center : State u.d
  basis : OrthonormalBasis (Modes u) ℝ (State u.d)
  eigenvalue : Modes u → ℝ
  clipped : Bool
  eigen : ∀ j, hessian X center (basis j) = eigenvalue j • basis j

noncomputable def Spectrum.multiplier {u : Input} {X : Images u} (s : Spectrum X)
    (j : Modes u) : ℝ :=
  if s.clipped then max (-1) (1-u.η*s.eigenvalue j) else 1-u.η*s.eigenvalue j

noncomputable def Spectrum.move {u : Input} {X : Images u} (s : Spectrum X)
    (v : State u.d) : State u.d :=
  s.basis.repr.symm (WithLp.toLp 2 (fun j => s.multiplier j*s.basis.repr v j))

noncomputable def Spectrum.work {u : Input} {X : Images u} (s : Spectrum X)
    (i : Fin u.n) (j : Modes u) : ℝ :=
  ((s.basis.repr (action (X i) s.center) j)*(s.basis.repr (u.η • descent X s.center) j))*
    (1+s.multiplier j)

structure Source (u : Input) where
  point : ℕ → State u.d
  linear : ℕ → State u.d →L[ℝ] State u.d
  width : ℕ → ℝ
  defect : ℕ → ℝ

noncomputable def Source.response {u : Input} (q : Source u) (a : ℕ) (v : State u.d)
    (e : ℕ → State u.d) : ℕ → State u.d
  | 0 => v
  | k+1 => q.linear (a+k) (q.response a v e k) + e (a+k)

noncomputable def Source.encloses {u : Input} (q : Source u) (X : Images u) (T : ℕ) : Prop :=
  ‖u.start-q.point 0‖ ≤ q.width 0 ∧
  (∀ t, t+1 < T → ∀ v, ‖v‖ ≤ q.width t →
    ‖q.point t + v + u.η • descent X (q.point t+v)-q.point (t+1)-q.linear t v‖ ≤
      q.defect t) ∧
  ∀ t, 0 < t → t < T → ∃ a < t, ∀ v, ‖v‖ ≤ q.width a →
    ∀ e, (∀ j ∈ Finset.Ico a t, ‖e j‖ ≤ q.defect j) →
      ‖q.response a v e (t-a)‖ ≤ q.width t

noncomputable def Spectrum.remainder {u : Input} {X : Images u} (s : Spectrum X)
    (z : State u.d) : State u.d :=
  u.η • (descent X z-descent X s.center) + (z-s.center) - s.move (z-s.center)

noncomputable def Spectrum.affine {u : Input} {X : Images u} (s : Spectrum X) :
    ℕ → State u.d
  | 0 => 0
  | t+1 => s.move (s.affine t) + u.η • descent X s.center

noncomputable def Spectrum.correction {u : Input} {X : Images u} (s : Spectrum X)
    (q : Source u) (K : ℕ) : ℕ → State u.d
  | 0 => q.point K-s.center
  | t+1 => s.move (s.correction q K t) + s.remainder (q.point (K+t))

noncomputable def propagation (κ : ℝ) (r : ℝ) (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => r
  | t+1 => κ*propagation κ r δ t + δ t

noncomputable def curvature {d : ℕ} (x : Features d) : ℝ :=
  Real.sqrt (‖x‖^2+|⟪x,shift x⟫|)

noncomputable def scoreError {d : ℕ} (x : Features d) (z : State d) (r : ℝ) : ℝ :=
  ‖action x z‖*r + curvature x*r^2/2

noncomputable def geometry (p : Params) (X : Images p.input) : Prop :=
  let N := ⌈2*p.d/p.W⌉₊
  let T := 2*N
  ∃ (i₀ : Fin p.input.n) (s : Spectrum X) (q : Source p.input) (R σ κ : ℝ) (δ : ℕ → ℝ),
    let ρ := 1-p.W/(4*p.d)
    let w := s.work i₀
    let x := fun j => (s.multiplier j)^2
    let a := s.affine T
    let c := s.correction q p.K T
    let err := propagation κ (q.width p.K) δ T
    let base := fun i => score (X i) (q.point p.K) + ⟪action (X i) s.center,a⟫
    let loss := fun i => max 0 (-(score (X i) s.center-score (X i) (q.point p.K) +
      ⟪action (X i) s.center,c⟫ + score (X i) (a+c))) +
      scoreError (X i) (s.center+(a+c)) err
    (s.center = q.point p.K ∨
      s.center = (1/2 : ℝ) • (q.point p.K+q.point (p.K+1))) ∧
    score (X i₀) (q.point p.K) < 0 ∧
    q.encloses X (p.K+T) ∧
    (∀ t < T, ∀ v, ‖v‖ ≤ q.width (p.K+t) →
      ‖s.remainder (q.point (p.K+t)+v) - s.remainder (q.point (p.K+t))‖ ≤ δ t) ∧
    (∀ j, |s.multiplier j| ≤ κ ∧ x j ≤ R) ∧
    0 ≤ σ ∧ ρ ≤ R ∧ p.W = ∑ j, w j ∧
    (∀ t ∈ Set.Icc 0 R, (4*p.W/5)*max (ρ-t) 0 ≤
      σ*max (R-t) 0 + ∑ j, w j*max (x j-t) 0) ∧
    -p.d ≤ score (X i₀) (q.point p.K) ∧
    loss i₀ + σ*(∑ j ∈ Finset.range N, R^j) ≤ p.d/4 ∧
    ∀ i ≠ i₀, 0 < base i ∧ loss i ≤ 3*base i/4

noncomputable def spec : Setup where
  Params := Params
  Public := Input
  publicInput := Params.input
  Instance := Images
  Query u := State u.d
  Reply u := State u.d
  Output u := State u.d
  valid := valid
  admissible p X O := geometry p X ∧ ∀ k q ω, O.answer k q ω = descent X q.2
  successful _ X out _ := ∀ ω, correct X (out ω)
  allowedAlgorithm u := family u.start

end LongTails.Setups.SpectralTwoTapLogistic
