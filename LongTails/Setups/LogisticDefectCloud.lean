import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.LogisticDefectCloud

open TwoSampleQuadraticPerceptron (Features shift)

abbrev Weights (d : ℕ) := EuclideanSpace ℝ (Fin 2 ⊕ Fin d)

structure Params where
  d : ℕ
  n : ℕ+
  L : ℝ
  μ : ℝ
  a : ℝ
  r : ℝ
  ρ : ℝ

structure Data (p : Params) where
  reference : Features p.d
  negative : Fin p.n → Features p.d

noncomputable def sumFeature {d : ℕ} (b : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (b + shift b)

noncomputable def diffFeature {d : ℕ} (b : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (b - shift b)

structure Geometry (p : Params) (D : Data p) where
  e : Features p.d
  u : Features p.d
  v : Features p.d
  norm_e : ‖e‖ = 1
  norm_u : ‖u‖ = 1
  norm_v : ‖v‖ = 1
  eu : ⟪e,u⟫ = 0
  ev : ⟪e,v⟫ = 0
  uv : ⟪u,v⟫ = 0
  z : Fin p.n → Features p.d
  y : Fin p.n → Features p.d
  reference_sum : sumFeature D.reference = p.L • e
  reference_diff : diffFeature D.reference = 0
  negative_sum : ∀ i, sumFeature (D.negative i) =
    p.L • ((1 + p.μ * p.a) • e - (p.μ * Real.sqrt (1 - p.a ^ 2)) • u + z i)
  negative_diff : ∀ i, diffFeature (D.negative i) = p.L • (-(p.μ • v) + y i)
  centered_z : ∑ i, z i = 0
  centered_y : ∑ i, y i = 0
  bound_z : ∀ i, ‖z i‖ ≤ 1
  bound_y : ∀ i, ‖y i‖ ≤ 1
  orthogonal : ∀ i, ∀ b ∈ ({e,u,v} : Set (Features p.d)), ⟪b,z i⟫ = 0 ∧ ⟪b,y i⟫ = 0

noncomputable def pack {d : ℕ} (s t : ℝ) (w : Features d) : Weights d :=
  WithLp.toLp 2 (Sum.elim ![s,t] w)

noncomputable def readout {d : ℕ} (x : Weights d) : Features d :=
  WithLp.toLp 2 (fun i => x (.inr i))

noncomputable def margin {d : ℕ} (b : Features d) (x : Weights d) : ℝ :=
  x (.inl 0) * ⟪sumFeature b, readout x⟫ + x (.inl 1) * ⟪diffFeature b, readout x⟫

noncomputable def direction {d : ℕ} (b : Features d) (x : Weights d) : Weights d :=
  pack ⟪sumFeature b, readout x⟫ ⟪diffFeature b, readout x⟫
    (x (.inl 0) • sumFeature b + x (.inl 1) • diffFeature b)

abbrev Index (p : Params) := Fin (2 * (p.n : ℕ))
abbrev Query (p : Params) := Index p × Weights p.d

noncomputable def input {p : Params} (D : Data p) (i : Index p) : Features p.d :=
  if i.val < p.n then D.reference else -D.negative (Fin.ofNat p.n (i.val - p.n))

structure Reply (d : ℕ) where
  margin : ℝ
  direction : Weights d

noncomputable def answer {p : Params} (D : Data p) (q : Query p) : Reply p.d :=
  ⟨margin (input D q.1) q.2, direction (input D q.1) q.2⟩

noncomputable def loss {p : Params} (D : Data p) (w : Weights p.d) : ℝ :=
  (∑ i : Index p, Real.log (1 + Real.exp (-(answer D (i,w)).margin))) / (2*p.n : ℝ)

def Separates {p : Params} (D : Data p) (w : Weights p.d) : Prop :=
  ∀ i, 0 < (answer D (i,w)).margin

structure Scan (p : Params) where
  point : Weights p.d
  cursor : Index p
  total : Weights p.d
  correct : Bool
  stopped : Bool

noncomputable def start (p : Params) (g : Weights p.d) : Scan p :=
  ⟨(p.r / ‖g‖) • g, ⟨0, by have := p.n.pos; omega⟩, 0, true, false⟩

noncomputable def advance (p : Params) (η : ℝ) (s : Scan p) (r : Reply p.d) : Scan p :=
  if s.stopped then s else
    let total := s.total + Real.sigmoid (-r.margin) • r.direction
    let correct := s.correct && decide (0 < r.margin)
    if h : s.cursor.val + 1 < 2 * (p.n : ℕ) then
      { s with cursor := ⟨_, h⟩, total, correct }
    else if correct then { s with stopped := true }
    else ⟨s.point + (η / (2 * p.n)) • total, ⟨0, by have := p.n.pos; omega⟩, 0, true, false⟩

def family (p : Params) (A : Algorithm (Query p) (Reply p.d) (Weights p.d)) : Prop :=
  ∃ (η : ℝ) (seed : A.Seed → Weights p.d) (view : A.State → Scan p),
    0 < η ∧ Measurable seed ∧ (A.law : Measure _).map seed = ProbabilityTheory.stdGaussian _ ∧
    (∀ g, view (A.initial g) = start p (seed g)) ∧
    (∀ s, A.query s = (0, (view s).cursor, (view s).point)) ∧
    (∀ s r, view (A.update s r) = advance p η (view s) r) ∧
    (∀ s, A.output s = (view s).point)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  Instance := Data
  Query := Query
  Reply p := Reply p.d
  Output p := Weights p.d
  valid p := 3 ≤ p.d ∧ 0 < p.L ∧ 0 < p.μ ∧ p.μ ≤ 1/10 ∧ 0 < p.a ∧ p.a ≤ 1/16 ∧
    0 < p.ρ ∧ p.ρ < 1 ∧ 0 < p.r ∧
    p.r * Real.sqrt p.L ≤ (p.a * p.μ * p.ρ / (2^20 * (p.d + 2 : ℝ)))^4
  admissible p D O := Nonempty (Geometry p D) ∧
    ∀ history q seed, O.answer history q seed = answer D q.2
  successful p D out P := (P : Measure _) {ω | ¬Separates D (out ω)} ≤ ENNReal.ofReal p.ρ
  allowedAlgorithm := family

end LongTails.Setups.LogisticDefectCloud
