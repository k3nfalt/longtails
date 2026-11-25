import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.CyclicLogisticFeatureLearning

open TwoSampleQuadraticPerceptron (Features shift margin direction)
open ManySampleConvolutionalPerceptron (Space Reply)

structure Params where
  d : ℕ
  n : ℕ+
  μ : ℝ
  κ : ℝ
  ρ : ℝ

abbrev Data (p : Params) := Fin p.n → Features p.d
abbrev Query (p : Params) := Fin p.n × Space p.d

noncomputable def sumFeature {d : ℕ} (b : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (b + shift b)

noncomputable def diffFeature {d : ℕ} (b : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (b - shift b)

structure Geometry (p : Params) (D : Data p) : Prop where
  sum_bound : ∀ i, ‖sumFeature (D i)‖ ≤ 1
  diff_bound : ∀ i, ‖diffFeature (D i)‖ ≤ p.μ
  orthogonal : ∀ i j, ⟪sumFeature (D i), diffFeature (D j)⟫ = 0
  nonseparable : ∀ v ∈ Submodule.span ℝ (Set.range (sumFeature ∘ D)),
    ∃ i, ⟪sumFeature (D i), v⟫ ≤ -p.ρ * ‖v‖
  separable : ∃ u : Features p.d, ‖u‖ = 1 ∧ ∀ i, p.μ * p.κ ≤ ⟪diffFeature (D i), u⟫

noncomputable def answer (p : Params) (D : Data p) (q : Query p) : Reply p.d :=
  ⟨margin .conv p.d (D q.1) q.2, direction .conv p.d (D q.1) q.2⟩

structure Scan (p : Params) where
  point : Space p.d
  cursor : Fin p.n
  total : Space p.d
  correct : Bool
  stopped : Bool

noncomputable def start (p : Params) : Scan p :=
  ⟨((1, 0), 0), ⟨0, p.n.pos⟩, 0, true, false⟩

noncomputable def advance (p : Params) (η : ℝ) (s : Scan p) (r : Reply p.d) : Scan p :=
  if s.stopped then s else
    let total := s.total + (1 / (1 + Real.exp r.margin)) • r.direction
    let correct := s.correct && decide (0 < r.margin)
    if h : s.cursor.val + 1 < p.n then
      { s with cursor := ⟨_, h⟩, total, correct }
    else if correct then { s with stopped := true }
    else ⟨s.point + (η / p.n) • total, ⟨0, p.n.pos⟩, 0, true, false⟩

def family (p : Params) (A : Algorithm (Query p) (Reply p.d) (Space p.d)) : Prop :=
  ∃ (η : ℝ) (view : A.State → Scan p), 0 < η ∧
    (∀ ω, view (A.initial ω) = start p) ∧
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
  Output p := Space p.d
  valid p := 0 < p.μ ∧ p.μ ≤ 1 ∧ 0 < p.κ ∧ p.κ ≤ 1 ∧ 0 < p.ρ ∧ p.ρ ≤ 1 ∧ 0 < p.d ∧ Even p.d
  admissible p D oracle := Geometry p D ∧
    ∀ history q seed, oracle.answer history q seed = answer p D q.2
  successful p D output _ := ∀ ω i, 0 < margin .conv p.d (D i) (output ω)
  allowedAlgorithm := family

end LongTails.Setups.CyclicLogisticFeatureLearning
