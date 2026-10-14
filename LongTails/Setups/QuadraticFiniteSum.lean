import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Setups.QuadraticFiniteSum

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  μ : ℝ
  R : ℝ
  G : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE
  Params.measurableE Params.borelE Params.nonzero

structure Instance (q : Params) where
  A : Fin q.n → q.E →L[ℝ] q.E
  b : Fin q.n → q.E

noncomputable def objective {q : Params} (f : Instance q) (x : q.E) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, (⟪x, f.A i x⟫ / 2 + ⟪f.b i, x⟫)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query q := Fin q.n × q.E
  Reply q := q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.G ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ i, (f.A i).toLinearMap.IsSymmetric) ∧
    (∀ i, ‖f.A i‖ ≤ q.L) ∧
    (∀ x, q.μ * ‖x‖ ^ 2 ≤ (q.n : ℝ)⁻¹ * ∑ i, ⟪x, f.A i x⟫) ∧
    (∀ k seed i x, oracle.answer k (0, (i, x)) seed = f.A i x + f.b i) ∧
    (∃ xstar, (∑ i, (f.A i xstar + f.b i)) = 0 ∧
      ‖q.x0 - xstar‖ ≤ q.R ∧ ∀ i, ‖f.A i xstar + f.b i‖ ≤ q.G)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (objective f) Set.univ xstar ∧
      Integrable (fun ω => objective f (output ω) - objective f xstar) (P : Measure _) ∧
      (∫ ω, objective f (output ω) - objective f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.QuadraticFiniteSum
