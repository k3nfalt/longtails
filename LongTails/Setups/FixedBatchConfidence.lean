import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.FixedBatchConfidence

open OracleTemplate

abbrev Space := EuclideanSpace ℝ (Fin 2)

structure Public where
  L : ℝ
  x0 : Space

structure Params extends Public where
  R : ℝ
  ε : ℝ
  δ : ℝ

structure Model (q : Params) (p : ProbabilityMeasure Space)
    (f : Space → ℝ) (u : Space) : Prop where
  bounded : ∀ᵐ a ∂(p : Measure Space), ‖a‖ ^ 2 ≤ q.L
  radius : ‖q.x0 - u‖ ≤ q.R
  population : ∀ x, f x = ∫ a, ⟪a, x - u⟫ ^ 2 / 2 ∂(p : Measure Space)

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance _ := Space → ℝ
  Query _ := Space
  Reply _ := Space
  Output _ := Space
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 < q.R ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (p : ProbabilityMeasure Space) (P : ProbabilityMeasure (ℕ → Space)) (u : Space),
      Model q p f u ∧
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Space) => ξ k)
        (p : Measure Space) (P : Measure (ℕ → Space)) ∧
      O = { Seed := fun _ => Space
            law := P
            answer := fun _ (_, x) a => ⟪a, x - u⟫ • a }
  successful q f output P :=
    Measurable output ∧ ∃ u, IsMinOn f Set.univ u ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f u} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.FixedBatchConfidence
