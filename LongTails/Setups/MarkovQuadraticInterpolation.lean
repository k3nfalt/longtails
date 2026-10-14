import LongTails.Setups.SmoothAndConvex
import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.MeasurableSpace.Instances

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.MarkovQuadraticInterpolation

open OracleTemplate

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public where
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  α : ℝ

attribute [instance] Public.measurableE Public.borelE Public.countableE

structure Params extends Public where
  R : ℝ
  ε : ℝ

structure Model (q : Params) (m : ℕ) (π : ProbabilityMeasure (Fin m))
    (κ : Kernel (Fin m) (Fin m)) (H : Fin m → q.E →L[ℝ] q.E)
    (f : q.E → ℝ) (u : q.E) : Prop where
  stationary : κ ∘ₘ (π : Measure (Fin m)) = (π : Measure (Fin m))
  refresh : ∀ i j, ENNReal.ofReal q.α * (π : Measure (Fin m)) {j} ≤ κ i {j}
  symmetric : ∀ i, (H i).adjoint = H i
  positive : ∀ i x, 0 ≤ ⟪x, H i x⟫
  smooth : ∀ i x, ⟪x, H i x⟫ ≤ q.L * ‖x‖ ^ 2
  radius : ‖q.x0 - u‖ ≤ q.R
  population : ∀ x, f x - f u =
    ∫ i, ⟪x - u, H i (x - u)⟫ / 2 ∂(π : Measure (Fin m))

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := q.E → ℝ
  Query q := q.E
  Reply q := q.E
  Output q := q.E
  publicInput := Params.toPublic
  valid q := 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.α ∧ q.α ≤ 1 ∧ 0 < q.ε
  admissible q f O :=
    ∃ (m : ℕ) (π μ : ProbabilityMeasure (Fin m)) (κ : Kernel (Fin m) (Fin m))
      (hκ : IsMarkovKernel κ) (H : Fin m → q.E →L[ℝ] q.E) (u : q.E),
      Model q m π κ H f u ∧
      O = { Seed := fun _ => Fin m
            law := @LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw (Fin m) _ κ hκ μ
            answer := fun _ (_, x) i => H i (x - u) }
  successful q f output P :=
    Measurable output ∧ ∃ u, IsMinOn f Set.univ u ∧
      Integrable (fun ω => f (output ω) - f u) (P : Measure _) ∧
      (∫ ω, f (output ω) - f u ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.MarkovQuadraticInterpolation
