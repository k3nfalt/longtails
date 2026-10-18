import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.QuantileSymmetricRemainderConvex

open OracleTemplate

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def HasSymmetricRemainder (μ : Measure ℝ) (M : ℝ) : Prop :=
  ∃ S A : Measure ℝ,
    μ = S + A ∧
    S.map (fun z : ℝ => -z) = S ∧
    Integrable (fun z : ℝ => z) A ∧
    (∫ z : ℝ, z ∂A) = 0 ∧
    Integrable (fun z : ℝ => z ^ 2) A ∧
    (∫ z : ℝ, z ^ 2 ∂A) ≤ M

def NoiseCondition (μ : Measure ℝ) (r M : ℝ) : Prop :=
  HasSymmetricRemainder μ M ∧ μ {z | r < |z|} ≤ 1 / 64

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : Space d
  L : ℝ
  R : ℝ
  r : ℝ
  M : ℝ
  ε : ℝ

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Space q.d → ℝ
  Query q := Space q.d
  Reply q := Space q.d
  Output q := Space q.d
  publicInput q := q
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 < q.R ∧ 0 < q.r ∧ 0 ≤ q.M ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : Space q.d → q.Ω → Space q.d) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
    Measurable (Function.uncurry g) ∧
    ∀ x i, NoiseCondition
      ((p : Measure _).map (fun ω => (g x ω - gradient f x) i)) q.r q.M
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.QuantileSymmetricRemainderConvex
