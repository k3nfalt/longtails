import LongTails.Setups.ExpectedSmoothnessNonconvex

open MeasureTheory

namespace LongTails.Setups.NonnegativeSmoothSampleLoss

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  x0 : E
  L : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.completeE Params.measurableE
  Params.borelE Params.countableE Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := q.E → ℝ
  Query q := q.E × q.E
  Reply q := q.E × q.E
  Output q := q.E
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (loss : q.Ω → q.E → ℝ) (g : q.E → q.Ω → q.E)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, xy) ω => (g xy.1 ω, g xy.2 ω) } ∧
      (∀ ω x, 0 ≤ loss ω x) ∧ (∀ ω x, HasGradientAt (loss ω) (g x ω) x) ∧
      (∀ ω x y, ‖g x ω - g y ω‖ ≤ q.L * ‖x - y‖) ∧
      Measurable (Function.uncurry g) ∧ (∀ x, Integrable (fun ω => loss ω x) (p : Measure _)) ∧
      (∀ x, f x = ∫ ω, loss ω x ∂(p : Measure _)) ∧ f q.x0 ≤ q.Δ
  successful q f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.NonnegativeSmoothSampleLoss
