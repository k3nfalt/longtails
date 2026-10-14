import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open OracleTemplate

abbrev Params := LongTails.Setups.StochasticGeneralizedSmoothAndConvex.Params

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.L0 ∧ 0 ≤ q.L1 ∧ 0 < q.R ∧ 0 < q.Δ ∧
    0 ≤ q.σ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ < 1
  admissible q f O :=
    ∃ (g : q.E → q.Ω → q.E) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → q.Ω)),
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
    O = { Seed := fun _ => q.Ω
          law := P
          answer := fun _ (_, x) seed => g x seed } ∧
    ConvexOn ℝ Set.univ f ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ q.L0 + q.L1 * ‖gradient f x‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0-xstar‖ ≤ q.R ∧ f q.x0-f xstar ≤ q.Δ) ∧
    LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient q.E q.Ω (p : Measure _) f g q.σ
  successful q f output P :=
    Measurable output ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
      (P : Measure _) {ω | q.ε < f (output ω) - f xstar} ≤ ENNReal.ofReal q.δ

end LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
