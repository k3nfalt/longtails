import LongTails.Setups.SimilarFiniteSumQuasar

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Setups.ContinuizedSimilarQuasar

open OracleTemplate

abbrev Params := LongTails.Setups.SimilarFiniteSumQuasar.Params

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.γ ∧ p.γ ≤ 1 ∧
    0 ≤ p.δ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ k i x seed, O.answer k (0, (i, x)) seed = gradient (f i) x) ∧
    (∀ x y, ‖gradient F x - gradient F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, (p.n : ℝ)⁻¹ * ∑ i,
      ‖(gradient (f i) x - gradient F x) -
        (gradient (f i) y - gradient F y)‖ ^ 2 ≤ p.δ ^ 2 * ‖x - y‖ ^ 2) ∧
    (∃ xstar, IsMinOn F Set.univ xstar ∧ F p.x0 - F xstar ≤ p.Δ ∧
      (∀ x, p.γ * F x + ⟪gradient F x, xstar - x⟫ +
        p.γ * p.μ / 2 * ‖xstar - x‖ ^ 2 ≤ p.γ * F xstar))
  successful p f output P :=
    ∃ xstar, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ xstar ∧
      Integrable (fun ω => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (output ω) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (P : Measure _) ∧
      (∫ ω, LongTails.Setups.FiniteSumSmoothAndConvex.objective f (output ω) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.ContinuizedSimilarQuasar
