import LongTails.Algorithms.HeterogeneousAdam
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.HeterogeneousSymmetricFirstMoment

open OracleTemplate LongTails.Algorithms.HeterogeneousAdam

structure Params where
  bodyDim : ℕ
  headDim : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  M : ℝ
  σBody : ℝ
  σHead : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x₀ : Point bodyDim headDim

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Point q.bodyDim q.headDim → ℝ
  Query q := Point q.bodyDim q.headDim
  Reply q := Point q.bodyDim q.headDim
  Output q := Point q.bodyDim q.headDim
  publicInput q := q
  valid q := 0 < q.bodyDim + q.headDim ∧ 0 < q.L ∧ 0 ≤ q.M ∧
    0 ≤ q.σBody ∧ 0 ≤ q.σHead ∧ 0 < q.Δ ∧ 0 < q.ε ∧ 0 < q.δ
  admissible q f O :=
    ∃ (g : Point q.bodyDim q.headDim → q.Ω → Point q.bodyDim q.headDim)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)) (K : q.Ω → ℝ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x₀ - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, ∫ ω, ∑ i : Fin q.bodyDim,
        |(g x ω - gradient f x) (.inl i)| ∂p ≤ q.σBody) ∧
      (∀ x, Integrable (fun ω => ∑ i : Fin q.headDim,
        ((g x ω - gradient f x) (.inr i)) ^ 2) p) ∧
      (∀ x, ∫ ω, ∑ i : Fin q.headDim,
        ((g x ω - gradient f x) (.inr i)) ^ 2 ∂p ≤ q.σHead ^ 2) ∧
      (∀ x (i : Fin q.bodyDim),
        (p : Measure _).map (fun ω => (g x ω - gradient f x) (.inl i)) =
        (p : Measure _).map (fun ω => -(g x ω - gradient f x) (.inl i))) ∧
      Measurable K ∧ Integrable K p ∧ (∫ ω, K ω ∂p) ≤ q.M ∧
      (∀ᵐ ω ∂(p : Measure _), 0 ≤ K ω ∧ ∀ x y (i : Fin q.bodyDim),
        |(g x ω - gradient f x) (.inl i) - (g y ω - gradient f y) (.inl i)| ≤
          K ω * ‖x - y‖)
  successful q f out P :=
    Measurable out ∧ Integrable (fun ω => ‖gradient f (out ω)‖) (P : Measure _) ∧
      (∫ ω, ‖gradient f (out ω)‖ ∂(P : Measure _)) ≤ q.ε
  allowedAlgorithm q A := ∃ cfg : Config,
    cfg.α = 9 / 10 ∧ cfg.β = 999 / 1000 ∧ cfg.δ = q.δ ∧ 0 < cfg.r₀ ∧
    (∀ t, 0 < cfg.bodyStep t) ∧ (∀ t, 0 < cfg.headStep t) ∧ A = method cfg q.x₀

end LongTails.Setups.HeterogeneousSymmetricFirstMoment
