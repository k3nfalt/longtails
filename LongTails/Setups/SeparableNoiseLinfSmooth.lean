import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.SeparableNoiseLinfSmooth

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  S : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := EuclideanSpace ℝ (Fin q.d) → ℝ
  Query q := EuclideanSpace ℝ (Fin q.d)
  Reply q := EuclideanSpace ℝ (Fin q.d)
  Output q := EuclideanSpace ℝ (Fin q.d)
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.S ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : EuclideanSpace ℝ (Fin q.d) → q.Ω → EuclideanSpace ℝ (Fin q.d))
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)) (fstar : ℝ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y r, (∀ i, |x i - y i| ≤ r) →
        ∑ i, |gradient f x i - gradient f y i| ≤ q.L * r) ∧
      (∀ x, fstar ≤ f x) ∧ (∀ η, 0 < η → ∃ x, f x < fstar + η) ∧ f q.x0 - fstar ≤ q.Δ ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x i, Integrable (fun ω => (g x ω i - gradient f x i) ^ 2) p) ∧
      (∀ x, ∑ i, Real.sqrt (∫ ω, (g x ω i - gradient f x i) ^ 2 ∂p) ≤ q.S)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ∑ i, |gradient f (output ω) i|) (P : Measure _) ∧
      ∫ ω, ∑ i, |gradient f (output ω) i| ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.SeparableNoiseLinfSmooth
