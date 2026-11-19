import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StronglyConvexDueling

open OracleTemplate

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ball (d : ℕ) := Metric.closedBall (0 : Point d) 1

structure Params where
  d : ℕ
  [nonzero : NeZero d]
  μ : ℝ
  L : ℝ
  G : ℝ
  r : ℝ
  c : ℝ
  M : ℝ
  k : ℕ
  ε : ℝ

attribute [instance] Params.nonzero

structure Objective (p : Params) (f : Point p.d → ℝ) : Prop where
  differentiable : ∀ x, HasGradientAt f (gradient f x) x
  continuous_gradient : Continuous (gradient f)
  lipschitz : ∀ x ∈ Ball p.d, ∀ y ∈ Ball p.d, |f x - f y| ≤ p.G * ‖x - y‖
  smooth : ∀ x ∈ Ball p.d, ∀ y ∈ Ball p.d,
    ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖
  strongly_convex : ∀ x ∈ Ball p.d, ∀ y ∈ Ball p.d,
    f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y

structure Transfer (p : Params) (ρ : ℝ → ℝ) : Prop where
  differentiable : ∀ t, HasDerivAt ρ (deriv ρ t) t
  continuous_derivative : Continuous (deriv ρ)
  odd : ∀ t, ρ (-t) = -ρ t
  monotone : Monotone ρ
  bounded : ∀ t, |ρ t| ≤ 1
  slope_lower : ∀ t, |t| ≤ p.r → p.c * |t| ^ p.k ≤ deriv ρ t
  slope_upper : ∀ t, |t| ≤ p.r → deriv ρ t ≤ p.M

def score (b : Bool) : ℝ := if b then 1 else -1

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Ball p.d × Ball p.d
  Reply _ := Bool
  Output p := Ball p.d
  publicInput := id
  valid p := 0 < p.μ ∧ 0 < p.L ∧ 0 < p.G ∧ 0 < p.r ∧ 0 < p.c ∧ 0 < p.M ∧ 0 < p.ε
  admissible p f O := Objective p f ∧ ∃ ρ, Transfer p ρ ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ν : ProbabilityMeasure Ω)
      (P : ProbabilityMeasure (ℕ → Ω)) (g : (Ball p.d × Ball p.d) → Ω → Bool),
      StochasticGeneralizedSmoothAndConvex.IID (fun k (ω : ℕ → Ω) => ω k) ν P ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, (∫ z, score (g x z) ∂(ν : Measure Ω)) = ρ (f x.1.val - f x.2.val)) ∧
      O = { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
  successful p f out P := Measurable out ∧ ∃ u : Ball p.d, IsMinOn f (Ball p.d) u.val ∧
    Integrable (fun ω => f (out ω).val - f u.val) (P : Measure _) ∧
    (∫ ω, f (out ω).val - f u.val ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.StronglyConvexDueling
