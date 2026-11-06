import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic

open scoped RealInnerProductSpace

namespace LongTails.Setups.ConstrainedMinimaxSecondOrder

open OracleTemplate

structure Params where
  E : Type
  F : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normedF : NormedAddCommGroup F]
  [innerF : InnerProductSpace ℝ F]
  [finiteF : FiniteDimensional ℝ F]
  Y : Set F
  L : ℝ
  μ : ℝ
  ρ : ℝ
  Δ : ℝ
  B : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Params.normedE Params.innerE Params.finiteE
  Params.normedF Params.innerF Params.finiteF

abbrev Space (p : Params) := WithLp 2 (p.E × p.F)

noncomputable def value {p : Params} (f : Space p → ℝ) (x : p.E) : ℝ :=
  ⨆ y : p.Y, f (WithLp.toLp 2 (x, y.1))

structure Regularity (p : Params) (f : Space p → ℝ) : Prop where
  hasGradient : ∀ z, HasGradientAt f (gradient f z) z
  gradient_differentiable : Differentiable ℝ (gradient f)
  gradient_lipschitz : ∀ z w, ‖gradient f z - gradient f w‖ ≤ p.L * ‖z - w‖
  hessian_lipschitz : ∀ z w,
    ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) w‖ ≤ p.ρ * ‖z - w‖
  strongly_concave : ∀ x y y',
    f (WithLp.toLp 2 (x, y')) ≤ f (WithLp.toLp 2 (x, y)) +
      ⟪(gradient f (WithLp.toLp 2 (x, y))).snd, y' - y⟫ - p.μ / 2 * ‖y' - y‖ ^ 2

structure Assumptions (p : Params) (f : Space p → ℝ) : Prop extends Regularity p f where
  initial_gap : ∀ x, value f p.x0 - value f x ≤ p.Δ
  initial_gradient : ‖gradient f (WithLp.toLp 2 (p.x0, p.y0))‖ ≤ p.B

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p
  Reply p := ℝ × Space p × (Space p →L[ℝ] Space p)
  Output p := p.E
  publicInput := id
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 ≤ p.B ∧ 0 < p.ε ∧
    IsClosed p.Y ∧ Convex ℝ p.Y ∧ p.y0 ∈ p.Y
  admissible p f oracle :=
    Assumptions p f ∧
    (∀ k seed z, oracle.answer k (0, z) seed =
      (f z, gradient f z, fderiv ℝ (gradient f) z))
  successful p f output law :=
    Differentiable ℝ (value f) ∧
    ∀ᵐ ω ∂(law : MeasureTheory.Measure _), ‖gradient (value f) (output ω)‖ ≤ p.ε

end LongTails.Setups.ConstrainedMinimaxSecondOrder
