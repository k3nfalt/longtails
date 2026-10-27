import LongTails.Template
import LongTails.Setups.StochasticTwoSidedPL
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped RealInnerProductSpace

namespace LongTails.Setups.NonconvexPLSecondOrder

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
  L : ℝ
  μ : ℝ
  ρ : ℝ
  Δ : ℝ
  D : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Params.normedE Params.innerE Params.finiteE
  Params.normedF Params.innerF Params.finiteF

abbrev Space (p : Params) := WithLp 2 (p.E × p.F)

noncomputable def value {p : Params} (f : Space p → ℝ) (x : p.E) : ℝ :=
  StochasticTwoSidedPL.maxValue (fun x y => f (WithLp.toLp 2 (x, y))) x

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p → ℝ
  Query p := Space p
  Reply p := ℝ × Space p × (Space p →L[ℝ] Space p)
  Output p := p.E
  publicInput := id
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 ≤ p.D ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ z, HasGradientAt f (gradient f z) z) ∧
    Differentiable ℝ (gradient f) ∧
    (∀ z w, ‖gradient f z - gradient f w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ z w, ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) w‖ ≤ p.ρ * ‖z - w‖) ∧
    (∀ x, ∃ y, ∀ y', f (WithLp.toLp 2 (x, y')) ≤ f (WithLp.toLp 2 (x, y))) ∧
    (∀ x y, 2 * p.μ * (value f x - f (WithLp.toLp 2 (x, y))) ≤
      ‖(gradient f (WithLp.toLp 2 (x, y))).snd‖ ^ 2) ∧
    (∀ x, value f p.x0 - value f x ≤ p.Δ) ∧
    value f p.x0 - f (WithLp.toLp 2 (p.x0, p.y0)) ≤ p.D ∧
    (∀ k seed z, oracle.answer k (0, z) seed =
      (f z, gradient f z, fderiv ℝ (gradient f) z))
  successful p f output law :=
    Differentiable ℝ (value f) ∧ Differentiable ℝ (gradient (value f)) ∧
    ∀ᵐ ω ∂(law : MeasureTheory.Measure _),
      ‖gradient (value f) (output ω)‖ ≤ p.ε ∧
      ∀ v, -Real.sqrt (100 * p.ρ * Real.sqrt (p.L / p.μ) * (4 + p.L / p.μ) * p.ε) *
        ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient (value f)) (output ω) v⟫

end LongTails.Setups.NonconvexPLSecondOrder
