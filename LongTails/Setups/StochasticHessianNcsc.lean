import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StochasticHessianNcsc

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  F : Type
  [normedF : NormedAddCommGroup F]
  [innerF : InnerProductSpace ℝ F]
  [finiteF : FiniteDimensional ℝ F]
  [measurableF : MeasurableSpace F]
  [borelF : BorelSpace F]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  μ : ℝ
  ρ : ℝ
  σ : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Params.normedE Params.innerE Params.finiteE Params.measurableE Params.borelE
  Params.normedF Params.innerF Params.finiteF Params.measurableF Params.borelF Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → p.F → ℝ
  Query p := p.E × p.F
  Reply p := p.E × p.F
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 < q.ρ ∧ 0 < q.σ ∧ 0 ≤ q.Δ ∧ 0 ≤ q.G ∧ 0 < q.ε
  admissible q f O :=
    ∃ (gx : q.E × q.F → q.E) (gy : q.E × q.F → q.F)
      (Hx : q.E × q.F → (q.E × q.F →L[ℝ] q.E)) (Hy : q.E × q.F → (q.E × q.F →L[ℝ] q.F))
      (ox : q.E × q.F → q.Ω → q.E) (oy : q.E × q.F → q.Ω → q.F)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, z) ω => (ox z ω, oy z ω) } ∧
      (∀ x y, HasGradientAt (fun x' => f x' y) (gx (x, y)) x) ∧
      (∀ x y, HasGradientAt (fun y' => f x y') (gy (x, y)) y) ∧
      (∀ z, HasFDerivAt gx (Hx z) z) ∧
      (∀ z, HasFDerivAt gy (Hy z) z) ∧
      (∀ z z' : q.E × q.F, ‖gx z - gx z'‖ ^ 2 + ‖gy z - gy z'‖ ^ 2 ≤
        q.L ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2)) ∧
      (∀ (z z' : q.E × q.F) (u : q.E) (v : q.F),
        ‖(Hx z - Hx z') (u, v)‖ ^ 2 + ‖(Hy z - Hy z') (u, v)‖ ^ 2 ≤
          q.ρ ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2)) ∧
      (∀ x y y', f x y' ≤ f x y + ⟪gy (x, y), y' - y⟫ - q.μ / 2 * ‖y' - y‖ ^ 2) ∧
      (∀ x y, ∃ y', f q.x0 y - f x y' ≤ q.Δ) ∧
      ‖gy (q.x0, q.y0)‖ ≤ q.G ∧
      Measurable (Function.uncurry ox) ∧ Measurable (Function.uncurry oy) ∧
      (∀ z, Integrable (ox z) p) ∧ (∀ z, Integrable (oy z) p) ∧
      (∀ z, ∫ ω, ox z ω ∂p = gx z) ∧ (∀ z, ∫ ω, oy z ω ∂p = gy z) ∧
      (∀ z, Integrable (fun ω => ‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2) p) ∧
      (∀ z, ∫ ω, ‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2 ∂p ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧ (∃ ys : q.E → q.F, ∀ x y, f x y ≤ f x (ys x)) ∧
      ∀ ys : q.E → q.F, (∀ x y, f x y ≤ f x (ys x)) →
        Integrable (fun ω => ‖gradient (fun x => f x (ys x)) (output ω)‖) (P : Measure _) ∧
        ∫ ω, ‖gradient (fun x => f x (ys x)) (output ω)‖ ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticHessianNcsc
