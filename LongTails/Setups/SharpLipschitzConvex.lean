import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.SharpLipschitzConvex

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  d : ℕ
  L : ℝ
  μ : ℝ
  D : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

def IsSubgradientOracle {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (O : Oracle (EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    (∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) ∧ ∀ h x s, O.answer h (0, x) s = (f x, g x)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := ℝ × EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.D ∧ 0 < p.ε
  admissible p f O :=
    ConvexOn ℝ Set.univ f ∧
    (∀ x y, |f x - f y| ≤ p.L * ‖x - y‖) ∧
    (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖p.x0 - xstar‖ ≤ p.D) ∧
    (∀ x, ∃ z, IsMinOn f Set.univ z ∧ p.μ * ‖x - z‖ ≤ f x - f z) ∧
    IsSubgradientOracle f O
  successful p f output P :=
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
      (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.SharpLipschitzConvex
