import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Setups.GlobalJacobianMonotoneExpected

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  d : ℕ
  x0 : EuclideanSpace ℝ (Fin d)
  L : ℝ
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d) ×
    (EuclideanSpace ℝ (Fin p.d) →L[ℝ] EuclideanSpace ℝ (Fin p.d))
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.R ∧ 0 < p.ε ∧ 4096 * p.ε ≤ p.L * p.R ^ 2 ∧
    4096 * (⌊(p.L * p.R ^ 2 / (4096 * p.ε)) ^ (2 / 5 : ℝ)⌋₊ + 2) ^ 5 ≤ p.d
  admissible p F O :=
    (∀ k x seed, O.answer k (0, x) seed = (F x, fderiv ℝ F x)) ∧
    Differentiable ℝ F ∧
    (∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) ∧
    ∃ xstar, F xstar = 0 ∧ ‖p.x0 - xstar‖ ≤ p.R
  successful p F output P :=
    Integrable (fun ω => ‖F (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖F (output ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GlobalJacobianMonotoneExpected
