import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.EuclideanWeakMinty

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  d : ℕ
  L : ℝ
  ρ : ℝ
  x0 : EuclideanSpace ℝ (Fin d)
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.L ∧ 0 ≤ p.ρ ∧ p.ρ ≤ 1 / (20 * p.L) ∧ 0 < p.ε ∧
    28 * p.ε ≤ p.L * p.R ∧ 257 ≤ p.d
  admissible p F oracle :=
    (∀ k seed x, oracle.answer k (0, x) seed = F x) ∧
    (∀ x y, ‖F x - F y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ xstar, F xstar = 0 ∧ ‖xstar - p.x0‖ ≤ p.R ∧
      ∀ x, -p.ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xstar⟫)
  successful p F output P :=
    Integrable (fun ω => ‖F (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖F (output ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.EuclideanWeakMinty
