import LongTails.Template
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace LongTails.Setups.HighDimensionalWeakMintySecondOrder

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  x0 : EuclideanSpace ℝ (Fin d)
  L₁ : ℝ
  L₂ : ℝ
  ρ : ℝ
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)
  Query p := EuclideanSpace ℝ (Fin p.d) ⊕ EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d) ×
    (EuclideanSpace ℝ (Fin p.d) →L[ℝ] EuclideanSpace ℝ (Fin p.d))
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid q := 0 < q.L₁ ∧ 0 < q.L₂ ∧ 0 ≤ q.ρ ∧ q.ρ * q.L₁ ≤ 1 ∧ 0 < q.R ∧ 0 < q.ε ∧
    2 ^ 15 ≤ min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2) ∧
    min (q.L₂ * q.R ^ 2 / q.ε) (q.L₁ ^ 2 * q.R ^ 2 / q.ε ^ 2) ^ 3 ≤ q.d
  admissible q F oracle :=
    ∃ J : EuclideanSpace ℝ (Fin q.d) → EuclideanSpace ℝ (Fin q.d) →L[ℝ] EuclideanSpace ℝ (Fin q.d),
      (∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0)) ∧
      (∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x)) ∧
      (∀ x, HasFDerivAt F (J x) x) ∧
      (∀ x y, ‖J x - J y‖ ≤ q.L₂ * ‖x - y‖) ∧
      (∀ x y, ‖F x - F y‖ ≤ q.L₁ * ‖x - y‖) ∧
      (∃ xstar, F xstar = 0 ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
        ∀ x, -(q.ρ / 2) * ‖F x‖ ^ 2 ≤ ⟪F x, x - xstar⟫)
  successful q F output P :=
    Integrable (fun ω => ‖F (output ω)‖) (P : Measure _) ∧
      (∫ ω, ‖F (output ω)‖ ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.HighDimensionalWeakMintySecondOrder
