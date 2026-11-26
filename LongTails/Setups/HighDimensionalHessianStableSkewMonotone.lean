import LongTails.Setups.HessianStableSkewMonotone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.HighDimensionalHessianStableSkewMonotone

open OracleTemplate MeasureTheory

structure Params where
  d : ℕ
  x0 : EuclideanSpace ℝ (Fin d)
  M : ℝ
  D : ℝ
  ε : ℝ
  Λ : ℝ

noncomputable def toGeneral (p : Params) : LongTails.Setups.HessianStableSkewMonotone.Params :=
  ⟨⟨EuclideanSpace ℝ (Fin p.d), p.x0, p.M, p.D, p.ε⟩, p.Λ⟩

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d) ⊕
    (EuclideanSpace ℝ (Fin p.d) →L[ℝ] EuclideanSpace ℝ (Fin p.d))
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := LongTails.Setups.HessianStableSkewMonotone.spec.valid (toGeneral p) ∧
    2 ^ 60 ≤ p.M * p.D ∧ p.ε * (p.M * p.D) ^ 2 ≤ p.Λ * p.D ∧
    2 ^ 21 * (p.M * p.D) ^ ((10 : ℝ) / 3) ≤ p.d
  admissible p F O := LongTails.Setups.HessianStableSkewMonotone.spec.admissible (toGeneral p) F O
  successful p F output P :=
    Integrable (fun ω => ‖F (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖F (output ω)‖ ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.HighDimensionalHessianStableSkewMonotone
