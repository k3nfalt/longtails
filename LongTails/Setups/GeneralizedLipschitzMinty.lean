import LongTails.Setups.MirrorGeneralizedSmooth
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace LongTails.Setups.GeneralizedLipschitzMinty

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

structure Params where
  d : ℕ
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)
  Query p := EuclideanSpace ℝ (Fin p.d)
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output p := EuclideanSpace ℝ (Fin p.d)
  publicInput p := p
  valid p := 0 < p.L0 ∧ 0 ≤ p.L1 ∧ 0 ≤ p.R ∧ 0 < p.ε
  admissible p F O :=
    (∀ h s x, O.answer h (0, x) s = F x) ∧ Continuous F ∧ MirrorGeneralizedSmooth.SegmentSmooth F p.L0 p.L1 ∧
      ∃ z, F z = 0 ∧ ‖p.x0 - z‖ ≤ p.R ∧ ∀ x, 0 ≤ ⟪F x, x - z⟫
  successful p F X P :=
    Integrable (fun ω => ‖F (X ω)‖) (P : Measure _) ∧
      (∫ ω, ‖F (X ω)‖ ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GeneralizedLipschitzMinty
