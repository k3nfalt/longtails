import LongTails.Setups.DistributedSmoothNonconvex
import Mathlib.Analysis.Calculus.FDeriv.Basic

open MeasureTheory

namespace LongTails.Setups.DistributedHessianLipschitzNonconvex

open DistributedTemplate

structure Params extends DistributedSmoothNonconvex.Params where
  Q : ℝ

abbrev Point (p : Params) := DistributedSmoothNonconvex.Point p.toParams

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance p := Point p → ℝ
  ComputeQuery p := DistributedSmoothNonconvex.ComputeQuery p.toParams
  ComputeReply p := DistributedSmoothNonconvex.ComputeReply p.toParams
  CommReply p := DistributedSmoothNonconvex.CommReply p.toParams
  Output p := Point p
  publicInput := id
  valid p := DistributedSmoothNonconvex.spec.valid p.toParams ∧ 0 ≤ p.Q
  admissible p f O :=
    DistributedSmoothNonconvex.spec.admissible p.toParams f O ∧
    Differentiable ℝ (gradient f) ∧
    ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
    ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedHessianLipschitzNonconvex
