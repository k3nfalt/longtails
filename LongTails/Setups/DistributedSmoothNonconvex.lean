import LongTails.TemplateDistributed
import LongTails.Setups.StarNetwork
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.DistributedSmoothNonconvex

open DistributedTemplate
open LongTails.Setups.StochasticSmoothAndConvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

structure Params where
  d : ℕ
  n : ℕ+
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  h : Fin n → Time
  l : Time
  b : Time
  L : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

abbrev Samples (p : Params) := Fin p.n → ℕ → p.Ω
abbrev ComputeQuery (p : Params) := StarNetwork.ComputeQuery (Point p)
abbrev ComputeReply (p : Params) := StarNetwork.ComputeReply (Point p) (Point p)
abbrev CommReply (p : Params) := StarNetwork.CommReply p.n

noncomputable def system (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1) :=
  StarNetwork.system ⟨p.h, p.l, p.b⟩
    (fun i x samples k => g i x (samples i k)) P

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance p := Point p → ℝ
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output p := Point p
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧
    0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f p.x0 - lower ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p)
      (μ : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)),
      O = system p g P ∧
      ProbabilityTheory.iIndepFun (fun i (ξ : Samples p) => ξ i) (P : Measure _) ∧
      ∀ i, IID (fun k (ξ : Samples p) => ξ i k) (μ i : Measure _) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) f (g i) p.σ
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
    ∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedSmoothNonconvex
