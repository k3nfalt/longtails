import LongTails.Setups.DistributedSmoothNonconvex

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedMeanSquaredSmooth

open StochasticSmoothAndConvex (IsStochasticGradient)
open StochasticGeneralizedSmoothAndConvex (IID)

abbrev Params := DistributedSmoothNonconvex.Params
abbrev Point := DistributedSmoothNonconvex.Point
abbrev Samples := DistributedSmoothNonconvex.Samples

abbrev Query (p : Params) := Point p × Point p
abbrev ComputeQuery (p : Params) := StarNetwork.ComputeQuery (Query p)
abbrev ComputeReply (p : Params) := StarNetwork.ComputeReply (Query p) (Query p)
abbrev CommReply (p : Params) := StarNetwork.CommReply p.n

noncomputable def system (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1) :=
  StarNetwork.system ⟨fun i => 2 * p.h i, p.l, p.b⟩
    (fun i q s k => (g i q.1 (s i k), g i q.2 (s i k))) P

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance p := Point p → ℝ
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∃ a : ℝ, (∀ x, a ≤ f x) ∧ f p.x0 - a ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p)
      (μ : Fin p.n → ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (Samples p)),
      O = system p g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) f (g i) p.σ ∧
        ∀ x y, Integrable (fun ξ => ‖g i x ξ - g i y ξ‖ ^ 2) (μ i : Measure _) ∧
          (∫ ξ, ‖g i x ξ - g i y ξ‖ ^ 2 ∂(μ i : Measure _)) ≤ p.L ^ 2 * ‖x - y‖ ^ 2
  successful p f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.DistributedMeanSquaredSmooth
