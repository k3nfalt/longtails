import LongTails.Setups.DistributedSmoothNonconvex
import LongTails.Setups.FiniteSumSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.DistributedAggregateSmoothNonconvex

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
  σ : Fin n → ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Functions (p : Params) := Fin p.n → Point p → ℝ
abbrev Samples (p : Params) := Fin p.n → ℕ → p.Ω

noncomputable def objective (p : Params) (f : Functions p) (x : Point p) : ℝ :=
  FiniteSumSmoothAndConvex.objective f x

abbrev ComputeQuery (p : Params) := StarNetwork.ComputeQuery (Point p)
abbrev ComputeReply (p : Params) := StarNetwork.ComputeReply (Point p) (Point p)
abbrev CommReply (p : Params) := StarNetwork.CommReply p.n

noncomputable def system (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1) :=
  StarNetwork.system ⟨p.h, p.l, p.b⟩ (fun i x samples k => g i x (samples i k)) P

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ (∀ i, 0 ≤ p.σ i) ∧ 0 < p.ε
  admissible p f O :=
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ objective p f x) ∧ objective p f p.x0 - lower ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p)
      (μ : Fin p.n → ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (Samples p)),
      O = system p g P ∧
      ProbabilityTheory.iIndepFun (fun i (ξ : Samples p) => ξ i) (P : Measure _) ∧
      ∀ i, IID (fun k (ξ : Samples p) => ξ i k) (μ i : Measure _) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (objective p f) (output ω)‖) (P : Measure _) ∧
    ∫ ω, ‖gradient (objective p f) (output ω)‖ ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedAggregateSmoothNonconvex
