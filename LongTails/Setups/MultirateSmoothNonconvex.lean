import LongTails.Setups.DistributedAggregateSmoothNonconvex

open MeasureTheory

namespace LongTails.Setups.MultirateSmoothNonconvex

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
  L : Fin n → ℝ
  Δ : ℝ
  σ : Fin n → ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

noncomputable abbrev aggregate (p : Params) : DistributedAggregateSmoothNonconvex.Params :=
  ⟨p.d, p.n, p.Ω, p.h, p.l, p.b, (∑ i, p.L i) / p.n, p.Δ, p.σ, p.ε, p.x0⟩

abbrev Point (p : Params) := DistributedAggregateSmoothNonconvex.Point (aggregate p)
abbrev Functions (p : Params) := DistributedAggregateSmoothNonconvex.Functions (aggregate p)
abbrev Samples (p : Params) := DistributedAggregateSmoothNonconvex.Samples (aggregate p)

noncomputable def objective (p : Params) := DistributedAggregateSmoothNonconvex.objective (aggregate p)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery p := DistributedAggregateSmoothNonconvex.ComputeQuery (aggregate p)
  ComputeReply p := DistributedAggregateSmoothNonconvex.ComputeReply (aggregate p)
  CommReply p := DistributedAggregateSmoothNonconvex.CommReply (aggregate p)
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ (∀ i, 0 ≤ p.L i) ∧ 0 ≤ p.Δ ∧ (∀ i, 0 ≤ p.σ i) ∧ 0 < p.ε
  admissible p f O :=
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖) ∧
    (∃ a : ℝ, (∀ x, a ≤ objective p f x) ∧ objective p f p.x0 - a ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)),
      O = DistributedAggregateSmoothNonconvex.system (aggregate p) g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure p.Ω) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (objective p f) (output ω)‖ ^ 2) (P : Measure _) ∧
    ∫ ω, ‖gradient (objective p f) (output ω)‖ ^ 2 ∂(P : Measure _) ≤ p.ε ^ 2

end LongTails.Setups.MultirateSmoothNonconvex
