import LongTails.Setups.DistributedAggregateSmoothNonconvex
import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedContaminatedSmoothNonconvex

open StochasticSmoothAndConvex (IsStochasticGradient)
open StochasticGeneralizedSmoothAndConvex (IID)

structure Params extends DistributedAggregateSmoothNonconvex.Params where
  η : Fin n → ℝ
  failure : ℝ

abbrev Point (p : Params) := DistributedAggregateSmoothNonconvex.Point p.toParams
abbrev Functions (p : Params) := DistributedAggregateSmoothNonconvex.Functions p.toParams
abbrev Samples (p : Params) := DistributedAggregateSmoothNonconvex.Samples p.toParams
noncomputable abbrev objective (p : Params) := DistributedAggregateSmoothNonconvex.objective p.toParams

noncomputable abbrev network (p : Params) : DistributedSmoothNonconvex.Params :=
  { d := p.d, n := p.n, Ω := p.Ω, h := p.h, l := p.l, b := p.b, L := p.L,
    Δ := p.Δ, ε := p.ε, σ := ⨆ i, p.σ i, x0 := p.x0 }

noncomputable def mixture {Ω : Type*} [MeasurableSpace Ω] (η : ℝ)
    (μ ν : Measure Ω) : Measure Ω :=
  ENNReal.ofReal (1 - η) • μ + ENNReal.ofReal η • ν

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n
  Instance := Functions
  ComputeQuery p := BandwidthHeterogeneousSmoothNonconvex.ComputeQuery (network p)
  ComputeReply p := BandwidthHeterogeneousSmoothNonconvex.ComputeReply (network p)
  CommReply p := BandwidthHeterogeneousSmoothNonconvex.CommReply (network p)
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε ∧
    (∀ i, 0 ≤ p.σ i ∧ 0 ≤ p.η i ∧ p.η i ≤ 1 / 16) ∧ 0 < p.failure ∧ p.failure < 1 ∧
    2 ^ 18 * (∑ i, p.σ i * Real.sqrt (p.η i)) ≤ (p.n : ℝ) * p.ε
  admissible p f O :=
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ objective p f x) ∧ objective p f p.x0 - lower ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p)
      (μ ν : Fin p.n → ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (Samples p)),
      O = BandwidthHeterogeneousSmoothNonconvex.system (network p) g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (mixture (p.η i) (μ i) (ν i)) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)
  successful p f X P :=
    Measurable X ∧ (P : Measure _) {s | p.ε < ‖gradient (objective p f) (X s)‖} ≤
      ENNReal.ofReal p.failure

end LongTails.Setups.DistributedContaminatedSmoothNonconvex
