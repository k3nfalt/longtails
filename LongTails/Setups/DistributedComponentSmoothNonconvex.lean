import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

namespace LongTails.Setups.DistributedComponentSmoothNonconvex

open MeasureTheory DistributedTemplate
open StochasticSmoothAndConvex (IsStochasticGradient)
open StochasticGeneralizedSmoothAndConvex (IID)

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

noncomputable def smoothness (p : Params) : ℝ := (∑ i, p.L i) / p.n

noncomputable abbrev network (p : Params) : BandwidthHeterogeneousSmoothNonconvex.Params where
  d := p.d
  n := p.n
  Ω := p.Ω
  h := p.h
  l := p.l
  b := p.b
  L := smoothness p
  Δ := p.Δ
  σ := 0
  ε := p.ε
  x0 := p.x0

abbrev Point (p : Params) := BandwidthHeterogeneousSmoothNonconvex.Point (network p)
abbrev Functions (p : Params) := BandwidthHeterogeneousSmoothNonconvex.Functions (network p)
abbrev Samples (p : Params) := BandwidthHeterogeneousSmoothNonconvex.Samples (network p)

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
  valid p := (∀ i, 0 < p.h i) ∧ (∀ i, 0 ≤ p.L i) ∧ 0 ≤ p.Δ ∧ (∀ i, 0 ≤ p.σ i) ∧ 0 < p.ε
  admissible p f O :=
    let F := BandwidthHeterogeneousSmoothNonconvex.objective (network p) f
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ F x) ∧ F p.x0 - lower ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)),
      O = BandwidthHeterogeneousSmoothNonconvex.system (network p) g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure p.Ω) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i)
  successful p f output P :=
    let F := BandwidthHeterogeneousSmoothNonconvex.objective (network p) f
    Measurable output ∧ Integrable (fun ω => ‖gradient F (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient F (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.DistributedComponentSmoothNonconvex
