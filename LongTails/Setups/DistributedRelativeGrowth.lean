import LongTails.Setups.DistributedWeakInterpolation

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedRelativeGrowth

structure Params extends DistributedWeakInterpolation.Params where
  ρ : ℝ

abbrev Point (p : Params) := DistributedWeakInterpolation.Point p.toParams
abbrev Functions (p : Params) := DistributedWeakInterpolation.Functions p.toParams
abbrev Samples (p : Params) := DistributedWeakInterpolation.Samples p.toParams

noncomputable def minimizers (p : Params) (f : Functions p) : Set (Point p) :=
  {z | IsMinOn (DistributedWeakInterpolation.objective p.toParams f) Set.univ z}

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery p := StarNetwork.ComputeQuery (Point p)
  ComputeReply p := StarNetwork.ComputeReply (Point p) (Point p)
  CommReply p := StarNetwork.CommReply p.n
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ (∀ i, 0 ≤ p.L i) ∧ 0 < p.μ ∧
    1 ≤ p.ρ ∧ 0 ≤ p.R ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ i, ConvexOn ℝ Set.univ (f i) ∧ (∀ x, HasGradientAt (f i) (gradient (f i) x) x) ∧
      ∀ x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖) ∧
    (∃ z ∈ minimizers p f, ‖p.x0 - z‖ ≤ p.R ∧ ∀ x,
      p.μ / 2 * Metric.infDist x (minimizers p f) ^ 2 ≤
        DistributedWeakInterpolation.objective p.toParams f x -
        DistributedWeakInterpolation.objective p.toParams f z) ∧
    (∀ x, ∑ i, ‖gradient (f i) x‖ ^ 2 ≤ (p.n : ℝ) * p.ρ *
      ‖gradient (DistributedWeakInterpolation.objective p.toParams f) x‖ ^ 2) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (ν : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)), O = DistributedWeakInterpolation.system p.toParams g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
        (ν i : Measure _) (P : Measure _) ∧
        StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ
  successful p f output P := Measurable output ∧
    Integrable (fun s => Metric.infDist (output s) (minimizers p f) ^ 2) (P : Measure _) ∧
    ∫ s, Metric.infDist (output s) (minimizers p f) ^ 2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedRelativeGrowth
