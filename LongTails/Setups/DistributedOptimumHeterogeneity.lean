import LongTails.Setups.DistributedWeakInterpolation

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedOptimumHeterogeneity

structure Params extends DistributedWeakInterpolation.Params where
  ζ : ℝ

abbrev Point (p : Params) := DistributedWeakInterpolation.Point p.toParams
abbrev Functions (p : Params) := DistributedWeakInterpolation.Functions p.toParams
abbrev Samples (p : Params) := DistributedWeakInterpolation.Samples p.toParams

noncomputable def objective (p : Params) := DistributedWeakInterpolation.objective p.toParams

def solutions (p : Params) (f : Functions p) : Set (Point p) :=
  {z | IsMinOn (objective p f) Set.univ z}

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
  valid p := DistributedWeakInterpolation.spec.valid p.toParams ∧ 0 ≤ p.ζ
  admissible p f O :=
    (∀ i, ConvexOn ℝ Set.univ (f i) ∧ (∀ x, HasGradientAt (f i) (gradient (f i) x) x) ∧
      ∀ x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖) ∧
    (∃ z ∈ solutions p f, ‖p.x0 - z‖ ≤ p.R ∧
      (∑ i, ‖gradient (f i) z‖ ^ 2) ≤ p.n * p.ζ ^ 2 ∧
      ∀ x, p.μ / 2 * Metric.infDist x (solutions p f) ^ 2 ≤ objective p f x - objective p f z) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (ν : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)), O = DistributedWeakInterpolation.system p.toParams g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
        (ν i : Measure _) (P : Measure _) ∧
        StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ
  successful p f output P := Measurable output ∧
    Integrable (fun s => Metric.infDist (output s) (solutions p f) ^ 2) (P : Measure _) ∧
    ∫ s, Metric.infDist (output s) (solutions p f) ^ 2 ∂(P : Measure _) ≤ p.ε ^ 2

end LongTails.Setups.DistributedOptimumHeterogeneity
