import LongTails.Setups.DistributedSmoothNonconvex
import Mathlib.Topology.MetricSpace.HausdorffDistance

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedWeakInterpolation

structure Params where
  d : ℕ
  n : ℕ+
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  h : Fin n → Time
  l : Time
  b : Time
  L : Fin n → ℝ
  μ : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Functions (p : Params) := Fin p.n → Point p → ℝ
abbrev Samples (p : Params) := Fin p.n → ℕ → p.Ω

def solutions (p : Params) (f : Functions p) : Set (Point p) :=
  {x | ∀ i, IsMinOn (f i) Set.univ x}

noncomputable def objective (p : Params) (f : Functions p) (x : Point p) : ℝ :=
  (∑ i, f i x) / p.n

noncomputable def system (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :=
  StarNetwork.system ⟨p.h, p.l, p.b⟩ (fun i x (s : Samples p) k => g i x (s i k)) P

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
    p.n * p.μ ≤ ∑ i, p.L i ∧ 0 ≤ p.R ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ i, ConvexOn ℝ Set.univ (f i) ∧ (∀ x, HasGradientAt (f i) (gradient (f i) x) x) ∧
      ∀ x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x - y‖) ∧
    (∃ z ∈ solutions p f, ‖p.x0 - z‖ ≤ p.R ∧ ∀ x,
      p.μ / 2 * Metric.infDist x (solutions p f) ^ 2 ≤ objective p f x - objective p f z) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (ν : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)), O = system p g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
        (ν i : Measure _) (P : Measure _) ∧
        StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ
  successful p f output P := Measurable output ∧
    Integrable (fun s => Metric.infDist (output s) (solutions p f) ^ 2) (P : Measure _) ∧
    ∫ s, Metric.infDist (output s) (solutions p f) ^ 2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedWeakInterpolation
