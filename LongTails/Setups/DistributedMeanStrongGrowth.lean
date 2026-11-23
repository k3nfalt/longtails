import LongTails.Setups.DistributedWeakInterpolation

open MeasureTheory DistributedTemplate

namespace LongTails.Setups.DistributedMeanStrongGrowth

structure Params where
  d : ℕ
  n : ℕ+
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  h : Fin n → Time
  l : Time
  b : Time
  L : ℝ
  μ : ℝ
  ρ : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Functions (p : Params) := Fin p.n → Point p → ℝ
abbrev Samples (p : Params) := Fin p.n → ℕ → p.Ω

noncomputable def objective (p : Params) (f : Functions p) (x : Point p) := (∑ i, f i x) / p.n

def solutions (p : Params) (f : Functions p) := {x | IsMinOn (objective p f) Set.univ x}

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery p := StarNetwork.ComputeQuery (Point p)
  ComputeReply p := StarNetwork.ComputeReply (Point p) (Point p)
  CommReply p := StarNetwork.CommReply p.n
  Output := Point
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.μ ∧ p.μ ≤ p.L ∧ 1 ≤ p.ρ ∧
    0 ≤ p.R ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ i, ConvexOn ℝ Set.univ (f i) ∧ ∀ x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x-y‖) ∧
    (∀ x, ∑ i, ‖gradient (f i) x‖ ^ 2 ≤ p.n * p.ρ * ‖gradient (objective p f) x‖ ^ 2) ∧
    (∃ z ∈ solutions p f, ‖p.x0-z‖ ≤ p.R ∧ ∀ x,
      p.μ / 2 * Metric.infDist x (solutions p f)^2 ≤ objective p f x - objective p f z) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (ν : Fin p.n → ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)),
      O = StarNetwork.system ⟨p.h,p.l,p.b⟩ (fun i x (s : Samples p) k => g i x (s i k)) P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, StochasticGeneralizedSmoothAndConvex.IID (fun k (s : Samples p) => s i k)
        (ν i : Measure _) (P : Measure _) ∧
        StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ
  successful p f output P := Measurable output ∧
    Integrable (fun s => Metric.infDist (output s) (solutions p f)^2) (P : Measure _) ∧
    ∫ s, Metric.infDist (output s) (solutions p f)^2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.DistributedMeanStrongGrowth
