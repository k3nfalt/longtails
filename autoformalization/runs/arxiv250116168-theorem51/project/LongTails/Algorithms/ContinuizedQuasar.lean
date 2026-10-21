import LongTails.Setups.ContinuizedSimilarQuasar
import Mathlib.Analysis.SpecialFunctions.Exp
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.Svrg
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Log

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def flowWeight (γ θ t : ℝ) : ℝ :=
  (1 - Real.exp (-(1 + γ) * θ * t)) / (1 + γ)

noncomputable def flow (γ θ t : ℝ) (s : E × E) : E × E :=
  let a := flowWeight γ θ t
  ((1 - a) • s.1 + a • s.2, (γ * a) • s.1 + (1 - γ * a) • s.2)

noncomputable def jump (θ μ : ℝ) (s : E × E) (g : E) : E × E :=
  (s.1 - (θ ^ 2 / μ) • g, s.2 - (θ / μ) • g)

noncomputable def theta (p : Params) : ℝ :=
  1 / (Real.sqrt (p.L / p.μ) + 512 * p.δ ^ 2 / (p.γ ^ 2 * p.μ ^ 2))

noncomputable def epochLength (p : Params) : ℕ :=
  max 1 ⌈8 * Real.sqrt (p.L / p.μ) / p.γ + 4096 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)⌉₊

noncomputable def epochs (p : Params) : ℕ :=
  max 1 (Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊)

noncomputable def sampleUpdate {n : ℕ} (γ θ μ : ℝ) (g : Fin n × E → E)
    (w : E) (s : E × E) (sample : ℝ × Fin n) : E × E :=
  let y := flow γ θ (max 0 sample.1) s
  jump θ μ y (FiniteSum.estimator g w y.1 sample.2)

def iterateSamples {S Ω : Type*} (advance : S → Ω → S) :
    (k : ℕ) → S → (Fin k → Ω) → S
  | 0, s, _ => s
  | k + 1, s, samples => iterateSamples advance k (advance s (samples 0))
      (fun i => samples i.succ)

noncomputable def innerRun (p : Params) (g : Fin p.n × p.E → p.E) (w : p.E)
    (k : ℕ) (s : p.E × p.E) (samples : Fin k → ℝ × Fin p.n) : p.E × p.E :=
  iterateSamples (sampleUpdate p.γ (theta p) p.μ g w) k s samples

noncomputable def epochRun (p : Params) (g : Fin p.n × p.E → p.E)
    (s : p.E × p.E) (samples : Fin (epochLength p) → ℝ × Fin p.n) : p.E × p.E :=
  innerRun p g s.1 (epochLength p) s samples

noncomputable def run (p : Params) (g : Fin p.n × p.E → p.E)
    (S : ℕ) (s : p.E × p.E) (samples : Fin S → Fin (epochLength p) → ℝ × Fin p.n) : p.E × p.E :=
  iterateSamples (epochRun p g) S s samples

noncomputable def sampleLaw (n : ℕ) [NeZero n] : ProbabilityMeasure (ℝ × Fin n) := by
  letI := ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  exact ⟨(ProbabilityTheory.expMeasure 1).prod (PMF.uniformOfFintype (Fin n)).toMeasure,
    inferInstance⟩

noncomputable def samplesLaw (n m S : ℕ) [NeZero n] :
    ProbabilityMeasure (Fin S → Fin m → ℝ × Fin n) :=
  ⟨Measure.pi (fun _ => Measure.pi (fun _ => (sampleLaw n : Measure _))), inferInstance⟩

noncomputable def cachePlan (p : Params) (x : p.E) :
    (m : ℕ) → (Fin m → Fin p.n) →
      QueryPlan (Fin p.n × p.E) p.E (Fin m → p.E) m
  | 0, _ => .done Fin.elim0
  | m + 1, ids => .ask (ids 0, x) (fun v =>
      QueryPlan.map (Fin.cons v) (cachePlan p x m (fun i => ids i.succ)))

noncomputable def step (p : Params) (cache : Fin p.n → p.E)
    (s : p.E × p.E) (sample : ℝ × Fin p.n) (reply : p.E) : p.E × p.E :=
  jump (theta p) p.μ (flow p.γ (theta p) (max 0 sample.1) s)
    (reply - cache sample.2 + (p.n : ℝ)⁻¹ • ∑ i, cache i)

noncomputable def stepPlan (p : Params) (cache : Fin p.n → p.E)
    (s : p.E × p.E) (sample : ℝ × Fin p.n) :
    QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) 1 :=
  .ask (sample.2, (flow p.γ (theta p) (max 0 sample.1) s).1)
    (fun reply => .done (step p cache s sample reply))

noncomputable def innerPlan (p : Params) (cache : Fin p.n → p.E) :
    (k : ℕ) → (p.E × p.E) → (Fin k → ℝ × Fin p.n) →
      QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) k
  | 0, s, _ => .done s
  | k + 1, s, samples => QueryPlan.bind (stepPlan p cache s (samples 0))
      (fun next => innerPlan p cache k next (fun i => samples i.succ))

noncomputable def epochPlan (p : Params) (s : p.E × p.E)
    (samples : Fin (epochLength p) → ℝ × Fin p.n) :
    QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) (epochLength p + p.n) :=
  QueryPlan.bind (cachePlan p s.1 p.n id)
    (fun cache => innerPlan p cache (epochLength p) s samples)

noncomputable def allPlan (p : Params) : (S : ℕ) → (p.E × p.E) →
    (Fin S → Fin (epochLength p) → ℝ × Fin p.n) →
      QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) ((epochLength p + p.n) * S)
  | 0, s, _ => .done s
  | S + 1, s, samples => QueryPlan.bind (epochPlan p s (samples 0))
      (fun next => allPlan p S next (fun i => samples i.succ))

noncomputable def accelerated (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  QueryPlan.algorithm (samplesLaw p.n (epochLength p) (epochs p)) (0, p.x0) p.x0
    ((epochLength p + p.n) * epochs p)
    (fun samples => QueryPlan.map Prod.fst (allPlan p (epochs p) (p.x0, p.x0) samples))

end OracleTemplate.ContinuizedSimilarQuasar
