import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.Svrg
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Nat.Log

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

noncomputable def theta (p : Params) : ℝ :=
  1 / (256 * (Real.sqrt (p.L / p.μ) + p.γ * p.n +
    (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ)))

noncomputable def epochs (p : Params) : ℕ :=
  ⌈1280 * (Real.sqrt (p.L / p.μ) + p.γ * p.n +
    (p.n * p.δ / (Real.sqrt p.γ * p.μ)) ^ (2 / 3 : ℝ)) *
      Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) / (p.γ * p.n)⌉₊

noncomputable def innerRun (p : Params) (g : Fin p.n × p.E → p.E) (w : p.E)
    (k : ℕ) (s : p.E × p.E) (samples : Fin k → ℝ × Fin p.n) : p.E × p.E :=
  iterateSamples (sampleUpdate p.γ (theta p) p.μ g w) k s samples

noncomputable def epochRun (p : Params) (g : Fin p.n × p.E → p.E)
    (s : p.E × p.E) (samples : Fin p.n → ℝ × Fin p.n) : p.E × p.E :=
  innerRun p g s.1 p.n s samples

noncomputable def run (p : Params) (g : Fin p.n × p.E → p.E)
    (S : ℕ) (s : p.E × p.E) (samples : Fin S → Fin p.n → ℝ × Fin p.n) : p.E × p.E :=
  iterateSamples (epochRun p g) S s samples

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
    (samples : Fin p.n → ℝ × Fin p.n) :
    QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) (p.n + p.n) :=
  QueryPlan.bind (cachePlan p s.1 p.n id)
    (fun cache => innerPlan p cache p.n s samples)

noncomputable def allPlan (p : Params) : (S : ℕ) → (p.E × p.E) →
    (Fin S → Fin p.n → ℝ × Fin p.n) →
      QueryPlan (Fin p.n × p.E) p.E (p.E × p.E) ((p.n + p.n) * S)
  | 0, s, _ => .done s
  | S + 1, s, samples => QueryPlan.bind (epochPlan p s (samples 0))
      (fun next => allPlan p S next (fun i => samples i.succ))

noncomputable def accelerated (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  QueryPlan.algorithm (samplesLaw p.n p.n (epochs p)) (0, p.x0) p.x0
    ((p.n + p.n) * epochs p)
    (fun samples => QueryPlan.map Prod.fst (allPlan p (epochs p) (p.x0, p.x0) samples))

end OracleTemplate.ContinuizedSimilarQuasar.Movement
