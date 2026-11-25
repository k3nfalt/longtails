import LongTails.Setups.StochasticEllSmoothNonconvex
import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Algorithms.MultiplicativeRobustEstimator

namespace LongTails.Algorithms.StochasticEllSmoothMedoid

open OracleTemplate MultiplicativeRobustEstimator
open LongTails.Algorithms.HighProbabilityStationarity (stepRepeat samplePlan)

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def blockMeans (K n : ℕ) (v : Fin ((2 * K + 2) * n) → E) : Fin (2 * K + 1 + 1) → E :=
  fun i => (1 / (n : ℝ)) • ∑ l : Fin n, v (finProdFinEquiv (i, l))

def estimate (K n : ℕ) (v : Fin ((2 * K + 2) * n) → E) : E := medoid (blockMeans K n v)

def roundStep (ℓ : ℝ → ℝ) (ε : ℝ) (s : E × Bool) (v : E) : E × Bool :=
  if s.2 then s
  else if ‖v‖ ≤ ε / 2 then (s.1, true)
  else (s.1 - (1 / (2 * ℓ (3 * ‖v‖))) • v, false)

def finish (x0 : E) (s : E × Bool) : E := if s.2 then s.1 else x0

def method (ℓ : ℝ → ℝ) (ε : ℝ) (K n T : ℕ) (x0 : E) :
    QueryPlan E E E ((2 * K + 2) * n * T) :=
  (stepRepeat T (fun s => (samplePlan s.1 ((2 * K + 2) * n)).map
    (fun w => roundStep ℓ ε s (estimate K n w))) (x0, false)).map (finish x0)

end

section Tuning

open LongTails.Setups.StochasticEllSmoothNonconvex

variable (q : Params)

noncomputable def horizon : ℝ := q.Δ * q.ℓ q.ε / q.ε ^ 2

noncomputable def steps : ℕ := ⌊72 * horizon q⌋₊ + 1

noncomputable def blockSize : ℕ := ⌈(2 ^ 16 * q.σ / q.ε) ^ (q.p / (q.p - 1))⌉₊ + 1

noncomputable def halfBlocks : ℕ := ⌈64 * Real.logb 2 (2 + horizon q) / (2 - q.ρ)⌉₊

noncomputable def unitLaw : MeasureTheory.ProbabilityMeasure Unit :=
  ⟨MeasureTheory.Measure.dirac (), inferInstance⟩

noncomputable def algorithm : Algorithm q.E q.E q.E :=
  QueryPlan.algorithm unitLaw q.x0 q.x0 _
    (fun _ => method q.ℓ q.ε (halfBlocks q) (blockSize q) (steps q) q.x0)

end Tuning

end LongTails.Algorithms.StochasticEllSmoothMedoid
