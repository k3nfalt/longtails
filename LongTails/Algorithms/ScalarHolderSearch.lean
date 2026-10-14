import LongTails.Setups.ScalarHolderStochastic
import LongTails.Algorithms.ScalarSearchPlans
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Classical

namespace OracleTemplate.ScalarHolderSearch

open LongTails.Setups.ScalarHolderStochastic

noncomputable def scale (q : Params) (j : ℕ) : ℝ := q.ε / 4 * (2 : ℝ) ^ j

noncomputable def levels (q : Params) : ℕ :=
  ⌈Real.logb 2 (max 1 (4 * q.H ^ (1 / (1 + q.ν)) * q.Δ ^ (q.ν / (1 + q.ν)) / q.ε))⌉₊

noncomputable def distance (q : Params) : ℝ := 32 * q.Δ / q.ε

noncomputable def depth (q : Params) : ℕ :=
  max 1 ⌈Real.logb 2 (max 1 (distance q * (8 * q.H / q.ε) ^ (1 / q.ν)))⌉₊

def probes (j : ℕ) : ℕ := 1024 * 2 ^ j

noncomputable def probeCalls (q : Params) (j : ℕ) : ℕ :=
  ScalarHeavyTailEstimator.calls q.σ q.p (scale q j / 12)
    (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j)

noncomputable def inspect (q : Params) (j : ℕ) (near : Bool) (point value : ℝ) :
    Option (Bool × ℝ) :=
  if near then
    if -q.ε / 2 ≤ value then some (decide (|value| ≤ q.ε / 2), point) else none
  else if scale q j / 2 ≤ value then some (false, point) else none

noncomputable def probePlan (q : Params) (s : ℝ) (j : ℕ) (near : Bool)
    (samples : ℕ → ℝ) : (n offset : ℕ) → Option (Bool × ℝ) →
      QueryPlan ℝ ℝ (Option (Bool × ℝ)) (probeCalls q j * n)
  | 0, _, result => .done result
  | n + 1, offset, result =>
      let point := distance q * samples offset
      QueryPlan.bind (ScalarSearchPlans.estimatePlan q.σ q.p (scale q j / 12)
        (ScalarHeavyTailEstimator.repetitions q.σ (q.ε / 48) j) (q.x0 + s * point))
        (fun value => probePlan q s j near samples n (offset + 1)
          (if result.isSome then result else inspect q j near point (s * value)))

noncomputable def levelCalls (q : Params) : ℕ → ℕ
  | 0 => 0
  | j + 1 => levelCalls q j + probeCalls q j * probes j

noncomputable def levelsPlan (q : Params) (s : ℝ) (samples : ℕ → ℝ) :
    (n offset : ℕ) → Option (Bool × ℝ) → QueryPlan ℝ ℝ (Option (Bool × ℝ)) (levelCalls q n)
  | 0, _, result => .done result
  | j + 1, offset, result =>
      QueryPlan.bind (probePlan q s j false samples (probes j) offset result)
        (fun result => levelsPlan q s samples j (offset + probes j) result)

noncomputable def discoveryCalls (q : Params) : ℕ :=
  levelCalls q (levels q + 1) + probeCalls q 0 * 1024

noncomputable def discoveryPlan (q : Params) (s : ℝ) (samples : ℕ → ℝ) :
    QueryPlan ℝ ℝ (Option (Bool × ℝ)) (discoveryCalls q) :=
  QueryPlan.bind (probePlan q s 0 true samples 1024 0 none)
    (fun result => levelsPlan q s samples (levels q + 1) 1024 result)

noncomputable def attemptCalls (q : Params) : ℕ :=
  ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6 +
    3 * ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 96) 6 * (16 * depth q)

noncomputable def attemptsPlan (q : Params) (s hi : ℝ) (times : ℕ → ℕ) :
    (n offset : ℕ) → Option ℝ → QueryPlan ℝ ℝ (Option ℝ) (attemptCalls q * n)
  | 0, _, result => .done result
  | n + 1, offset, result =>
      QueryPlan.bind (ScalarSearchPlans.rootAttemptPlan q.σ q.p q.ε q.x0 s hi (depth q) (times offset))
        (fun pair => attemptsPlan q s hi times n (offset + 1)
          (if result.isSome then result else if |pair.2| ≤ 3 * q.ε / 4 then some pair.1 else none))

noncomputable def executionCalls (q : Params) : ℕ :=
  (attemptCalls q * 32 + discoveryCalls q) + ScalarHeavyTailEstimator.calls q.σ q.p (q.ε / 48) 6

noncomputable def plan (q : Params) (samples : ℕ → ℝ) (times : ℕ → ℕ) :
    QueryPlan ℝ ℝ ℝ (executionCalls q) :=
  QueryPlan.bind (ScalarSearchPlans.estimatePlan q.σ q.p (q.ε / 48) 6 q.x0)
    (fun first =>
      let s : ℝ := if first ≤ 0 then 1 else -1
      QueryPlan.bind (discoveryPlan q s samples) (fun discovered =>
        let hi := match discovered with | some (false, x) => x | _ => distance q
        QueryPlan.map (fun result =>
          if |first| ≤ q.ε / 2 then q.x0 else
            match discovered with
            | some (true, x) => q.x0 + s * x
            | _ => result.getD q.x0)
          (attemptsPlan q s hi times 32 0 none)))

noncomputable def unitLaw : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc (0 : ℝ) 1), ⟨by simp⟩⟩

instance depth_neZero (q : Params) : NeZero (16 * depth q) := by
  constructor
  unfold depth
  omega

noncomputable def seedLaw (q : Params) : ProbabilityMeasure ((ℕ → ℝ) × (ℕ → Fin (16 * depth q))) :=
  ⟨(Measure.infinitePi fun _ : ℕ => (unitLaw : Measure ℝ)).prod
    (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin (16 * depth q))).toMeasure),
    inferInstance⟩

noncomputable def algorithm (q : Params) : Algorithm ℝ ℝ ℝ :=
  QueryPlan.algorithm (seedLaw q) q.x0 q.x0 (executionCalls q)
    (fun seed => plan q seed.1 (fun i => (seed.2 i).val))

end OracleTemplate.ScalarHolderSearch
