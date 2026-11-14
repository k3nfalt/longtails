import LongTails.Algorithms.StochasticMfcqDirection
import LongTails.Algorithms.StochasticEnvelopeProgram

namespace LongTails.Algorithms.StochasticMfcq

open OracleTemplate
open LongTails.Setups.StochasticMfcqInequalities
open StochasticMfcqDirection StochasticEnvelopeProgram

abbrev State (p : Params) :=
  p.E × p.E × (Fin (replicas p) → JointSpace p) × Bool × Constraint p

noncomputable def initial (p : Params) : State p := (p.x0, p.x0, 0, false, 0)

noncomputable def nextState (p : Params) (s : State p)
    (estimates : Fin (replicas p) → JointSpace p) : State p :=
  let v := robustEstimate p estimates
  if s.2.2.2.1 then (s.1, s.1, estimates, true, s.2.2.2.2)
  else if ‖residual p v‖ ≤ 4 * precision p then
    (s.1, s.1, estimates, true, multipliers p v)
  else (s.1 + stepSize p • direction p v, s.1, estimates, false, 0)

noncomputable def batchSize (p : Params) (k : ℕ) : ℕ :=
  if k % epochLength p = 0 then resetBatch p else incrementBatch p

noncomputable def sampleValue (p : Params) (k : ℕ) (v : Primitive p × Primitive p) :
    JointSpace p :=
  if k % epochLength p = 0 then jointEquiv p v.1 else jointEquiv p (v.1 - v.2)

noncomputable def batchPlan (p : Params) (k : ℕ) (s : State p) (i : Fin (replicas p)) :
    QueryPlan (p.E × p.E) (Primitive p × Primitive p) (JointSpace p) (batchSize p k) :=
  castPlan (Nat.one_mul _) ((collectPlans (batchSize p k) (fun _ =>
    .ask (s.1, s.2.1) fun v => .done (sampleValue p k v))).map fun values =>
      (batchSize p k : ℝ)⁻¹ • ∑ j, values j +
        if k % epochLength p = 0 then 0 else s.2.2.1 i)

noncomputable def stepPlan (p : Params) (k : ℕ) (s : State p) :
    QueryPlan (p.E × p.E) (Primitive p × Primitive p) (State p)
      (batchSize p k * replicas p) :=
  (collectPlans (replicas p) (batchPlan p k s)).map (nextState p s)

noncomputable def calls (p : Params) : ℕ :=
  slotCalls (fun k => batchSize p k * replicas p) (outerSteps p) 0

noncomputable def program (p : Params) :
    QueryPlan (p.E × p.E) (Primitive p × Primitive p) (p.E × Constraint p) (calls p) :=
  (slotPlan (fun k => batchSize p k * replicas p) (stepPlan p)
    (outerSteps p) 0 (initial p)).map (fun s => (s.1, s.2.2.2.2))

noncomputable def algorithm (p : Params) :
    Algorithm (p.E × p.E) (Primitive p × Primitive p) (p.E × Constraint p) :=
  StochasticEnvelopeProgram.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (p.x0, p.x0) (p.x0, 0) (fun _ => ⟨calls p, program p⟩)

noncomputable def output (p : Params)
    (O : Oracle (p.E × p.E) (Primitive p × Primitive p)) (K : ℕ)
    (seed : Unit) (ξ : (k : ℕ) → O.Seed k) : p.E × Constraint p :=
  execute O (algorithm p) (fun _ => K) seed ξ

end LongTails.Algorithms.StochasticMfcq
