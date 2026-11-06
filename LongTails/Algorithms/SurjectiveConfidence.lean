import LongTails.Setups.ConfidentStochasticSurjectiveInequalities
import LongTails.Algorithms.SurjectiveProxLinear
import LongTails.Algorithms.SampledQueryPlan
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Algorithms.AdaptiveEntropic
import Mathlib.Analysis.InnerProductSpace.ProdL2

open MeasureTheory

namespace LongTails.Algorithms.SurjectiveConfidence

open OracleTemplate
open LongTails.Setups.StochasticSurjectiveInequalities (Primitive Constraint Jacobian)
open LongTails.Setups.ConfidentStochasticSurjectiveInequalities (Params)

noncomputable def replicas (p : Params) : ℕ := ⌈2 * Real.log (2 / p.δ)⌉₊ + 1
noncomputable def groups (p : Params) : ℕ := ⌈8 * Real.log (2 / p.δ)⌉₊ + 1
noncomputable def batch (p : Params) : ℕ := ⌈2 ^ 40 * p.problem.m ^ 4 * p.problem.H ^ 18 * p.problem.σ ^ 2 / p.problem.ε ^ 2⌉₊ + 1
noncomputable def trainingCalls (p : Params) : ℕ :=
  SurjectiveProxLinear.initialBatch p.problem + SurjectiveProxLinear.iterations p.problem +
    SurjectiveProxLinear.certificateBatch p.problem
noncomputable def trialCalls (p : Params) : ℕ := batch p * groups p + trainingCalls p

abbrev Joint (p : Params) := WithLp 2
  (p.problem.E × WithLp 2 (Constraint p.problem × Jacobian p.problem))

noncomputable def lift (p : Params) (v : Primitive p.problem) : Joint p :=
  WithLp.toLp 2 (v.1, WithLp.toLp 2 v.2)

noncomputable def unlift (p : Params) (v : Joint p) : Primitive p.problem :=
  ((WithLp.ofLp v).1, WithLp.ofLp (WithLp.ofLp v).2)

noncomputable def robustEstimate (p : Params) (samples : List (List (Primitive p.problem))) :
    Primitive p.problem :=
  unlift p (RobustGradient.pilotCenter (SurjectiveProxLinear.certificateError p.problem / 2)
    (fun i : Fin (groups p) => (1 / (batch p : ℝ)) •
      ∑ j : Fin (batch p), lift p ((samples.getD i.val []).getD j.val 0)))

noncomputable def trainingPlan (p : Params) : (n : ℕ) → SurjectiveProxLinear.State p.problem →
    QueryPlan (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      p.problem.E n
  | 0, s => .done s.x
  | n + 1, s => .ask (SurjectiveProxLinear.query p.problem s)
      (fun r => trainingPlan p n (SurjectiveProxLinear.update p.problem s r))

noncomputable def samplePlan (p : Params) (x : p.problem.E) : (n : ℕ) →
    QueryPlan (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      (List (Primitive p.problem)) n
  | 0 => .done []
  | n + 1 => .ask (x, x) (fun r => QueryPlan.map (r.1 :: ·) (samplePlan p x n))

noncomputable def certificatePlan (p : Params) (x : p.problem.E) :
    QueryPlan (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      (Primitive p.problem) (batch p * groups p) :=
  QueryPlan.map (robustEstimate p) (QueryPlan.traverse (groups p) (fun _ => samplePlan p x (batch p)))

noncomputable def trialPlan (p : Params) (t : Fin (SurjectiveProxLinear.iterations p.problem + 1)) :
    QueryPlan (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      (p.problem.E × Primitive p.problem) (trialCalls p) :=
  QueryPlan.bind (trainingPlan p (trainingCalls p) ⟨t.val, 0, p.problem.x0, 0, 0⟩)
    (fun x => QueryPlan.map (fun v => (x, v)) (certificatePlan p x))

noncomputable def selectedIndex (p : Params)
    (entries : Fin (replicas p) → p.problem.E × Primitive p.problem) : Fin (replicas p) :=
  AdaptiveHeavyTailSimplex.minimumIndex (by unfold replicas; omega)
    (fun i => ‖SurjectiveProxLinear.modelStep p.problem (entries i).2‖)

noncomputable def selectFunction (p : Params)
    (entries : Fin (replicas p) → p.problem.E × Primitive p.problem) :
    p.problem.E × Constraint p.problem :=
  ((entries (selectedIndex p entries)).1,
    SurjectiveProxLinear.dualPoint p.problem (entries (selectedIndex p entries)).2)

noncomputable def select (p : Params) (candidates : List (p.problem.E × Primitive p.problem)) :
    p.problem.E × Constraint p.problem :=
  selectFunction p (fun i => candidates.getD i.val (p.problem.x0, 0))

noncomputable def plan (p : Params)
    (targets : Fin (replicas p) → Fin (SurjectiveProxLinear.iterations p.problem + 1)) :
    QueryPlan (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      (p.problem.E × Constraint p.problem) (trialCalls p * replicas p) :=
  QueryPlan.map (select p) (QueryPlan.traverse (replicas p) (fun i => trialPlan p (targets i)))

noncomputable def seedLaw (p : Params) :
    ProbabilityMeasure (Fin (replicas p) → Fin (SurjectiveProxLinear.iterations p.problem + 1)) :=
  ⟨Measure.pi fun _ : Fin (replicas p) =>
    ((PMF.uniformOfFintype (Fin (SurjectiveProxLinear.iterations p.problem + 1))).toMeasure), inferInstance⟩

noncomputable def algorithm (p : Params) :
    Algorithm (p.problem.E × p.problem.E) (Primitive p.problem × Primitive p.problem)
      (p.problem.E × Constraint p.problem) :=
  QueryPlan.algorithm (seedLaw p) (p.problem.x0, p.problem.x0) (p.problem.x0, 0)
    (trialCalls p * replicas p) (plan p)

end LongTails.Algorithms.SurjectiveConfidence
