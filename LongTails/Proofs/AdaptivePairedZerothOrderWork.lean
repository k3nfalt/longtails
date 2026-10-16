import LongTails.Algorithms.AdaptivePairedZerothOrderWork
import LongTails.Proofs.ClippedTwoPointWork
import LongTails.Proofs.AdaptivePairedZerothOrder
import LongTails.Proofs.ClippedTwoPointLayers

namespace LongTails.Proofs.AdaptivePairedZerothOrderWork

open LongTails.Setups.AdaptivePairedZerothOrder
open LongTails.Algorithms.AdaptivePairedZerothOrder
open LongTails.Proofs.ClippedTwoPointWork
open LongTails.Algorithms.ClippedTwoPointWork
open LongTails.Algorithms.AdaptivePairedZerothOrderWork

lemma minimum_value (a b : ℝ) : (minimum a b).value = min a b := by
  by_cases hab : a ≤ b <;> simp [minimum, Bind.bind, Pure.pure, bindWork, pureWork,
    realLe, hab, min_def]

lemma minimum_cost (a b : ℝ) : (minimum a b).cost = ⟨1, 0, 0, 0⟩ := by
  by_cases hab : a ≤ b <;> simp [minimum, Bind.bind, Pure.pure, bindWork, pureWork,
    realLe, hab, Cost.add]

lemma preprocess_cost (p : Public) : (preprocess p).cost = ⟨35, 0, 0, 0⟩ := by
  dsimp only [preprocess, Bind.bind, Pure.pure, bindWork, pureWork, natReal,
    realAdd, realMul, realDiv, realSqrt, natMul, natAdd]
  rw [minimum_cost, minimum_cost]
  rfl

lemma preprocess_value (p : Public) : (preprocess p).value =
    ⟨LongTails.Algorithms.AdaptivePairedZerothOrder.weightTotal p,
      LongTails.Algorithms.AdaptivePairedZerothOrder.scale p,
      LongTails.Algorithms.AdaptivePairedZerothOrder.clipRadius p,
      LongTails.Algorithms.AdaptivePairedZerothOrder.regularization p,
      LongTails.Algorithms.AdaptivePairedZerothOrder.validationClip p,
      smoothRadius p, nonsmoothRadius p, 6 * p.T + 4 * p.N⟩ := by
  dsimp only [preprocess, Bind.bind, Pure.pure, bindWork, pureWork, natReal,
    realAdd, realMul, realDiv, realSqrt, natMul, natAdd]
  rw [minimum_value, minimum_value]
  simp only [LongTails.Algorithms.AdaptivePairedZerothOrder.weightTotal,
    LongTails.Algorithms.AdaptivePairedZerothOrder.scale,
    LongTails.Algorithms.AdaptivePairedZerothOrder.clipRadius,
    LongTails.Algorithms.AdaptivePairedZerothOrder.regularization,
    LongTails.Algorithms.AdaptivePairedZerothOrder.validationClip,
    smoothRadius, nonsmoothRadius, pow_two]

lemma evaluate_cost (p : Public) (seed : ℕ → Point p.d) (reply : ℕ → Point p.d → ℝ)
    (hbatch : (∑ j ∈ Finset.range p.N, batch p j) ≤ p.T + p.N) :
    (evaluate p seed reply).cost.operations ≤ 128 * (p.T + p.N + 1) ∧
      (evaluate p seed reply).cost.projections = 2 * p.N ∧
      (evaluate p seed reply).cost.queries = 6 * p.T + 4 * p.N ∧
      (evaluate p seed reply).cost.directions ≤ 2 * (p.T + p.N) := by
  have hB : ∀ t, (batchCount p.T (weightTotal p) t).value = batch p t := by
    intro t
    exact batch_count_value _ _ _
  let run := dualRun p.d p.T (weightTotal p) (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) p.project
    ⟨((p.x0, p.x0), (p.x0, p.x0)), 0, 0⟩ seed reply p.N
  obtain ⟨ho, hp, hq, hd⟩ := dual_run_cost p.d p.T (weightTotal p) (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) p.project
    ⟨((p.x0, p.x0), (p.x0, p.x0)), 0, 0⟩ seed reply p.N
  simp only [hB] at ho hq hd
  have hc := (dual_run_offsets p.d p.T (weightTotal p) (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) p.project
    ⟨((p.x0, p.x0), (p.x0, p.x0)), 0, 0⟩ seed reply p.N).2
  simp only [hB, Nat.zero_add] at hc
  obtain ⟨so, sp, sq, sd⟩ := selection_cost (validationClip p) run.value.states.1.1
    run.value.states.2.1 reply p.T run.value.call
  dsimp only [evaluate, Bind.bind, bindWork, natMul, natAdd, natSub]
  rw [preprocess_cost]
  simp only [preprocess_value, padding_cost, Cost.add, Nat.zero_add, Nat.add_zero]
  change 35 + (run.cost.operations +
    ((selection (validationClip p) run.value.states.1.1 run.value.states.2.1 reply p.T run.value.call).cost.operations +
      (1 + (1 + (1 + 2 * (6 * p.T + 4 * p.N - (run.value.call + 2 * p.T))))))) ≤ _ ∧
    run.cost.projections +
      (selection (validationClip p) run.value.states.1.1 run.value.states.2.1 reply p.T run.value.call).cost.projections = _ ∧
    run.cost.queries +
      ((selection (validationClip p) run.value.states.1.1 run.value.states.2.1 reply p.T run.value.call).cost.queries +
        (6 * p.T + 4 * p.N - (run.value.call + 2 * p.T))) = _ ∧
    run.cost.directions +
      (selection (validationClip p) run.value.states.1.1 run.value.states.2.1 reply p.T run.value.call).cost.directions ≤ _
  change run.cost.operations ≤ _ at ho
  change run.cost.projections = _ at hp
  change run.cost.queries = _ at hq
  change run.cost.directions = _ at hd
  change run.value.call = _ at hc
  constructor
  · omega
  · constructor
    · omega
    · constructor <;> omega

lemma evaluate_plan_value (p : Public) (seed : ℕ → Direction p)
    (reply : ℕ → Point p.d → ℝ) :
    (evaluate p (fun i => seed i) reply).value =
      OracleTemplate.QueryPlan.sampledEval (fun x k => reply k x) id
        (LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d (clipRadius p) (clipRadius p)
          (smoothRadius p) (nonsmoothRadius p) (regularization p) (validationClip p)
          p.project (p.x0, p.x0) (batch p) (firstDirections p seed) (secondDirections p seed) p.N p.T) 0 := by
  have hB : ∀ t, batch p t = (batchCount p.T (weightTotal p) t).value := by
    intro t
    exact (batch_count_value _ _ _).symm
  have hs := dual_run_value p.d p.T (weightTotal p) (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) p.project (p.x0, p.x0)
    (fun i => (seed i : Point p.d)) reply 0 0 p.N (batch p) hB
  have hc := (dual_run_offsets p.d p.T (weightTotal p) (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) p.project
    ⟨((p.x0, p.x0), (p.x0, p.x0)), 0, 0⟩ (fun i => (seed i : Point p.d)) reply p.N).2
  simp only [← hB, Nat.zero_add] at hc
  simp only [Nat.zero_add] at hs
  dsimp only [evaluate, Bind.bind, bindWork, natMul, natAdd, natSub]
  simp only [preprocess_value, padding_value, selection_value]
  rw [hs, hc]
  rw [LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan,
    OracleTemplate.QueryPlan.sampledEval_bind]
  rw [show 0 + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N =
      4 * (∑ j ∈ Finset.range p.N, batch p j) by
    rw [LongTails.Proofs.ClippedTwoPointExecution.dual_solver_calls_sum, Nat.zero_add]]
  rfl

lemma public_batch_count (p : Public) (hN : 0 < p.N) (hT : 0 < p.T) :
    (∑ j ∈ Finset.range p.N, batch p j) ≤ p.T + p.N := by
  have hc := LongTails.Proofs.AdaptivePairedZerothOrder.actual_value_cost p hN hT
  rw [LongTails.Proofs.ClippedTwoPointExecution.dual_solver_calls_sum] at hc
  omega

lemma evaluate_execute_value {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → ℝ)
    (seed : ℕ → Direction p) (ξ : ℕ → Ω) (hN : 0 < p.N) (hT : 0 < p.T) :
    (evaluate p (fun i => seed i) (fun k x => g x (ξ k))).value =
      OracleTemplate.execute
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w }
        (algorithm p) (fun _ => 6 * p.T + 4 * p.N) seed ξ := by
  have hreply : ∀ {k : ℕ} (plan : OracleTemplate.QueryPlan (Point p.d) ℝ (Point p.d) k) (call : ℕ),
      OracleTemplate.QueryPlan.sampledEval (fun x k => g x (ξ k)) id plan call =
        OracleTemplate.QueryPlan.sampledEval g ξ plan call := by
    intro k plan
    induction plan with
    | done value => intro call; rfl
    | ask q rest ih =>
      intro call
      exact ih (g q (ξ call)) (call + 1)
  rw [evaluate_plan_value, hreply]
  exact (OracleTemplate.QueryPlan.execute_sampledPlan_of_le (directionLaw p) P p.x0 p.x0
    (2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N)
    (6 * p.T + 4 * p.N)
    (fun z => LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d
      (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
      (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
      (firstDirections p z) (secondDirections p z) p.N p.T)
    g seed ξ (LongTails.Proofs.AdaptivePairedZerothOrder.actual_value_cost p hN hT)).symm

lemma execute_padding_query (p : Public) (seed : ℕ → Direction p)
    (reply : ℕ → Point p.d → ℝ) (j : ℕ)
    (hj : 2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N ≤ j) :
    ((algorithm p).query (OracleTemplate.StochasticGradient.advance
      (fun call state => (algorithm p).update state (reply call ((algorithm p).query state).2))
      j 0 ((algorithm p).initial seed))).2 = p.x0 := by
  change OracleTemplate.QueryPlan.query p.x0
    (OracleTemplate.StochasticGradient.advance
      (fun call state => OracleTemplate.QueryPlan.update state
        (reply call (OracleTemplate.QueryPlan.query p.x0 state))) j 0
      ⟨2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N,
        LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d (clipRadius p) (clipRadius p)
          (smoothRadius p) (nonsmoothRadius p) (regularization p) (validationClip p)
          p.project (p.x0, p.x0) (batch p) (firstDirections p seed) (secondDirections p seed) p.N p.T⟩) = p.x0
  have he := OracleTemplate.QueryPlan.advance_sampledPlan_of_le (fun x k => reply k x) id p.x0
    (LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d (clipRadius p) (clipRadius p)
      (smoothRadius p) (nonsmoothRadius p) (regularization p) (validationClip p)
      p.project (p.x0, p.x0) (batch p) (firstDirections p seed) (secondDirections p seed) p.N p.T) hj 0
  exact congrArg (OracleTemplate.QueryPlan.query p.x0) he

lemma public_query_layers (p : Public) (seed : ℕ → Direction p) :
    LongTails.Algorithms.QueryLayers.Layers (paddedExecutionPlan p seed) (p.N + 1) := by
  exact LongTails.Proofs.ClippedTwoPointLayers.adaptive_padded_layers p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
    (firstDirections p seed) (secondDirections p seed) p.N p.T _

lemma public_query_trace (p : Public) (seed : ℕ → Direction p) (reply : ℕ → Point p.d → ℝ)
    (hN : 0 < p.N) (hT : 0 < p.T) :
    LongTails.Algorithms.QueryLayers.queryTrace reply (paddedExecutionPlan p seed) 0 =
      List.ofFn (fun i : Fin (6 * p.T + 4 * p.N) =>
        ((algorithm p).query (OracleTemplate.StochasticGradient.advance
          (fun call state => (algorithm p).update state (reply call ((algorithm p).query state).2))
          i 0 ((algorithm p).initial seed))).2) := by
  let k := 2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N
  let K := 6 * p.T + 4 * p.N
  let plan := LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
    (firstDirections p seed) (secondDirections p seed) p.N p.T
  have hk : k ≤ K := LongTails.Proofs.AdaptivePairedZerothOrder.actual_value_cost p hN hT
  calc
    _ = LongTails.Algorithms.QueryLayers.executionTrace p.x0 reply (K - k + k) 0 ⟨k, plan⟩ :=
      (LongTails.Proofs.QueryLayers.execution_trace_padded p.x0 reply plan (K - k) 0).symm
    _ = LongTails.Algorithms.QueryLayers.executionTrace p.x0 reply K 0 ⟨k, plan⟩ :=
      congrArg (fun n => LongTails.Algorithms.QueryLayers.executionTrace p.x0 reply n 0 ⟨k, plan⟩)
        (Nat.sub_add_cancel hk)
    _ = _ := LongTails.Proofs.QueryLayers.execution_trace_ofFn p.x0 reply K 0 ⟨k, plan⟩

structure ExecutionCertificate (p : Public) : Prop where
  cost : ∀ (seed : ℕ → Point p.d) (reply : ℕ → Point p.d → ℝ),
    (evaluate p seed reply).cost.operations ≤ 128 * (p.T + p.N + 1) ∧
    (evaluate p seed reply).cost.projections = 2 * p.N ∧
    (evaluate p seed reply).cost.queries = 6 * p.T + 4 * p.N ∧
    (evaluate p seed reply).cost.directions ≤ 2 * (p.T + p.N)
  layers : ∀ seed : ℕ → Direction p,
    LongTails.Algorithms.QueryLayers.Layers (paddedExecutionPlan p seed) (p.N + 1)
  trace : ∀ (seed : ℕ → Direction p) (reply : ℕ → Point p.d → ℝ),
    LongTails.Algorithms.QueryLayers.queryTrace reply (paddedExecutionPlan p seed) 0 =
      List.ofFn (fun i : Fin (6 * p.T + 4 * p.N) =>
        ((algorithm p).query (OracleTemplate.StochasticGradient.advance
          (fun call state => (algorithm p).update state (reply call ((algorithm p).query state).2))
          i 0 ((algorithm p).initial seed))).2)
  execution_value : ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → ℝ)
    (seed : ℕ → Direction p) (ξ : ℕ → Ω),
    (evaluate p (fun i => seed i) (fun k x => g x (ξ k))).value =
      OracleTemplate.execute
        { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w }
        (algorithm p) (fun _ => 6 * p.T + 4 * p.N) seed ξ

lemma execution_certificate (p : Public) (hN : 0 < p.N) (hT : 0 < p.T) :
    ExecutionCertificate p := by
  refine ⟨?_, public_query_layers p, ?_, ?_⟩
  · intro seed reply
    exact evaluate_cost p seed reply (public_batch_count p hN hT)
  · intro seed reply
    exact public_query_trace p seed reply hN hT
  · intro Ω inst P g seed ξ
    exact evaluate_execute_value p P g seed ξ hN hT

lemma certified_success (p : LongTails.Setups.AdaptivePairedZerothOrder.Params) (hv : LongTails.Setups.AdaptivePairedZerothOrder.spec.valid p) (I : LongTails.Setups.AdaptivePairedZerothOrder.Instance p.toPublic)
    (O : OracleTemplate.Oracle (Point p.d) ℝ) (hadm : LongTails.Setups.AdaptivePairedZerothOrder.spec.admissible p I O) :
    ExecutionCertificate p.toPublic ∧
    LongTails.Setups.AdaptivePairedZerothOrder.spec.successful p I
      (fun z : (algorithm p.toPublic).Seed × ((k : ℕ) → O.Seed k) =>
        OracleTemplate.execute O (algorithm p.toPublic) (fun _ => 6 * p.T + 4 * p.N) z.1 z.2)
      ⟨((algorithm p.toPublic).law : MeasureTheory.Measure _).prod (O.law : MeasureTheory.Measure _), inferInstance⟩ := by
  exact ⟨execution_certificate p.toPublic hv.2.2.2.2.1 hv.2.2.2.2.2.1,
    LongTails.Proofs.AdaptivePairedZerothOrder.successful_execution p hv I O hadm⟩

end LongTails.Proofs.AdaptivePairedZerothOrderWork
