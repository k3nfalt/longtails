import LongTails.Algorithms.CappedProximal
import LongTails.Proofs.ComponentEnvelopeExecution

namespace LongTails.Proofs.CappedProximalExecution

open LongTails.Setups.CappedHessianSimilarConvex
open LongTails.Algorithms.CappedProximal
open OracleTemplate.ComponentEnvelope

lemma mem_contacts (p : Params) (indices : Fin p.s → Option (Fin p.m)) (i : Fin p.m) :
    i ∈ contacts p indices ↔ ∃ j, indices j = some i := by
  classical
  simp [contacts]

lemma sampled_mem (p : Params) (indices : Fin p.s → Fin p.m) (j : Fin p.s) :
    indices j ∈ contacts p (fun k => some (indices k)) := by
  rw [mem_contacts]
  exact ⟨j, rfl⟩

lemma mem_block_contacts (p : Params) (block : ℕ) (i : Fin p.m) :
    i ∈ contacts p (blockIndices p block) ↔
      block * p.s ≤ i.val ∧ i.val < (block + 1) * p.s := by
  rw [mem_contacts]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hb : block * p.s + j.val < p.m
    · simp only [blockIndices, dite_eq_left hb] at hj
      have he := congrArg Fin.val (Option.some.inj hj)
      have hjlt := j.isLt
      simp only [Nat.add_mul, Nat.one_mul]
      dsimp at he
      omega
    · simp [blockIndices, hb] at hj
  · rintro ⟨hl, hu⟩
    have hlt : i.val - block * p.s < p.s := by
      simp only [Nat.add_mul, Nat.one_mul] at hu
      omega
    refine ⟨⟨i.val - block * p.s, hlt⟩, ?_⟩
    have he : block * p.s + (i.val - block * p.s) = i.val := Nat.add_sub_of_le hl
    simp only [blockIndices, he, dite_eq_left i.isLt]

lemma snapshot_eval (p : Params) (inst : Instance p) (x : p.E)
    (k block : ℕ) (cache : Fin p.m → p.E) (i : Fin p.m) :
    Program.eval (reply inst) (Algorithms.CappedProximal.snapshotPlan p x k block cache) i =
      if block * p.s ≤ i.val ∧ i.val < (block + k) * p.s
      then gradient (inst.components i) x else cache i := by
  induction k generalizing block cache with
  | zero => simp [Algorithms.CappedProximal.snapshotPlan, Program.eval]
  | succ k ih =>
      simp only [Algorithms.CappedProximal.snapshotPlan, Program.eval, ih]
      have hm : i ∈ (gradientQuery p (blockIndices p block) x).clients ↔
          block * p.s ≤ i.val ∧ i.val < (block + 1) * p.s := mem_block_contacts p block i
      have hr : reply inst (gradientQuery p (blockIndices p block) x) i =
          if block * p.s ≤ i.val ∧ i.val < (block + 1) * p.s
          then gradient (inst.components i) x else 0 := by
        simp only [reply, gradientQuery, roundQuery, mem_block_contacts]
      simp only [hm, hr]
      have he : (block + 1 + k) * p.s = (block + (k + 1)) * p.s := by congr 1; omega
      rw [he]
      have hle : block * p.s ≤ (block + 1) * p.s := Nat.mul_le_mul_right p.s (by omega)
      have hle2 : (block + 1) * p.s ≤ (block + (k + 1)) * p.s :=
        Nat.mul_le_mul_right p.s (by omega)
      split_ifs <;> first | rfl | omega

lemma snapshot_covers (p : Params) (hs : 0 < p.s) :
    p.m ≤ snapshotLength p * p.s := by
  have hm := Nat.mod_lt (p.m + p.s - 1) hs
  have hd := Nat.div_add_mod (p.m + p.s - 1) p.s
  dsimp [snapshotLength]
  rw [Nat.mul_comm p.s] at hd
  omega

lemma full_snapshot_eval (p : Params) (inst : Instance p) (hs : 0 < p.s)
    (x : p.E) (cache : Fin p.m → p.E) :
    Program.eval (reply inst)
      (Algorithms.CappedProximal.snapshotPlan p x (snapshotLength p) 0 cache) =
      fun i => gradient (inst.components i) x := by
  funext i
  rw [snapshot_eval]
  have hi : i.val < snapshotLength p * p.s := lt_of_lt_of_le i.isLt (snapshot_covers p hs)
  simp [hi]

lemma gradient_reply (p : Params) (inst : Instance p)
    (indices : Fin p.s → Fin p.m) (x : p.E) (j : Fin p.s) :
    reply inst (gradientQuery p (fun k => some (indices k)) x) (indices j) =
      gradient (inst.components (indices j)) x := by
  simp [reply, gradientQuery, roundQuery, sampled_mem]

lemma proximal_reply (p : Params) (inst : Instance p)
    (indices : Fin p.s → Fin p.m) (a : {a : ℝ // 0 < a})
    (centers : Fin p.m → p.E) (j : Fin p.s) :
    reply inst (proximalQuery p (fun k => some (indices k)) a centers) (indices j) =
      inst.prox (indices j) a.val (centers (indices j)) := by
  simp [reply, proximalQuery, roundQuery, sampled_mem]

lemma corrected_prox_eval (p : Params) (inst : Instance p)
    (indices : Fin p.s → Fin p.m) (a : {a : ℝ // 0 < a}) (x g : p.E) :
    Program.eval (reply inst) (correctedProxPlan p indices a x g) =
      (p.s : ℝ)⁻¹ • ∑ j, inst.prox (indices j) a.val
        (x + a.val⁻¹ • (gradient (inst.components (indices j)) x - g)) := by
  simp only [correctedProxPlan, Program.eval]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [proximal_reply, gradient_reply]

lemma epoch_one_eval (p : Params) (inst : Instance p) (center : p.E)
    (cache : Fin p.m → p.E) (samples : Cohorts p) (state : State p.E)
    (ht : 0 < innerRegularization p + outerRegularization p) :
    let x := predictor (innerRegularization p) state
    let g := (p.m : ℝ)⁻¹ • (∑ i, cache i) + (p.s : ℝ)⁻¹ •
      (∑ j, (gradient (inst.components (samples.1 j)) x - cache (samples.1 j))) +
        outerRegularization p • (x - center)
    let z := (p.s : ℝ)⁻¹ • ∑ j, inst.prox (samples.2 j)
      (innerRegularization p + outerRegularization p)
      (x + (innerRegularization p + outerRegularization p)⁻¹ •
        (gradient (inst.components (samples.2 j)) x - g))
    Program.eval (reply inst) (epochSteps p center cache 1 (fun _ => samples) state) =
      advance (innerRegularization p) state z := by
  dsimp only
  simp only [epochSteps, Program.eval, Program.eval_bind, corrected_prox_eval,
    gradient_reply, positiveCoefficient, dite_eq_left ht]

lemma epoch_steps_eval_succ (p : Params) (answer : Query p → Fin p.m → p.E)
    (center : p.E) (cache : Fin p.m → p.E) (k : ℕ)
    (samples : Fin (k + 1) → Cohorts p) (state : State p.E) :
    Program.eval answer (epochSteps p center cache (k + 1) samples state) =
      Program.eval answer (epochSteps p center cache k (fun j => samples j.succ)
        (Program.eval answer (epochSteps p center cache 1 (fun _ => samples 0) state))) := by
  simp only [epochSteps, Program.eval, Program.eval_bind]

lemma epoch_steps_eval_snoc (p : Params) (answer : Query p → Fin p.m → p.E)
    (center : p.E) (cache : Fin p.m → p.E) (k : ℕ)
    (samples : Fin k → Cohorts p) (last : Cohorts p) (state : State p.E) :
    Program.eval answer (epochSteps p center cache (k + 1) (Fin.snoc samples last) state) =
      Program.eval answer (epochSteps p center cache 1 (fun _ => last)
        (Program.eval answer (epochSteps p center cache k samples state))) := by
  induction k generalizing state with
  | zero => simp only [Fin.snoc_zero, epochSteps, Program.eval]
  | succ k ih =>
    rw [← Fin.cons_self_tail samples, ← Fin.cons_snoc_eq_snoc_cons]
    rw [epoch_steps_eval_succ p answer center cache (k + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    rw [epoch_steps_eval_succ p answer center cache k]
    simp only [Fin.cons_zero, Fin.cons_succ]

lemma outer_one_eval (p : Params) (answer : Query p → Fin p.m → p.E)
    (samples : Fin (solveLength p) → Fin (epochLength p) → Cohorts p) (state : State p.E) :
    Program.eval answer (outerSteps p 1 (fun _ => samples) state) =
      advance (outerRegularization p) state (Program.eval answer
        (solvePlan p (predictor (outerRegularization p) state) (solveLength p) samples state.primal)) := by
  simp only [outerSteps, Program.eval_bind, Program.eval]

lemma outer_steps_eval_succ (p : Params) (answer : Query p → Fin p.m → p.E) (k : ℕ)
    (samples : Fin (k + 1) → Fin (solveLength p) → Fin (epochLength p) → Cohorts p) (state : State p.E) :
    Program.eval answer (outerSteps p (k + 1) samples state) =
      Program.eval answer (outerSteps p k (fun j => samples j.succ)
        (Program.eval answer (outerSteps p 1 (fun _ => samples 0) state))) := by
  simp only [outerSteps, Program.eval_bind, Program.eval]

lemma outer_steps_eval_snoc (p : Params) (answer : Query p → Fin p.m → p.E) (k : ℕ)
    (samples : Fin k → Fin (solveLength p) → Fin (epochLength p) → Cohorts p)
    (last : Fin (solveLength p) → Fin (epochLength p) → Cohorts p) (state : State p.E) :
    Program.eval answer (outerSteps p (k + 1) (Fin.snoc samples last) state) =
      Program.eval answer (outerSteps p 1 (fun _ => last)
        (Program.eval answer (outerSteps p k samples state))) := by
  induction k generalizing state with
  | zero => simp only [Fin.snoc_zero, outerSteps, Program.eval_bind, Program.eval]
  | succ k ih =>
    rw [← Fin.cons_self_tail samples, ← Fin.cons_snoc_eq_snoc_cons]
    rw [outer_steps_eval_succ p answer (k + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    rw [outer_steps_eval_succ p answer k]
    simp only [Fin.cons_zero, Fin.cons_succ]

lemma corrected_prox_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (indices : Fin p.s → Fin p.m) (a : {a : ℝ // 0 < a}) (x g : p.E) :
    Program.cost answer (correctedProxPlan p indices a x g) = 2 := by
  rfl

lemma snapshot_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (x : p.E) (k block : ℕ) (cache : Fin p.m → p.E) :
    Program.cost answer (snapshotPlan p x k block cache) = k := by
  induction k generalizing block cache with
  | zero => rfl
  | succ k ih => simp only [Algorithms.CappedProximal.snapshotPlan, Program.cost, ih]

lemma epoch_steps_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (center : p.E) (cache : Fin p.m → p.E) (k : ℕ) (samples : Fin k → Cohorts p)
    (state : Algorithms.CappedProximal.State p.E) :
    Program.cost answer (epochSteps p center cache k samples state) = 3 * k := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih =>
      simp only [epochSteps, Program.cost, Program.cost_bind, corrected_prox_cost, ih]
      omega

lemma epoch_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (center start : p.E) (samples : Fin (epochLength p) → Cohorts p) :
    Program.cost answer (Algorithms.CappedProximal.epochPlan p center start samples) =
      snapshotLength p + 3 * epochLength p := by
  simp only [Algorithms.CappedProximal.epochPlan, Program.cost_bind, snapshot_cost,
    Program.cost_map, epoch_steps_cost]

lemma solve_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (center : p.E) (k : ℕ) (samples : Fin k → Fin (epochLength p) → Cohorts p) (start : p.E) :
    Program.cost answer (solvePlan p center k samples start) =
      k * (snapshotLength p + 3 * epochLength p) := by
  induction k generalizing start with
  | zero => simp [solvePlan, Program.cost]
  | succ k ih =>
      simp only [solvePlan, Program.cost_bind, epoch_cost, ih]
      ring

lemma outer_steps_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (k : ℕ) (samples : Fin k → Fin (solveLength p) → Fin (epochLength p) → Cohorts p)
    (state : Algorithms.CappedProximal.State p.E) :
    Program.cost answer (outerSteps p k samples state) =
      k * solveLength p * (snapshotLength p + 3 * epochLength p) := by
  induction k generalizing state with
  | zero => simp [outerSteps, Program.cost]
  | succ k ih =>
      simp only [outerSteps, Program.cost_bind, solve_cost, ih]
      ring

lemma restarts_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (k : ℕ) (samples : Fin k → Fin (outerLength p) → Fin (solveLength p) →
      Fin (epochLength p) → Cohorts p) (start : p.E) :
    Program.cost answer (restartsPlan p k samples start) =
      k * outerLength p * solveLength p * (snapshotLength p + 3 * epochLength p) := by
  induction k generalizing start with
  | zero => simp [restartsPlan, Program.cost]
  | succ k ih =>
      simp only [restartsPlan, Program.cost_bind, outer_steps_cost, ih]
      ring

lemma plan_cost (p : Params) (answer : Query p → Fin p.m → p.E)
    (seed : Algorithms.CappedProximal.Seeds p) :
    Program.cost answer (Algorithms.CappedProximal.plan p seed) =
      restartCount p * outerLength p * solveLength p *
        (snapshotLength p + 3 * epochLength p) := by
  exact restarts_cost p answer (restartCount p) seed p.x0

lemma output_eq_eval (p : Params) (inst : Instance p)
    (oracle : OracleTemplate.Oracle (Query p) (Fin p.m → p.E))
    (hanswer : ∀ history query seed, oracle.answer history (0, query) seed = reply inst query)
    (budget : ℕ) (seed : Algorithms.CappedProximal.Seeds p)
    (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hbudget : restartCount p * outerLength p * solveLength p *
      (snapshotLength p + 3 * epochLength p) ≤ budget) :
    Algorithms.CappedProximal.output p oracle budget seed oracleSeed =
      Program.eval (reply inst) (Algorithms.CappedProximal.plan p seed) := by
  unfold Algorithms.CappedProximal.output
  erw [OracleTemplate.execute_eq_of_answer_eq oracle (reply inst) hanswer,
    OracleTemplate.execute_iterate (reply inst) (Algorithms.CappedProximal.algorithm p) budget seed]
  change Program.output p.x0
    ((fun state : Program (Query p) (Fin p.m → p.E) p.E =>
      state.update (reply inst (state.query (gradientQuery p (fun _ => none) p.x0))))^[budget]
        (Algorithms.CappedProximal.plan p seed)) = _
  rw [Program.iterate_of_cost_le (reply inst) (gradientQuery p (fun _ => none) p.x0)
    budget _ (by rw [plan_cost]; exact hbudget)]
  rfl

end LongTails.Proofs.CappedProximalExecution
