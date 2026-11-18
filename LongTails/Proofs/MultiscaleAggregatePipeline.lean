import LongTails.Proofs.MultiscaleAggregateState
import LongTails.Proofs.MultiscaleAggregateBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.MultiscaleAggregateExecution

open DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate

noncomputable def computeTime (p : Params) : Time :=
  Finset.univ.sup (fun i : Fin p.n => (batch p i : Time) * p.h i)

noncomputable def payload (p : Params) (k : ℕ) : ℕ := p.d * width p k

noncomputable def roundTime (p : Params) (k : ℕ) : Time :=
  computeTime p + p.l + p.b * (payload p k + clockBits : ℕ) +
    if k + 1 < rounds p then p.l + p.b * (payload p k + clockBits : ℕ) else 0

noncomputable def executionTime (p : Params) : Time :=
  ∑ k ∈ Finset.range (rounds p), roundTime p k

lemma rounds_pos (p : Params) : 0 < rounds p := Nat.two_pow_pos _

noncomputable def roundStart (p : Params) (k : ℕ) : Time :=
  ∑ j ∈ Finset.range k, roundTime p j

lemma roundStart_zero (p : Params) : roundStart p 0 = 0 := by
  simp [roundStart]

lemma roundStart_succ (p : Params) (k : ℕ) :
    roundStart p (k + 1) = roundStart p k + roundTime p k := by
  exact Finset.sum_range_succ _ _

lemma roundStart_mono (p : Params) : Monotone (roundStart p) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [roundStart_succ]
  exact le_add_of_nonneg_right (by positivity)

lemma roundStart_final (p : Params) :
    roundStart p (rounds p) = executionTime p := rfl

lemma computation_finish_le (p : Params) (k j : ℕ) (i : Fin p.n)
    (hj : j ≤ (batch p i)) :
    roundStart p k + j * p.h i ≤
      roundStart p k + computeTime p := by
  exact add_le_add le_rfl <| (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (by positivity)).trans
    (Finset.le_sup (f := fun i : Fin p.n => (batch p i : Time) * p.h i) (Finset.mem_univ i))

noncomputable def workerProgress (p : Params) (v : Fin (p.n + 1)) (s : State p) : ℕ :=
  Fin.cases ((3 * p.n + 1) * s.iteration + 2 * s.arrived.card + (p.n - s.targets.length))
    (fun i => (2 * (batch p i) + 2) * s.iteration + 2 * s.samples + s.pending.toNat + s.sent.toNat) v

lemma query_progress (p : Params) (T : Time)
    (v : Fin (p.n + 1)) (s : State p) (clock : ClockReading) :
    workerProgress p v s ≤ workerProgress p v ((algorithm p T).query v s clock).2 := by
  classical
  induction v using Fin.cases with
  | zero =>
      cases ht : s.targets <;> simp [algorithm, ht, workerProgress]
      omega
  | succ i =>
      simp only [algorithm, Fin.cases_succ]
      split_ifs with hready hcount hsent
      · have hp : s.pending = false := by simpa using hready.2
        simp [workerProgress, hp]
      · have hs : s.sent = false := by simpa using hsent
        simp [workerProgress, hs]
      · simp [workerProgress]
      · simp [workerProgress]

def WorkerControl (p : Params) (i : Fin p.n) (time wake : Time) (s : State p) : Prop :=
  (s.iteration = 0 ∧ s.samples = 0 ∧ s.pending = false ∧ s.sent = false ∧ time = 0 ∧ wake = 0) ∨
  (s.iteration < (rounds p) ∧ s.samples < (batch p i) ∧ s.pending = true ∧ s.sent = false) ∨
  (s.iteration < (rounds p) ∧ s.samples = (batch p i) ∧ s.pending = false ∧ s.sent = true)

structure Pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p))
    (c : ExecutionState (system p g P) (algorithm p T)) : Prop where
  root : RootData p g samples selected (c.workers 0)
  workers : ∀ i : Fin p.n, WorkerData p g samples i (c.workers i.succ)
  seeds : ∀ i : Fin p.n, (c.oracle.computation i.succ).seed = samples
  used : ∀ i : Fin p.n, (c.oracle.computation i.succ).used =
    (c.workers i.succ).iteration * (batch p i) + (c.workers i.succ).samples
  root_limit : (c.workers 0).iteration ≤ (rounds p)
  arrived_incomplete : (c.workers 0).arrived ≠ Finset.univ
  targets_nodup : (c.workers 0).targets.Nodup
  targets_queued : ∀ i ∈ (c.workers 0).targets,
    (c.workers i.succ).iteration + 1 = (c.workers 0).iteration
  targets_active : (c.workers 0).targets ≠ [] → (c.workers 0).iteration < (rounds p)
  targets_ready : (c.workers 0).targets ≠ [] → c.wakeTime 0 ≤ c.time
  outbox : (c.workers 0).targets ≠ [] →
    (c.workers 0).outbox = rootBits p g samples ((c.workers 0).iteration - 1)
  broadcast_time : (c.workers 0).targets ≠ [] →
    c.time + (p.l + p.b * (payload p ((c.workers 0).iteration - 1) + clockBits : ℕ)) =
      roundStart p (c.workers 0).iteration
  synchronized : ∀ i : Fin p.n, (c.workers i.succ).iteration ≤ (c.workers 0).iteration ∧
    (c.workers 0).iteration ≤ (c.workers i.succ).iteration + 1
  behind : ∀ i : Fin p.n, (c.workers i.succ).iteration < (c.workers 0).iteration →
    (c.workers i.succ).samples = (batch p i) ∧ (c.workers i.succ).sent = true
  control : ∀ i : Fin p.n, WorkerControl p i c.time (c.wakeTime i.succ) (c.workers i.succ)
  root_pending : (c.oracle.computation 0).pending = none
  pending : ∀ i : Fin p.n, (c.oracle.computation i.succ).pending =
    if (c.workers i.succ).pending then
      some (roundStart p (c.workers i.succ).iteration + ((c.workers i.succ).samples + 1) * p.h i,
        (c.workers i.succ).model.point) else none
  arrived_current : ∀ i ∈ (c.workers 0).arrived,
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧ (c.workers i.succ).sent = true
  arrived_time : ∀ i ∈ (c.workers 0).arrived,
    roundStart p (c.workers 0).iteration + (batch p i) * p.h i +
      (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)) ≤ c.time
  links : ∀ source target, c.oracle.communication.messages source target =
    Fin.cases
      (Fin.cases none (fun i =>
        if (c.workers 0).iteration < (rounds p) ∧
            (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧ i ∉ (c.workers 0).targets then
          some (roundStart p (c.workers 0).iteration,
            rootBits p g samples ((c.workers 0).iteration - 1) ++
              List.replicate clockBits false) else none) target)
      (fun i =>
        if target = 0 ∧ (c.workers i.succ).iteration = (c.workers 0).iteration ∧
            (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived then
          some (roundStart p (c.workers i.succ).iteration + (batch p i) * p.h i +
              (p.l + p.b * (payload p (c.workers 0).iteration + clockBits : ℕ)),
            workerBits p g samples (c.workers i.succ).iteration i ++
              List.replicate clockBits false) else none) source

lemma initial_pipeline (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (samples : Samples p) (selected : Fin (rounds p)) (deadline : Time) :
    Pipeline p T g P samples selected
      (DistributedTemplate.initial (system p g P) (algorithm p T) deadline (selected, samples)) := by
  refine {
    root := initial_root_data p g samples selected
    workers := fun i => initial_worker_data p g samples selected i
    seeds := fun _ => rfl
    used := fun i => by
      change 0 = 0 * (batch p i) + 0
      simp
    root_limit := Nat.zero_le _
    arrived_incomplete := ?_
    targets_nodup := List.nodup_nil
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    synchronized := ?_
    behind := ?_
    control := ?_
    root_pending := rfl
    pending := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · change (∅ : Finset (Fin p.n)) ≠ Finset.univ
    intro he
    have hm := Finset.mem_univ (0 : Fin p.n)
    rw [← he] at hm
    exact Finset.notMem_empty _ hm
  · simp [DistributedTemplate.initial, algorithm]
  · simp [DistributedTemplate.initial, algorithm]
  · simp [DistributedTemplate.initial, algorithm]
  · simp [DistributedTemplate.initial, algorithm]
  · simp [DistributedTemplate.initial, algorithm]
  · intro i
    simp [DistributedTemplate.initial, algorithm]
  · intro i hlt
    simp [DistributedTemplate.initial, algorithm] at hlt
  · intro i
    simp [WorkerControl, DistributedTemplate.initial, algorithm]
  · intro i
    simp [DistributedTemplate.initial, algorithm, system, LongTails.Setups.StarNetwork.system,
      Oracle.initial, LongTails.Setups.StarNetwork.computation]
  · intro i hi
    simp [DistributedTemplate.initial, algorithm] at hi
  · intro i hi
    simp [DistributedTemplate.initial, algorithm] at hi
  · intro source target
    refine Fin.cases ?_ (fun i => ?_) source
    · refine Fin.cases ?_ (fun i => ?_) target <;>
        simp [DistributedTemplate.initial, algorithm, system, LongTails.Setups.StarNetwork.system,
          Oracle.initial, LongTails.Setups.StarNetwork.communication]
    · simp [DistributedTemplate.initial, algorithm, system, LongTails.Setups.StarNetwork.system,
        Oracle.initial, LongTails.Setups.StarNetwork.communication]


end LongTails.Proofs.MultiscaleAggregateExecution
