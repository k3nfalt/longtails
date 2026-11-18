import LongTails.Proofs.DistributedNormalizedProtocol
import LongTails.Proofs.DistributedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedNormalizedExecution

open DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open LongTails.Algorithms.DistributedNormalizedProtocol

noncomputable def roundStart (p : Params) (cfg : Config) (k : ℕ) : Time :=
  ∑ j ∈ Finset.range k, roundTime p cfg j

lemma roundStart_zero (p : Params) (cfg : Config) : roundStart p cfg 0 = 0 := by
  simp [roundStart]

lemma roundStart_succ (p : Params) (cfg : Config) (k : ℕ) :
    roundStart p cfg (k + 1) = roundStart p cfg k + roundTime p cfg k := by
  exact Finset.sum_range_succ _ _

lemma roundStart_mono (p : Params) (cfg : Config) : Monotone (roundStart p cfg) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [roundStart_succ]
  exact le_add_of_nonneg_right (by positivity)

lemma roundStart_final (p : Params) (cfg : Config) :
    roundStart p cfg cfg.iterations = executionTime p cfg := rfl

lemma computation_finish_le (p : Params) (cfg : Config) (k j : ℕ) (i : Fin p.n)
    (hj : j ≤ cfg.batch) :
    roundStart p cfg k + j * p.h i ≤
      roundStart p cfg k + cfg.batch * Finset.univ.sup p.h := by
  apply add_le_add le_rfl
  exact mul_le_mul (Nat.cast_le.mpr hj) (Finset.le_sup (f := p.h) (Finset.mem_univ i))
    (by positivity) (by positivity)

def workerProgress (p : Params) (cfg : Config) (v : Fin (p.n + 1)) (s : State p) : ℕ :=
  Fin.cases ((3 * p.n + 1) * s.iteration + 2 * s.arrived.card + (p.n - s.targets.length))
    (fun _ => (2 * cfg.batch + 2) * s.iteration + 2 * s.samples + s.pending.toNat + s.sent.toNat) v

lemma query_progress (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (v : Fin (p.n + 1)) (s : State p) (clock : ClockReading) :
    workerProgress p cfg v s ≤ workerProgress p cfg v ((algorithm p cfg T).query v s clock).2 := by
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

open LongTails.Setups.DistributedSmoothNonconvex (system Samples)
open DistributedNormalizedProtocol

def WorkerControl (cfg : Config) (time wake : Time) (s : State p) : Prop :=
  (s.iteration = 0 ∧ s.samples = 0 ∧ s.pending = false ∧ s.sent = false ∧ time = 0 ∧ wake = 0) ∨
  (s.iteration < cfg.iterations ∧ s.samples < cfg.batch ∧ s.pending = true ∧ s.sent = false) ∨
  (s.iteration < cfg.iterations ∧ s.samples = cfg.batch ∧ s.pending = false ∧ s.sent = true)

structure Pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T)) : Prop where
  root : RootData p cfg D g samples selected (c.workers 0)
  workers : ∀ i : Fin p.n, WorkerData p cfg D g samples i (c.workers i.succ)
  seeds : ∀ i : Fin p.n, (c.oracle.computation i.succ).seed = samples
  used : ∀ i : Fin p.n, (c.oracle.computation i.succ).used =
    (c.workers i.succ).iteration * cfg.batch + (c.workers i.succ).samples
  root_limit : (c.workers 0).iteration ≤ cfg.iterations
  arrived_incomplete : (c.workers 0).arrived ≠ Finset.univ
  targets_nodup : (c.workers 0).targets.Nodup
  targets_queued : ∀ i ∈ (c.workers 0).targets,
    (c.workers i.succ).iteration + 1 = (c.workers 0).iteration
  targets_active : (c.workers 0).targets ≠ [] → (c.workers 0).iteration < cfg.iterations
  targets_ready : (c.workers 0).targets ≠ [] → c.wakeTime 0 ≤ c.time
  outbox : (c.workers 0).targets ≠ [] → ∀ i : Fin p.n,
    (c.workers 0).outbox i = rootMessage p cfg D g samples ((c.workers 0).iteration - 1) i
  broadcast_time : (c.workers 0).targets ≠ [] →
    c.time + (p.l + p.b * (downlinkPayload p cfg ((c.workers 0).iteration - 1) + clockBits : ℕ)) =
      roundStart p cfg (c.workers 0).iteration
  rounds : ∀ i : Fin p.n, (c.workers i.succ).iteration ≤ (c.workers 0).iteration ∧
    (c.workers 0).iteration ≤ (c.workers i.succ).iteration + 1
  behind : ∀ i : Fin p.n, (c.workers i.succ).iteration < (c.workers 0).iteration →
    (c.workers i.succ).samples = cfg.batch ∧ (c.workers i.succ).sent = true
  control : ∀ i : Fin p.n, WorkerControl cfg c.time (c.wakeTime i.succ) (c.workers i.succ)
  root_pending : (c.oracle.computation 0).pending = none
  pending : ∀ i : Fin p.n, (c.oracle.computation i.succ).pending =
    if (c.workers i.succ).pending then
      some (roundStart p cfg (c.workers i.succ).iteration + ((c.workers i.succ).samples + 1) * p.h i,
        (c.workers i.succ).point) else none
  arrived_current : ∀ i ∈ (c.workers 0).arrived,
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧ (c.workers i.succ).sent = true
  arrived_time : ∀ i ∈ (c.workers 0).arrived,
    roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)) ≤ c.time
  links : ∀ source target, c.oracle.communication.messages source target =
    Fin.cases
      (Fin.cases none (fun i =>
        if (c.workers 0).iteration < cfg.iterations ∧
            (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧ i ∉ (c.workers 0).targets then
          some (roundStart p cfg (c.workers 0).iteration,
            rootMessage p cfg D g samples ((c.workers 0).iteration - 1) i ++
              List.replicate clockBits false) else none) target)
      (fun i =>
        if target = 0 ∧ (c.workers i.succ).iteration = (c.workers 0).iteration ∧
            (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived then
          some (roundStart p cfg (c.workers i.succ).iteration + cfg.batch * p.h i +
              (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)),
            workerMessage p cfg D g samples (c.workers i.succ).iteration i ++
              List.replicate clockBits false) else none) source

lemma initial_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations) (deadline : Time) :
    Pipeline p cfg T g P D samples selected
      (DistributedTemplate.initial (system p.toParams g P) (algorithm p cfg T) deadline ((selected, D), samples)) := by
  refine {
    root := initial_root_data p cfg D g samples selected
    workers := fun i => initial_worker_data p cfg D g samples selected i
    seeds := fun _ => rfl
    used := fun _ => by
      change 0 = 0 * (cfg.batch : ℕ) + 0
      simp
    root_limit := Nat.zero_le _
    arrived_incomplete := ?_
    targets_nodup := List.nodup_nil
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    rounds := ?_
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

def Timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget)) : Prop :=
  (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time ≤ finish) ∧
  (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
    c.time ≤ finish) ∧ ∀ v, c.time ≤ c.wakeTime v

lemma initial_timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (T : Time)
    (seed : (algorithm p cfg budget).Seed × (system p.toParams g P).Seed) :
    Timely p cfg budget g P (DistributedTemplate.initial (system p.toParams g P) (algorithm p cfg budget) T seed) := by
  simp [Timely, DistributedTemplate.initial, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
    LongTails.Setups.StarNetwork.computation, LongTails.Setups.StarNetwork.communication]

lemma jump_timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget))
    (hc : c.time ≤ c.deadline) (htimely : Timely p cfg budget g P c) :
    Timely p cfg budget g P { c with time := nextTime (event (system p.toParams g P) (algorithm p cfg budget) c) c.time c.deadline } := by
  let O := system p.toParams g P
  let A := algorithm p cfg budget
  have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) P A c hc
  rcases htimely with ⟨hcompute, hcomm, hwake⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i finish input hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcompute i finish input hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inl
    refine ⟨i.succ, ?_⟩
    exact (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
      (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) finish).mpr ⟨finish, input, hpending, le_rfl⟩
  · intro source target finish bits hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcomm source target finish bits hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inr
    exact (DistributedExecution.communication_ready (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩
      c.oracle.communication finish).mpr ⟨source, target, finish, bits, hpending, le_rfl⟩
  · intro v
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline (c.wakeTime v) hex (hwake v)
    exact (DistributedExecution.event_ready O A c (c.wakeTime v)).mpr (Or.inr ⟨v, le_rfl⟩)

lemma event_timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget)) (htimely : Timely p cfg budget g P c)
    (v : Fin (p.n + 1)) (notification : Event (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams) (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams))
    (next : OracleState (system p.toParams g P))
    (hevent : event (system p.toParams g P) (algorithm p cfg budget) c c.time = some ((v, notification), next)) :
    Timely p cfg budget g P { c with oracle := next } := by
  classical
  rcases DistributedExecution.event_cases (system p.toParams g P) (algorithm p cfg budget)
    c c.time v notification next hevent with horacle | ⟨_, hnext, _⟩
  · rcases htimely with ⟨hcompute, hcomm, hwake⟩
    rcases DistributedExecution.oracle_answer_cases (system p.toParams g P) c.oracle next c.time v notification horacle with
      ⟨reply, state, _, ha, rfl⟩ | ⟨reply, state, _, ha, rfl⟩
    · refine ⟨?_, hcomm, hwake⟩
      intro i finish input hpending
      by_cases hv : i.succ = v
      · have hp : state.pending = some (finish, input) := by simpa [hv] using hpending
        rcases DistributedExecution.computation_answer_pending ⟨p.h, p.l, p.b⟩
          (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) v
          (c.oracle.computation v) state c.time reply ha with hnone | hold
        · simp [hnone] at hp
        · apply hcompute i finish input
          simpa [hv, ← hold] using hp
      · apply hcompute i finish input
        simpa [hv] using hpending
    · refine ⟨hcompute, ?_, hwake⟩
      intro source target finish bits hpending
      rcases DistributedExecution.communication_answer_pending (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩
        c.oracle.communication state c.time v reply ha source target with hnone | hold
      · simp [hnone] at hpending
      · exact hcomm source target finish bits (hold ▸ hpending)
  · simpa only [hnext] using htimely

lemma step_timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg budget))
    (htimely : Timely p cfg budget g P c)
    (hstep : step (system p.toParams g P) (algorithm p cfg budget) c = some next) : Timely p cfg budget g P next := by
  classical
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate] at hstep
    have hc : c.time ≤ c.deadline := le_of_not_gt hlate
    cases he : event (system p.toParams g P) (algorithm p cfg budget) c c.time with
    | none =>
        rw [he] at hstep
        by_cases hdeadline : c.time = c.deadline
        · simp only [ite_eq_left hdeadline, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdeadline] at hstep
          have hn := Option.some.inj hstep
          subst next
          exact jump_timely p cfg budget g P c hc htimely
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        have ho := event_timely p cfg budget g P c htimely v notification oracle he
        rcases ho with ⟨hcompute, hcomm, hwake⟩
        rw [he] at hstep
        cases hq : (algorithm p cfg budget).query v
            ((algorithm p cfg budget).update v (c.workers v) ((algorithm p cfg budget).clock c.time) notification)
            ((algorithm p cfg budget).clock c.time) with
        | mk action state =>
            simp only [hq] at hstep
            cases action with
            | compute query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨?_, hcomm, ?_⟩
                · intro i finish input hpending
                  by_cases hv : i.succ = v
                  · have hp : ((system p.toParams g P).computation.submit i.succ
                        (oracle.computation i.succ) c.time query).pending = some (finish, input) := by
                      simpa [← hv] using hpending
                    exact DistributedExecution.computation_submit_timely ⟨p.h, p.l, p.b⟩
                      (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) i
                      (oracle.computation i.succ) c.time query (hcompute i) finish input hp
                  · apply hcompute i finish input
                    simpa [hv] using hpending
                · intro w
                  by_cases hw : w = v
                  · simp [hw]
                  · simpa [hw] using hwake w
            | communicate query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨hcompute, ?_, ?_⟩
                · exact DistributedExecution.communication_submit_timely (Seed := Samples p.toParams)
                    ⟨p.h, p.l, p.b⟩ oracle.communication c.time v
                    (query.1, query.2 ++ List.replicate clockBits false) hcomm
                · intro w
                  by_cases hw : w = v
                  · simp [hw]
                  · simpa [hw] using hwake w
            | advance target =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨hcompute, hcomm, ?_⟩
                intro w
                by_cases hw : w = v
                · simp [hw]
                · simpa [hw] using hwake w

lemma run_timely (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (T : Time)
    (seed : (algorithm p cfg budget).Seed × (system p.toParams g P).Seed) (k : ℕ) :
    Timely p cfg budget g P (run (system p.toParams g P) (algorithm p cfg budget) k
      (DistributedTemplate.initial (system p.toParams g P) (algorithm p cfg budget) T seed)) := by
  have hrun : ∀ j (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget)),
      Timely p cfg budget g P c → Timely p cfg budget g P (run (system p.toParams g P) (algorithm p cfg budget) j c) := by
    intro j
    induction j with
    | zero => intro c hc; exact hc
    | succ j ih =>
        intro c hc
        cases hs : step (system p.toParams g P) (algorithm p cfg budget) c with
        | none => simpa only [run, hs] using hc
        | some next =>
            simpa only [run, hs] using ih next (step_timely p cfg budget g P c next hc hs)
  exact hrun k _ (initial_timely p cfg budget g P T seed)

lemma completed_output (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (hk : (c.workers 0).iteration = cfg.iterations) :
    (algorithm p cfg T).output (c.workers (algorithm p cfg T).root) =
      output p cfg D g samples selected :=
  root_selected_complete p cfg D g samples selected (c.workers 0) hc.root.toRootPoints hk

lemma completed_workers (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (hk : (c.workers 0).iteration = cfg.iterations) (i : Fin p.n) :
    (c.workers i.succ).iteration + 1 = cfg.iterations ∧
    (c.workers i.succ).samples = cfg.batch ∧ (c.workers i.succ).sent = true ∧
    (c.oracle.computation i.succ).used = cfg.iterations * cfg.batch := by
  have hlt : (c.workers i.succ).iteration < cfg.iterations := by
    rcases hc.control i with h | h | h
    · rw [h.1]
      exact cfg.iterations.pos
    · exact h.1
    · exact h.1
  have hr := hc.rounds i
  rw [hk] at hr
  have he : (c.workers i.succ).iteration + 1 = cfg.iterations := by omega
  obtain ⟨hb, hs⟩ := hc.behind i (by simpa only [hk] using hlt)
  refine ⟨he, hb, hs, ?_⟩
  rw [hc.used i, hb, ← he, Nat.add_mul, Nat.one_mul]

lemma computed_at_finish (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget)) (htimely : Timely p cfg budget g P c)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p.toParams g P))
    (hevent : event (system p.toParams g P) (algorithm p cfg budget) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.oracle.computation i.succ).pending = some (c.time, input) ∧
      value = g i input ((c.oracle.computation i.succ).seed i (c.oracle.computation i.succ).used) ∧
      next = { c.oracle with computation := (Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := none, used := (c.oracle.computation i.succ).used + 1 }) } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.computed_event (system p.toParams g P) (algorithm p cfg budget)
    c c.time i.succ (.computed input value) next hevent
  obtain ⟨finish, hp, ht, hv, hs⟩ := DistributedExecution.computation_completed_data ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) i
    (c.oracle.computation i.succ) state c.time input value ha
  have hf : finish = c.time := le_antisymm ht (htimely.1 i finish input hp)
  subst finish
  exact ⟨hp, hv, by simpa only [hs] using hn⟩

lemma received_at_finish (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget)) (htimely : Timely p cfg budget g P c)
    (source target : Fin (p.n + 1)) (bits : List Bool) (next : OracleState (system p.toParams g P))
    (hevent : event (system p.toParams g P) (algorithm p cfg budget) c c.time =
      some ((target, .received (.received source bits)), next)) :
    c.oracle.communication.messages source target = some (c.time, bits) ∧
      next = { c.oracle with communication := { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages source
          (Function.update (c.oracle.communication.messages source) target none)) } } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.received_event (system p.toParams g P) (algorithm p cfg budget)
    c c.time target (.received source bits) next hevent
  obtain ⟨finish, hp, ht, hs⟩ := DistributedExecution.communication_received_data (Seed := Samples p.toParams)
    ⟨p.h, p.l, p.b⟩ c.oracle.communication state c.time source target bits ha
  have hf : finish = c.time := le_antisymm ht (htimely.2.1 source target finish bits hp)
  subst finish
  exact ⟨hp, by simpa only [hs] using hn⟩

lemma broadcast_arrived_empty (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (hh : ∀ i, 0 < p.h i)
    (htargets : (c.workers 0).targets ≠ []) : (c.workers 0).arrived = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have ha := hc.arrived_time i hi
  have ht := hc.broadcast_time htargets
  have hp : (0 : Time) < (cfg.batch : Time) * p.h i :=
    mul_pos (by exact_mod_cast cfg.batch.pos) (hh i)
  have hstart : c.time ≤ roundStart p cfg (c.workers 0).iteration := by
    rw [← ht]
    exact le_add_of_nonneg_right (by positivity)
  have hbefore : roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i ≤ c.time :=
    (le_add_of_nonneg_right (by positivity)).trans ha
  have hlt : roundStart p cfg (c.workers 0).iteration <
      roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i := by
    exact lt_add_of_pos_right _ hp
  exact (not_lt_of_ge (hbefore.trans hstart)) hlt

lemma quiet_future (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (budget : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg budget))
    (hquiet : event (system p.toParams g P) (algorithm p cfg budget) c c.time = none) :
    (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time < finish) ∧
    (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
      c.time < finish) ∧ ∀ v, c.time < c.wakeTime v := by
  have hnot : ¬ (event (system p.toParams g P) (algorithm p cfg budget) c c.time).isSome := by simp [hquiet]
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready] at hnot
  refine ⟨?_, ?_, ?_⟩
  · intro i finish input hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inl ⟨i.succ, ?_⟩)
    exact (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
      (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) c.time).mpr ⟨finish, input, hp, ht⟩
  · intro source target finish bits hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inr ?_)
    exact (DistributedExecution.communication_ready (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time).mpr ⟨source, target, finish, bits, hp, ht⟩
  · intro v
    exact lt_of_not_ge (fun ht => hnot (Or.inr ⟨v, ht⟩))

lemma quiet_targets_empty (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (hquiet : event (system p.toParams g P) (algorithm p cfg T) c c.time = none) :
    (c.workers 0).targets = [] := by
  by_contra ht
  exact (not_lt_of_ge (hc.targets_ready ht)) ((quiet_future p cfg T g P c hquiet).2.2 0)

lemma jump_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (hquiet : event (system p.toParams g P) (algorithm p cfg T) c c.time = none) :
    Pipeline p cfg T g P D samples selected
      { c with time := nextTime (event (system p.toParams g P) (algorithm p cfg T) c) c.time c.deadline } := by
  have ht := quiet_targets_empty p cfg T g P D samples selected c hc hquiet
  refine { hc with targets_ready := ?_, broadcast_time := ?_, control := ?_, arrived_time := ?_ }
  · simp only [ht, ne_eq, not_true_eq_false, false_implies]
  · simp only [ht, ne_eq, not_true_eq_false, false_implies]
  · intro i
    rcases hc.control i with hinit | hworking | hwaiting
    · have hw := (quiet_future p cfg T g P c hquiet).2.2 i.succ
      rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at hw
      exact (lt_irrefl _ hw).elim
    · exact Or.inr (Or.inl hworking)
    · exact Or.inr (Or.inr hwaiting)
  · intro i hi
    exact (hc.arrived_time i hi).trans (DistributedExecution.nextTime_ge _ _ _)

lemma worker_query_compute (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading)
    (hk : s.iteration < cfg.iterations) (hp : s.pending = false) (hj : s.samples < cfg.batch) :
    (algorithm p cfg T).query i.succ s clock = (.compute (.evaluate s.point), { s with pending := true }) := by
  simp [algorithm, hk, hp, hj]

lemma worker_query_send (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading)
    (hk : s.iteration < cfg.iterations) (hp : s.pending = false) (hj : s.samples = cfg.batch)
    (hs : s.sent = false) :
    (algorithm p cfg T).query i.succ s clock =
      (.communicate (0, uplinkMessage p cfg s.draws s.iteration i ((cfg.batch : ℝ)⁻¹ • s.accumulator)),
        { s with sent := true }) := by
  simp [algorithm, hk, hp, hj, hs]

lemma query_advance_state (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s next : State p) (v : Fin (p.n + 1)) (clock target : ClockReading)
    (hq : (algorithm p cfg T).query v s clock = (.advance target, next)) : next = s := by
  induction v using Fin.cases with
  | zero =>
      cases ht : s.targets <;> simp_all [algorithm]
  | succ i =>
      simp only [algorithm, Fin.cases_succ] at hq
      split_ifs at hq <;> simp_all

lemma idle_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (v : Fin (p.n + 1)) (clock target : ClockReading) (next : State p)
    (hq : (algorithm p cfg T).query v (c.workers v) clock = (.advance target, next)) :
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers v next
        wakeTime := Function.update c.wakeTime v (max c.time ((algorithm p cfg T).timer target))
        turn := v.val + 1 } := by
  classical
  have hn := query_advance_state p cfg T (c.workers v) next v clock target hq
  subst next
  rw [Function.update_eq_self]
  refine { hc with targets_ready := ?_, control := ?_ }
  · intro ht
    by_cases hv : (0 : Fin (p.n + 1)) = v
    · subst v
      cases hs : (c.workers 0).targets with
      | nil => exact (ht hs).elim
      | cons i rest => simp [algorithm, hs] at hq
    · simpa only [Function.update_of_ne hv] using hc.targets_ready ht
  · intro i
    by_cases hv : i.succ = v
    · rcases hc.control i with hinit | hworking | hwaiting
      · have hk : (c.workers i.succ).iteration < cfg.iterations := by
          rw [hinit.1]
          exact cfg.iterations.pos
        have hj : (c.workers i.succ).samples < cfg.batch := by
          rw [hinit.2.1]
          exact cfg.batch.pos
        have hcompute := worker_query_compute p cfg T (c.workers i.succ) i clock hk hinit.2.2.1 hj
        rw [← hv, hcompute] at hq
        cases congrArg Prod.fst hq
      · exact Or.inr (Or.inl hworking)
      · exact Or.inr (Or.inr hwaiting)
    · simpa only [Function.update_of_ne hv] using hc.control i

lemma start_worker_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0) :
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers i.succ { c.workers i.succ with pending := true }
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with computation := (Function.update c.oracle.computation i.succ
          { c.oracle.computation i.succ with pending := some (c.time + p.h i, (c.workers i.succ).point) }) } } := by
  classical
  have hw : Function.update c.workers i.succ { c.workers i.succ with pending := true } =
      fun v => { c.workers v with pending := if v = i.succ then true else (c.workers v).pending } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have ho : Function.update c.oracle.computation i.succ
      { c.oracle.computation i.succ with pending := some (c.time + p.h i, (c.workers i.succ).point) } =
      fun v => { c.oracle.computation v with pending := (if v = i.succ then
        some (c.time + p.h i, (c.workers i.succ).point) else (c.oracle.computation v).pending) } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have hwake : Function.update c.wakeTime i.succ c.time = c.wakeTime := by
    rw [hinit.2.2.2.2.1.trans hinit.2.2.2.2.2.symm, Function.update_eq_self]
  rw [hw, ho, hwake]
  refine { hc with
    root := ⟨⟨hc.root.draws, hc.root.point, hc.root.index, hc.root.selected_point⟩, hc.root.accumulator⟩
    workers := fun j => ⟨(hc.workers j).draws, (hc.workers j).point,
      (hc.workers j).count, (hc.workers j).accumulator⟩
    control := ?_
    root_pending := ?_
    pending := ?_ }
  · intro j
    by_cases hj : j = i
    · subst j
      apply Or.inr
      apply Or.inl
      refine ⟨?_, ?_, by simp, hinit.2.2.2.1⟩
      · simpa only [hinit.1] using cfg.iterations.pos
      · simpa only [hinit.2.1] using cfg.batch.pos
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [WorkerControl, ite_eq_right hs] using hc.control j
  · have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [hinit.1, hinit.2.1, hinit.2.2.2.2.1, roundStart_zero]
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [ite_eq_right hs] using hc.pending j

lemma pending_worker (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true) :
    (c.workers i.succ).iteration < cfg.iterations ∧ (c.workers i.succ).samples < cfg.batch ∧
      (c.workers i.succ).sent = false ∧ (c.workers i.succ).iteration = (c.workers 0).iteration := by
  have hcontrol := hc.control i
  simp only [WorkerControl, hpending, Bool.true_eq_false, false_and, and_false, false_or,
    true_and, or_false] at hcontrol
  obtain ⟨hk, hj, hs⟩ := hcontrol
  refine ⟨hk, hj, hs, ?_⟩
  have hle := (hc.rounds i).1
  by_contra hne
  have hbehind := (hc.behind i (lt_of_le_of_ne hle hne)).2
  rw [hs] at hbehind
  cases hbehind

lemma computed_worker_facts (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T)) (hp : Pipeline p cfg T g P D samples selected c)
    (htimely : Timely p cfg T g P c) (i : Fin p.n) (input value : Point p)
    (next : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.workers i.succ).pending = true ∧ input = (c.workers i.succ).point ∧
      c.time = roundStart p cfg (c.workers i.succ).iteration +
        ((c.workers i.succ).samples + 1) * p.h i ∧
      value = g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch + (c.workers i.succ).samples)) := by
  obtain ⟨hready, hv, _⟩ := computed_at_finish p cfg T g P c htimely i input value next he
  rw [hp.pending i] at hready
  cases hb : (c.workers i.succ).pending with
  | false => simp [hb] at hready
  | true =>
      simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at hready
      obtain ⟨ht, hx⟩ := hready
      refine ⟨rfl, hx.symm, ht.symm, ?_⟩
      rw [← hx, hp.seeds i, hp.used i] at hv
      exact hv

lemma continue_worker_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true)
    (hmore : (c.workers i.succ).samples + 1 < cfg.batch)
    (htime : c.time = roundStart p cfg (c.workers i.succ).iteration +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let value := g i (c.workers i.succ).point
      (samples i ((c.workers i.succ).iteration * cfg.batch + (c.workers i.succ).samples))
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + value
      samples := (c.workers i.succ).samples + 1 }
    let localState := { c.oracle.computation i.succ with
      pending := some (c.time + p.h i, (c.workers i.succ).point)
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with computation := Function.update c.oracle.computation i.succ localState } } := by
  classical
  intro value state localState
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hk, hj, hs, hr⟩ := pending_worker p cfg T g P D samples selected c hc i hpending
  have hw : Function.update c.workers i.succ state = fun v => { c.workers v with
      accumulator := if v = i.succ then (c.workers v).accumulator + value else (c.workers v).accumulator
      samples := if v = i.succ then (c.workers v).samples + 1 else (c.workers v).samples } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have ho : Function.update c.oracle.computation i.succ localState = fun v => { c.oracle.computation v with
      pending := if v = i.succ then localState.pending else (c.oracle.computation v).pending
      used := if v = i.succ then (c.oracle.computation v).used + 1 else (c.oracle.computation v).used } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw, ho]
  refine { hc with
    root := ?_
    workers := ?_
    used := ?_
    targets_ready := ?_
    behind := ?_
    control := ?_
    root_pending := ?_
    pending := ?_ }
  · simp only [ite_eq_right hz]
    exact ⟨⟨hc.root.draws, hc.root.point, hc.root.index, hc.root.selected_point⟩, hc.root.accumulator⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      refine ⟨(hc.workers i).draws, (hc.workers i).point, hmore.le, ?_⟩
      change (c.workers i.succ).accumulator + value = _
      rw [Finset.sum_range_succ, ← (hc.workers i).accumulator]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [ite_eq_right hne]
      exact ⟨(hc.workers j).draws, (hc.workers j).point, (hc.workers j).count, (hc.workers j).accumulator⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      rw [hc.used i, Nat.add_assoc]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.used j
  · simpa only [Function.update_of_ne hz] using hc.targets_ready
  · intro j hb
    by_cases he : j = i
    · subst j
      exact (lt_irrefl _ (hr ▸ hb)).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.behind j hb
  · intro j
    by_cases he : j = i
    · subst j
      exact Or.inr (Or.inl ⟨hk, by simpa only [ite_true] using hmore, hpending, hs⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [WorkerControl, ite_eq_right hne, Function.update_of_ne hne] using hc.control j
  · simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true, hpending]
      change some (c.time + p.h i, (c.workers i.succ).point) = _
      congr 2
      rw [htime]
      push_cast
      ring
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.pending j

lemma finish_worker_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hpending : (c.workers i.succ).pending = true)
    (hlast : (c.workers i.succ).samples + 1 = cfg.batch)
    (htime : c.time = roundStart p cfg (c.workers i.succ).iteration +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let value := g i (c.workers i.succ).point
      (samples i ((c.workers i.succ).iteration * cfg.batch + (c.workers i.succ).samples))
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + value
      samples := (c.workers i.succ).samples + 1
      pending := false
      sent := true }
    let localState := { c.oracle.computation i.succ with
      pending := none
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := Function.update c.oracle.computation i.succ localState
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages i.succ
              (Function.update (c.oracle.communication.messages i.succ) 0
                (some (c.time + (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)),
                  workerMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } } } := by
  classical
  intro value state localState
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hk, hj, hs, hr⟩ := pending_worker p cfg T g P D samples selected c hc i hpending
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have hf := (hc.arrived_current i hm).2
    rw [hs] at hf
    cases hf
  have hw : Function.update c.workers i.succ state = fun v => { c.workers v with
      accumulator := if v = i.succ then (c.workers v).accumulator + value else (c.workers v).accumulator
      samples := if v = i.succ then (c.workers v).samples + 1 else (c.workers v).samples
      pending := if v = i.succ then false else (c.workers v).pending
      sent := if v = i.succ then true else (c.workers v).sent } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  have ho : Function.update c.oracle.computation i.succ localState = fun v => { c.oracle.computation v with
      pending := if v = i.succ then localState.pending else (c.oracle.computation v).pending
      used := if v = i.succ then (c.oracle.computation v).used + 1 else (c.oracle.computation v).used } := by
    funext v
    by_cases hv : v = i.succ
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw, ho]
  refine { hc with
    root := ?_
    workers := ?_
    used := ?_
    targets_ready := ?_
    behind := ?_
    control := ?_
    root_pending := ?_
    pending := ?_
    arrived_current := ?_
    links := ?_ }
  · simp only [ite_eq_right hz]
    exact ⟨⟨hc.root.draws, hc.root.point, hc.root.index, hc.root.selected_point⟩, hc.root.accumulator⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      refine ⟨(hc.workers i).draws, (hc.workers i).point, hlast.le, ?_⟩
      change (c.workers i.succ).accumulator + value = _
      rw [Finset.sum_range_succ, ← (hc.workers i).accumulator]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [ite_eq_right hne]
      exact ⟨(hc.workers j).draws, (hc.workers j).point, (hc.workers j).count, (hc.workers j).accumulator⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true]
      rw [hc.used i, Nat.add_assoc]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.used j
  · simpa only [Function.update_of_ne hz] using hc.targets_ready
  · intro j hb
    by_cases he : j = i
    · subst j
      exact (lt_irrefl _ (hr ▸ hb)).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.behind j hb
  · intro j
    by_cases he : j = i
    · subst j
      exact Or.inr (Or.inr ⟨hk, by simpa only [ite_true] using hlast, by simp, by simp⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [WorkerControl, ite_eq_right hne, Function.update_of_ne hne] using hc.control j
  · simpa only [ite_eq_right hz] using hc.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [ite_true, Bool.false_eq_true, ite_false]
      rfl
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.pending j
  · intro j hmem
    by_cases he : j = i
    · subst j
      exact (hnot hmem).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [ite_eq_right hne] using hc.arrived_current j hmem
  · intro source target
    induction source using Fin.cases with
    | zero =>
        simpa only [Function.update_of_ne hz, Fin.cases_zero] using hc.links 0 target
    | succ j =>
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Fin.cases_succ, ite_true]
          by_cases ht : target = 0
          · subst target
            simp only [Function.update_self, hr, hnot, and_self, ite_true, not_false_eq_true]
            congr 2
            rw [htime]
            have hb : (((c.workers i.succ).samples : Time) + 1) = (cfg.batch : Time) := by
              exact_mod_cast hlast
            rw [hb, hr]
          · rw [Function.update_of_ne ht, hc.links i.succ target]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simpa only [Function.update_of_ne hne, Fin.cases_succ, ite_eq_right hne] using
            hc.links j.succ target

lemma compute_update (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s : State p) (v : Fin (p.n + 1)) (clock : ClockReading) (input value : Point p) :
    (algorithm p cfg T).update v s clock (.computed (.computed input value)) =
      { s with accumulator := s.accumulator + value, samples := s.samples + 1, pending := false } := rfl

lemma computed_continue_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hmore : (c.workers i.succ).samples + 1 < cfg.batch)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts p cfg T g P D samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish p cfg T g P c htimely i input value oracle he
  obtain ⟨hk, _, _, _⟩ := pending_worker p cfg T g P D samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hk, hmore, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system,
      LongTails.Setups.StarNetwork.computation, Function.update_self, Fin.cases_succ,
      Function.update_idem, Option.some.injEq] at hstep
    subst next
    have h := continue_worker_pipeline p cfg T g P D samples selected c hp i hpending hmore ht
    simpa only [hpending] using h

lemma computed_finish_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hlast : (c.workers i.succ).samples + 1 = cfg.batch)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts p cfg T g P D samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish p cfg T g P c htimely i input value oracle he
  obtain ⟨hk, _, hs, _⟩ := pending_worker p cfg T g P D samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  have hbits : uplinkMessage p cfg (c.workers i.succ).draws (c.workers i.succ).iteration i
      ((cfg.batch : ℝ)⁻¹ • ((c.workers i.succ).accumulator + g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch + (c.workers i.succ).samples)))) =
      workerMessage p cfg D g samples (c.workers i.succ).iteration i := by
    simp only [workerMessage, ← (hp.workers i).point, batchMean, (hp.workers i).draws]
    congr 2
    rw [show Finset.range (cfg.batch) = Finset.range ((c.workers i.succ).samples + 1) by rw [hlast],
      Finset.sum_range_succ, ← (hp.workers i).accumulator]
  have hfree : c.oracle.communication.messages i.succ 0 = none := by
    rw [hp.links]
    simp only [Fin.cases_succ, hs, Bool.false_eq_true, false_and, and_false, ite_false]
  have hsubmit : (system p.toParams g P).communication.submit c.oracle.communication c.time i.succ
      ⟨0, workerMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ =
      { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages i.succ
          (Function.update (c.oracle.communication.messages i.succ) 0
            (some (c.time + (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)),
              workerMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } := by
    change (LongTails.Setups.StarNetwork.communication (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩).submit
      c.oracle.communication c.time i.succ
      ⟨0, workerMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ = _
    rw [DistributedExecution.communication_submit_free (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time i.succ 0
      (workerMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)
      (Or.inr ⟨Fin.succ_ne_zero i, rfl⟩) hfree]
    simp only [List.length_append, List.length_replicate, workerMessage, uplink_message_length]
    congr 1
    funext source target
    by_cases hv : source = i.succ
    · subst source
      simp only [Function.update_self, Function.update_apply]
      (split_ifs; congr 2) <;> ring_nf
    · simp only [Function.update_of_ne hv]
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hk, not_lt.mpr hlast.ge, hs, Bool.not_false,
      and_self, ite_true, ite_false, hbits] at hstep
    rw [hsubmit] at hstep
    simp only [Option.some.injEq] at hstep
    subst next
    exact finish_worker_pipeline p cfg T g P D samples selected c hp i hpending hlast ht

lemma broadcast_send_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n) (rest : List (Fin p.n))
    (htargets : (c.workers 0).targets = i :: rest) :
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers 0 { c.workers 0 with targets := rest }
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (roundStart p cfg (c.workers 0).iteration,
                rootMessage p cfg D g samples ((c.workers 0).iteration - 1) i ++
                  List.replicate clockBits false)))) } } } := by
  classical
  have hnonempty : (c.workers 0).targets ≠ [] := by simp only [htargets, ne_eq, List.cons_ne_nil, not_false_eq_true]
  have hnodup : (i :: rest).Nodup := htargets ▸ hc.targets_nodup
  have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
  have hround : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration :=
    hc.targets_queued i (by simp only [htargets, List.mem_cons, true_or])
  have hactive := hc.targets_active hnonempty
  have hw : Function.update c.workers 0 { c.workers 0 with targets := rest } =
      fun v => { c.workers v with targets := if v = 0 then rest else (c.workers v).targets } := by
    funext v
    by_cases hv : v = 0
    · subst v; simp only [Function.update_self, ite_true]
    · rw [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw]
  refine { hc with
    root := ⟨⟨hc.root.draws, hc.root.point, hc.root.index, hc.root.selected_point⟩, hc.root.accumulator⟩
    workers := fun j => ⟨(hc.workers j).draws, (hc.workers j).point,
      (hc.workers j).count, (hc.workers j).accumulator⟩
    targets_nodup := ?_
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    control := ?_
    links := ?_ }
  · simpa only [ite_true] using (List.nodup_cons.mp hnodup).2
  · intro j hj
    apply hc.targets_queued j
    simp only [ite_true] at hj
    simp only [htargets, List.mem_cons]
    exact Or.inr hj
  · intro _
    exact hactive
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro _ j
    exact hc.outbox hnonempty j
  · intro _
    exact hc.broadcast_time hnonempty
  · intro j
    simpa only [WorkerControl, Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro source target
    simp only [ite_true]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero =>
            simpa only [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.cases_zero] using hc.links 0 0
        | succ j =>
            by_cases he : j = i
            · subst j
              simp only [Function.update_self, Fin.cases_succ, hactive, hround, hnot,
                not_false_eq_true, and_self, ite_true]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hc.links 0 j.succ]
              simp only [Fin.cases_zero, Fin.cases_succ, htargets, List.mem_cons, he, false_or]
    | succ j =>
        simpa only [Function.update_of_ne (Fin.succ_ne_zero j), Fin.cases_succ] using hc.links j.succ target

lemma root_partial_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hpartial : insert i (c.workers 0).arrived ≠ Finset.univ)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ))) :
    let value := uplinkReceive p cfg D (c.workers 0).iteration i
      (workerMessage p cfg D g samples (c.workers 0).iteration i)
    let state := { c.workers 0 with
      accumulator := (c.workers 0).accumulator + value
      arrived := insert i (c.workers 0).arrived }
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers 0 state
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages i.succ
            (Function.update (c.oracle.communication.messages i.succ) 0 none)) } } } := by
  classical
  intro value state
  have hw : Function.update c.workers 0 state = fun v => { c.workers v with
      accumulator := if v = 0 then (c.workers v).accumulator + value else (c.workers v).accumulator
      arrived := if v = 0 then insert i (c.workers v).arrived else (c.workers v).arrived } := by
    funext v
    by_cases hv : v = 0
    · subst v; simp only [Function.update_self, ite_true]; rfl
    · simp only [Function.update_of_ne hv, ite_eq_right hv]
      rfl
  rw [hw]
  refine { hc with
    root := ?_
    workers := ?_
    arrived_incomplete := ?_
    targets_ready := ?_
    control := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · refine ⟨⟨hc.root.draws, hc.root.point, hc.root.index, hc.root.selected_point⟩, ?_⟩
    simp only [ite_true]
    rw [Finset.sum_insert hnot, hc.root.accumulator]
    dsimp only [value]
    abel
  · intro j
    simp only [ite_eq_right (Fin.succ_ne_zero j)]
    exact ⟨(hc.workers j).draws, (hc.workers j).point, (hc.workers j).count, (hc.workers j).accumulator⟩
  · simpa only [ite_true] using hpartial
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro j
    simpa only [WorkerControl, Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro j hj
    simp only [ite_true, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hc.arrived_current j hj
  · intro j hj
    simp only [ite_true, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact htime.ge
    · exact hc.arrived_time j hj
  · intro source target
    simp only [ite_true]
    induction source using Fin.cases with
    | zero =>
        simpa only [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.cases_zero] using hc.links 0 target
    | succ j =>
        simp only [Fin.cases_succ]
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, not_true_eq_false, and_false, ite_false]
          by_cases ht : target = 0
          · subst target; simp only [Function.update_self]
          · rw [Function.update_of_ne ht, hc.links i.succ target]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simpa only [Function.update_of_ne hne, Fin.cases_succ, Finset.mem_insert, he, false_or] using
            hc.links j.succ target

lemma received_worker_facts (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle)) :
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧
      (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived ∧
      c.time = roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i +
        (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)) ∧
      bits = workerMessage p cfg D g samples (c.workers 0).iteration i ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish p cfg T g P c htimely i.succ 0 bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_succ, true_and] at hm
  split_ifs at hm with hvalid
  · obtain ⟨hr, hs, hnot⟩ := hvalid
    have heq := Option.some.inj hm
    obtain ⟨ht, hb⟩ := Prod.mk.inj heq
    exact ⟨hr, hs, hnot, by simpa only [hr] using ht.symm,
      by simpa only [hr] using hb.symm⟩

lemma sent_worker (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hsent : (c.workers i.succ).sent = true) :
    (c.workers i.succ).iteration < cfg.iterations ∧ (c.workers i.succ).samples = cfg.batch ∧
      (c.workers i.succ).pending = false := by
  have hcontrol := hc.control i
  simpa only [WorkerControl, hsent, Bool.true_eq_false, false_and, and_false,
    false_or, true_and, and_true] using hcontrol

lemma last_arrival_time (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ))) :
    c.time = roundStart p cfg (c.workers 0).iteration + cfg.batch * Finset.univ.sup p.h +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)) := by
  have hmax : Finset.univ.sup p.h = p.h i := by
    apply le_antisymm _ (Finset.le_sup (f := p.h) (Finset.mem_univ i))
    apply Finset.sup_le
    intro j hj
    rw [← hcomplete, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact le_rfl
    · have hbefore := hc.arrived_time j hj
      rw [htime] at hbefore
      have hb : (cfg.batch : Time) * p.h j ≤ cfg.batch * p.h i :=
        le_of_add_le_add_left (le_of_add_le_add_right hbefore)
      exact (mul_le_mul_iff_right₀ (show (0 : Time) < cfg.batch by exact_mod_cast cfg.batch.pos)).mp hb
  rw [hmax]
  exact htime

lemma complete_workers (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ) :
    ∀ j : Fin p.n, (c.workers j.succ).iteration = (c.workers 0).iteration ∧
      (c.workers j.succ).samples = cfg.batch ∧ (c.workers j.succ).sent = true ∧
      (c.workers j.succ).pending = false := by
  intro j
  have hj : j ∈ insert i (c.workers 0).arrived := by rw [hcomplete]; exact Finset.mem_univ j
  have hf : (c.workers j.succ).iteration = (c.workers 0).iteration ∧ (c.workers j.succ).sent = true := by
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hc.arrived_current j hj
  have hw := sent_worker p cfg T g P D samples selected c hc j hf.2
  exact ⟨hf.1, hw.2.1, hf.2, hw.2.2⟩

lemma complete_messages (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ) :
    Function.update c.oracle.communication.messages i.succ
      (Function.update (c.oracle.communication.messages i.succ) 0 none) = fun _ _ => none := by
  classical
  have hall := complete_workers p cfg T g P D samples selected c hc i hr hs hcomplete
  funext source target
  induction source using Fin.cases with
  | zero =>
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, hc.links]
      induction target using Fin.cases with
      | zero => rfl
      | succ j =>
          have hne : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
          simp only [Fin.cases_zero, Fin.cases_succ, (hall j).1, hne, false_and,
            and_false, ite_false]
  | succ j =>
      by_cases he : j = i
      · subst j
        rw [Function.update_self]
        by_cases ht : target = 0
        · subst target; exact Function.update_self ..
        · rw [Function.update_of_ne ht, hc.links]
          simp only [Fin.cases_succ, ht, false_and, ite_false]
      · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
        have hj : j ∈ (c.workers 0).arrived := by
          have hm : j ∈ insert i (c.workers 0).arrived := by rw [hcomplete]; exact Finset.mem_univ j
          exact (Finset.mem_insert.mp hm).resolve_left he
        rw [Function.update_of_ne hne, hc.links]
        simp only [Fin.cases_succ, hj, not_true_eq_false, and_false, ite_false]

lemma root_complete_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + cfg.batch * p.h i +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ))) :
    let aggregate := (c.workers 0).accumulator + uplinkReceive p cfg D (c.workers 0).iteration i
      (workerMessage p cfg D g samples (c.workers 0).iteration i)
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers 0 (finish p cfg (c.workers 0) aggregate)
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages i.succ
            (Function.update (c.oracle.communication.messages i.succ) 0 none)) } } } := by
  classical
  intro aggregate
  have hall := complete_workers p cfg T g P D samples selected c hc i hr hs hcomplete
  have hm := complete_messages p cfg T g P D samples selected c hc i hr hs hcomplete
  have ht := last_arrival_time p cfg T g P D samples selected c hc i hcomplete htime
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← hr]
    exact (sent_worker p cfg T g P D samples selected c hc i hs).1
  have he : (p.n : ℝ)⁻¹ • aggregate = estimator p cfg D g samples (c.workers 0).iteration
      (trajectory p cfg D g samples (c.workers 0).iteration) :=
    completed_aggregate p cfg D g samples selected (c.workers 0) i hc.root hnot hcomplete
  have hroot : RootData p cfg D g samples selected (finish p cfg (c.workers 0) aggregate) := by
    refine ⟨finish_root_points p cfg D g samples selected (c.workers 0) aggregate hc.root.toRootPoints he, ?_⟩
    simp only [finish, Finset.sum_empty]
  have hnext : (finish p cfg (c.workers 0) aggregate).targets ≠ [] →
      (c.workers 0).iteration + 1 < cfg.iterations := by
    dsimp only [finish]
    split_ifs with h
    · exact fun _ => h
    · simp
  rw [hm]
  refine {
    root := by simpa only [Function.update_self] using hroot
    workers := ?_
    seeds := hc.seeds
    used := ?_
    root_limit := ?_
    arrived_incomplete := ?_
    targets_nodup := ?_
    targets_queued := ?_
    targets_active := ?_
    targets_ready := ?_
    outbox := ?_
    broadcast_time := ?_
    rounds := ?_
    behind := ?_
    control := ?_
    root_pending := hc.root_pending
    pending := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.workers j
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.used j
  · simpa only [Function.update_self, finish] using Nat.succ_le_of_lt hk
  · change (∅ : Finset (Fin p.n)) ≠ Finset.univ
    intro hempty
    have hj := Finset.mem_univ (0 : Fin p.n)
    rw [← hempty] at hj
    exact Finset.notMem_empty _ hj
  · simp only [Function.update_self, finish]
    split_ifs
    · exact List.nodup_finRange _
    · exact List.nodup_nil
  · intro j _
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), finish] using
      congrArg (fun k => k + 1) (hall j).1
  · simpa only [Function.update_self, finish] using hnext
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro _ j
    have hmsg := finish_root_message p cfg D g samples selected (c.workers 0) aggregate hc.root.toRootPoints he j
    simpa only [Function.update_self, finish, Nat.add_sub_cancel] using hmsg
  · intro htargets
    have hnew := hnext (by simpa only [Function.update_self] using htargets)
    simp only [Function.update_self, finish, Nat.add_sub_cancel]
    rw [roundStart_succ, ht]
    simp only [roundTime, ite_eq_left hnew]
    ring
  · intro j
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), finish, (hall j).1]
    omega
  · intro j _
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using ⟨(hall j).2.1, (hall j).2.2.1⟩
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.pending j
  · simp only [Function.update_self, finish, Finset.notMem_empty, false_implies, implies_true]
  · simp only [Function.update_self, finish, Finset.notMem_empty, false_implies, implies_true]
  · intro source target
    simp only [Function.update_self, finish]
    induction source using Fin.cases with
    | zero =>
        induction target using Fin.cases with
        | zero => rfl
        | succ j =>
            simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
            split_ifs <;> simp_all
    | succ j =>
        have hne : (c.workers 0).iteration ≠ (c.workers 0).iteration + 1 := by omega
        simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j), (hall j).1, hne,
          false_and, and_false, ite_false]

lemma root_query_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) :
    match (algorithm p cfg T).query 0 (c.workers 0) 0 with
    | (.compute _, _) => False
    | (.communicate (target, bits), state) =>
        Pipeline p cfg T g P D samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 c.time
            turn := 1
            oracle := { c.oracle with communication := ((system p.toParams g P).communication.submit
              c.oracle.communication c.time 0 (target, bits ++ List.replicate clockBits false)) } }
    | (.advance target, state) =>
        Pipeline p cfg T g P D samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 (max c.time ((algorithm p cfg T).timer target))
            turn := 1 } := by
  classical
  cases ht : (c.workers 0).targets with
  | nil =>
      have hq : (algorithm p cfg T).query 0 (c.workers 0) 0 = (.advance 0, c.workers 0) := by
        simp [algorithm, ht]
      rw [hq]
      exact idle_pipeline p cfg T g P D samples selected c hc 0 0 0 _ hq
  | cons i rest =>
      let bits := rootMessage p cfg D g samples ((c.workers 0).iteration - 1) i
      have hnonempty : (c.workers 0).targets ≠ [] := by simp only [ht, List.cons_ne_nil, ne_eq, not_false_eq_true]
      have ho : (c.workers 0).outbox i = bits := hc.outbox hnonempty i
      have hq : (algorithm p cfg T).query 0 (c.workers 0) 0 =
          (.communicate (i.succ, bits), { c.workers 0 with targets := rest }) := by
        simp only [algorithm, Fin.cases_zero, ht, ho]
      rw [hq]
      dsimp only
      have hfree : c.oracle.communication.messages 0 i.succ = none := by
        simp only [hc.links, Fin.cases_zero, Fin.cases_succ, ht, List.mem_cons_self,
          not_true_eq_false, and_false, ite_false]
      have hsubmit : (system p.toParams g P).communication.submit c.oracle.communication c.time 0
          (i.succ, bits ++ List.replicate clockBits false) =
          { c.oracle.communication with messages := (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (c.time + (p.l + p.b * (downlinkPayload p cfg ((c.workers 0).iteration - 1) + clockBits : ℕ)),
                bits ++ List.replicate clockBits false)))) } := by
        change (LongTails.Setups.StarNetwork.communication (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩).submit
          c.oracle.communication c.time 0 (i.succ, bits ++ List.replicate clockBits false) = _
        rw [DistributedExecution.communication_submit_free (Seed := Samples p.toParams) ⟨p.h, p.l, p.b⟩
          c.oracle.communication c.time 0 i.succ (bits ++ List.replicate clockBits false)
          (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩) hfree]
        have hlength : bits.length = downlinkPayload p cfg ((c.workers 0).iteration - 1) :=
          downlink_message_length p cfg D _ i _ _
        simp only [List.length_append, List.length_replicate, hlength]
        congr 1
        funext source target
        by_cases hs : source = 0
        · subst source
          simp only [Function.update_self, Function.update_apply]
          (split_ifs; congr 2) <;> ring_nf
        · simp only [Function.update_of_ne hs]
      rw [hsubmit, hc.broadcast_time hnonempty]
      exact broadcast_send_pipeline p cfg T g P D samples selected c hc i rest ht

lemma root_event_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (notification : Event (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams) (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams)) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((0, notification), oracle))
    (hp : Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers 0 ((algorithm p cfg T).update 0 (c.workers 0) 0 notification)
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := oracle })
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  have h := root_query_pipeline p cfg T g P D samples selected _ hp
  simp only [Function.update_self, Function.update_idem] at h
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    have hclock : (algorithm p cfg T).clock c.time = 0 := rfl
    rw [hclock] at hstep
    cases hq : (algorithm p cfg T).query 0 ((algorithm p cfg T).update 0 (c.workers 0) 0 notification) 0 with
    | mk action state =>
        simp only [hq] at h hstep
        cases action with
        | compute query => exact h.elim
        | communicate query =>
            rcases query with ⟨target, bits⟩
            simp only [Fin.val_zero, Nat.zero_add, Option.some.injEq] at hstep
            subst next
            exact h
        | advance target =>
            simp only [Fin.val_zero, Nat.zero_add, Function.update_idem, Option.some.injEq] at hstep
            subst next
            exact h

lemma root_ready_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) :
    Pipeline p cfg T g P D samples selected { c with wakeTime := Function.update c.wakeTime 0 c.time, turn := 1 } := by
  refine { hc with targets_ready := ?_, control := ?_ }
  · intro _
    simp only [Function.update_self]
    exact le_rfl
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hc.control j

lemma accept_partial (p : Params) (cfg : Config) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < cfg.iterations) (hp : insert i s.arrived ≠ Finset.univ) :
    accept p cfg s i.succ bits = { s with
      accumulator := s.accumulator + uplinkReceive p cfg s.draws s.iteration i bits
      arrived := insert i s.arrived } := by
  simp only [accept, Fin.cases_succ, hnot, not_false_eq_true, hk, and_self, ite_true, hp, ite_false]

lemma accept_complete (p : Params) (cfg : Config) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < cfg.iterations) (hp : insert i s.arrived = Finset.univ) :
    accept p cfg s i.succ bits = finish p cfg s
      (s.accumulator + uplinkReceive p cfg s.draws s.iteration i bits) := by
  simp only [accept, Fin.cases_succ, hnot, not_false_eq_true, hk, and_self, ite_true, hp]

lemma root_receive (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s : State p) (clock : ClockReading) (source : Fin (p.n + 1)) (bits : List Bool) :
    (algorithm p cfg T).update 0 s clock (.received (.received source bits)) = accept p cfg s source bits := rfl

lemma workerMessage_frame (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p.toParams) (k : ℕ) (i : Fin p.n) :
    uplinkReceive p cfg D k i (workerMessage p cfg D g samples k i ++ List.replicate clockBits false) =
      uplinkReceive p cfg D k i (workerMessage p cfg D g samples k i) := by
  unfold workerMessage
  exact uplink_receive_frame p cfg D k i _ _

lemma received_partial_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hpartial : insert i (c.workers 0).arrived ≠ Finset.univ)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  obtain ⟨hr, hs, hnot, ht, hb⟩ := received_worker_facts p cfg T g P D samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p cfg T g P c htimely i.succ 0 bits oracle he
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← hr]
    exact (sent_worker p cfg T g P D samples selected c hc i hs).1
  apply root_event_pipeline p cfg T g P D samples selected c next _ oracle he _ hstep
  rw [root_receive, accept_partial p cfg (c.workers 0) i bits hnot hk hpartial, hc.root.draws, hb,
    workerMessage_frame, ho]
  simpa only [hc.root.draws] using
    root_partial_pipeline p cfg T g P D samples selected c hc i hr hs hnot hpartial ht

lemma received_complete_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hcomplete : insert i (c.workers 0).arrived = Finset.univ)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  obtain ⟨hr, hs, hnot, ht, hb⟩ := received_worker_facts p cfg T g P D samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p cfg T g P c htimely i.succ 0 bits oracle he
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← hr]
    exact (sent_worker p cfg T g P D samples selected c hc i hs).1
  apply root_event_pipeline p cfg T g P D samples selected c next _ oracle he _ hstep
  rw [root_receive, accept_complete p cfg (c.workers 0) i bits hnot hk hcomplete, hc.root.draws, hb,
    workerMessage_frame, ho]
  exact root_complete_pipeline p cfg T g P D samples selected c hc i hr hs hnot hcomplete ht

lemma received_broadcast_facts (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle)) :
    (c.workers 0).iteration < cfg.iterations ∧ (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧
      i ∉ (c.workers 0).targets ∧
      (c.workers i.succ).samples = cfg.batch ∧ (c.workers i.succ).pending = false ∧
      (c.workers i.succ).sent = true ∧ c.time = roundStart p cfg (c.workers 0).iteration ∧
      bits = rootMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish p cfg T g P c htimely 0 i.succ bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_zero, Fin.cases_succ] at hm
  split_ifs at hm with hvalid
  obtain ⟨hi, hr, hnot⟩ := hvalid
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  obtain ⟨hcount, hsent⟩ := hp.behind i hbefore
  have hpending := (sent_worker p cfg T g P D samples selected c hp i hsent).2.2
  obtain ⟨ht, hb⟩ := Prod.mk.inj (Option.some.inj hm)
  have hk : (c.workers 0).iteration - 1 = (c.workers i.succ).iteration := by omega
  exact ⟨hi, hr, hnot, hcount, hpending, hsent, ht.symm, by simpa only [hk] using hb.symm⟩

lemma broadcast_worker_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (i : Fin p.n)
    (hk : (c.workers 0).iteration < cfg.iterations) (hqueued : i ∉ (c.workers 0).targets)
    (hr : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration)
    (hcount : (c.workers i.succ).samples = cfg.batch)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration) :
    let x := (trajectory p cfg D g samples (c.workers 0).iteration).workers i
    let state := { c.workers i.succ with
      point := x
      iteration := (c.workers 0).iteration
      accumulator := 0
      samples := 0
      pending := true
      sent := false }
    Pipeline p cfg T g P D samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := (Function.update c.oracle.computation i.succ
            { c.oracle.computation i.succ with pending := some (c.time + p.h i, x) })
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages 0
              (Function.update (c.oracle.communication.messages 0) i.succ none)) } } } := by
  classical
  intro x state
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have he := (hc.arrived_current i hm).1
    omega
  refine {
    root := by simpa only [Function.update_of_ne hz] using hc.root
    workers := ?_
    seeds := ?_
    used := ?_
    root_limit := by simpa only [Function.update_of_ne hz] using hc.root_limit
    arrived_incomplete := by simpa only [Function.update_of_ne hz] using hc.arrived_incomplete
    targets_nodup := by simpa only [Function.update_of_ne hz] using hc.targets_nodup
    targets_queued := ?_
    targets_active := by simpa only [Function.update_of_ne hz] using hc.targets_active
    targets_ready := by simpa only [Function.update_of_ne hz] using hc.targets_ready
    outbox := by simpa only [Function.update_of_ne hz] using hc.outbox
    broadcast_time := by simpa only [Function.update_of_ne hz] using hc.broadcast_time
    rounds := ?_
    behind := ?_
    control := ?_
    root_pending := by simpa only [Function.update_of_ne hz] using hc.root_pending
    pending := ?_
    arrived_current := ?_
    arrived_time := by simpa only [Function.update_of_ne hz] using hc.arrived_time
    links := ?_ }
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      refine ⟨(hc.workers i).draws, rfl, Nat.zero_le _, ?_⟩
      simp only [state, Finset.range_zero, Finset.sum_empty]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.workers j
  · intro j
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hc.seeds i
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.seeds j
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      change (c.oracle.computation i.succ).used = (c.workers 0).iteration * cfg.batch + 0
      simp only [hc.used i, hcount, ← hr, Nat.add_mul, Nat.one_mul, Nat.add_zero]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.used j
  · intro j hj
    simp only [Function.update_of_ne hz] at hj
    have hne : j ≠ i := fun he => hqueued (he ▸ hj)
    simpa only [Function.update_of_ne hz,
      Function.update_of_ne (fun he => hne (Fin.succ_inj.mp he))] using hc.targets_queued j hj
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, state]
      exact ⟨le_rfl, Nat.le_succ _⟩
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hc.rounds j
  · intro j hb
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, state, lt_self_iff_false] at hb
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [Function.update_of_ne hne, Function.update_of_ne hz] at hb ⊢
      exact hc.behind j hb
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, WorkerControl, state]
      exact Or.inr (Or.inl ⟨hk, cfg.batch.pos, trivial, trivial⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.control j
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, state, htime, Nat.cast_zero, zero_add, one_mul, ite_true]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hc.pending j
  · intro j hj
    simp only [Function.update_of_ne hz] at hj
    by_cases he : j = i
    · subst j; exact (hnot hj).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hc.arrived_current j hj
  · intro source target
    simp only [Function.update_of_ne hz]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero => simp only [Function.update_of_ne hz]; exact hc.links 0 0
        | succ j =>
            by_cases he : j = i
            · subst j
              have hn : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
              simp only [Function.update_self, Fin.cases_succ, state, hn, false_and, and_false, ite_false]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hc.links]
              simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne hne]
    | succ j =>
        rw [Function.update_of_ne (Fin.succ_ne_zero j), hc.links]
        simp only [Fin.cases_succ]
        by_cases he : j = i
        · subst j
          have hn : (c.workers i.succ).iteration ≠ (c.workers 0).iteration := by omega
          simp only [Function.update_self, state, hn, false_and, and_false, ite_false, Bool.false_eq_true]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simp only [Function.update_of_ne hne]

lemma worker_receive (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (s : State p) (i : Fin p.n) (clock : ClockReading) (bits : List Bool) :
    (algorithm p cfg T).update i.succ s clock (.received (.received 0 bits)) = receive p cfg s i bits := by
  simp only [algorithm, Fin.cases_succ, ite_true]

lemma received_broadcast_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle))
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  obtain ⟨hk, hr, hqueued, hcount, hpending, hsent, ht, hb⟩ :=
    received_broadcast_facts p cfg T g P D samples selected c hc htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish p cfg T g P c htimely 0 i.succ bits oracle he
  subst bits
  subst oracle
  let x := (trajectory p cfg D g samples (c.workers 0).iteration).workers i
  let updated : State p := { c.workers i.succ with
    point := x
    iteration := (c.workers 0).iteration
    accumulator := 0
    samples := 0
    pending := false
    sent := false }
  have hdecode : downlinkReceive p cfg (c.workers i.succ).draws (c.workers i.succ).iteration i
      (c.workers i.succ).point
      (rootMessage p cfg D g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false) = x := by
    rw [(hc.workers i).draws, (hc.workers i).point, receive_rootMessage, hr]
  have hup : (algorithm p cfg T).update i.succ (c.workers i.succ) 0
      (.received (.received 0 (rootMessage p cfg D g samples (c.workers i.succ).iteration i ++
        List.replicate clockBits false))) = updated := by
    rw [worker_receive]
    unfold receive
    rw [hdecode, hr]
  have hq := worker_query_compute p cfg T updated i 0 hk rfl cfg.batch.pos
  have hfree : (c.oracle.computation i.succ).pending = none := by
    rw [hc.pending i, hpending]
    rfl
  have hsubmit : (system p.toParams g P).computation.submit i.succ (c.oracle.computation i.succ)
      c.time (.evaluate x) = { c.oracle.computation i.succ with pending := some (c.time + p.h i, x) } :=
    DistributedExecution.computation_submit_idle ⟨p.h, p.l, p.b⟩
      (fun j y (ξ : Samples p.toParams) k => g j y (ξ j k)) i (c.oracle.computation i.succ) c.time x hfree
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    have hclock : (algorithm p cfg T).clock c.time = 0 := rfl
    simp only [hclock, hup, hq] at hstep
    change some { c with
      workers := Function.update c.workers i.succ { updated with pending := true }
      wakeTime := Function.update c.wakeTime i.succ c.time
      turn := i.succ.val + 1
      oracle := { c.oracle with
        computation := Function.update c.oracle.computation i.succ
          ((system p.toParams g P).computation.submit i.succ (c.oracle.computation i.succ) c.time (.evaluate x))
        communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ none)) } } } = some next at hstep
    rw [hsubmit] at hstep
    have hn := Option.some.inj hstep
    subst next
    exact broadcast_worker_pipeline p cfg T g P D samples selected c hc i hk hqueued hr hcount ht

lemma wake_idle_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T)) (hp : Pipeline p cfg T g P D samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p.toParams g P)) (target : ClockReading) (state : State p)
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((v, .wake), oracle))
    (hq : (algorithm p cfg T).query v (c.workers v) ((algorithm p cfg T).clock c.time) = (.advance target, state))
    (hs : step (system p.toParams g P) (algorithm p cfg T) c = some next) : Pipeline p cfg T g P D samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p.toParams g P) (algorithm p cfg T) c c.time v oracle he).1
  subst oracle
  have hup : (algorithm p cfg T).update v (c.workers v) ((algorithm p cfg T).clock c.time) .wake = c.workers v := rfl
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate, he, hup, hq, Function.update_idem, Option.some.injEq] at hs
    subst next
    exact idle_pipeline p cfg T g P D samples selected c hp v ((algorithm p cfg T).clock c.time) target state hq

lemma wake_start_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T)) (hp : Pipeline p cfg T g P D samples selected c)
    (i : Fin p.n) (oracle : OracleState (system p.toParams g P))
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0)
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((i.succ, .wake), oracle))
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p.toParams g P) (algorithm p cfg T) c c.time i.succ oracle he).1
  subst oracle
  have hk : (c.workers i.succ).iteration < cfg.iterations := by
    rw [hinit.1]
    exact cfg.iterations.pos
  have hj : (c.workers i.succ).samples < cfg.batch := by rw [hinit.2.1]; exact cfg.batch.pos
  have hnone : (c.oracle.computation i.succ).pending = none := by
    rw [hp.pending, hinit.2.2.1]
    rfl
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    simp only [algorithm, Fin.cases_succ, hk, hj, hinit.2.2.1, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system, LongTails.Setups.StarNetwork.computation,
      Fin.cases_succ, hnone, Option.some.injEq] at hstep
    subst next
    exact start_worker_pipeline p cfg T g P D samples selected c hp i hinit

lemma wake_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((v, .wake), oracle))
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  have hidle (hq : (algorithm p cfg T).query v (c.workers v) ((algorithm p cfg T).clock c.time) =
      (.advance 0, c.workers v)) : Pipeline p cfg T g P D samples selected next :=
    wake_idle_pipeline p cfg T g P D samples selected c next hc v oracle _ _ he hq hstep
  induction v using Fin.cases with
  | zero =>
      have ho := (DistributedExecution.wake_event (system p.toParams g P) (algorithm p cfg T) c c.time 0 oracle he).1
      subst oracle
      apply root_event_pipeline p cfg T g P D samples selected c next .wake c.oracle he _ hstep
      simpa only [show (algorithm p cfg T).update 0 (c.workers 0) 0 .wake = c.workers 0 from rfl,
        Function.update_eq_self] using root_ready_pipeline p cfg T g P D samples selected c hc
  | succ i =>
      rcases hc.control i with hinit | hcompute | hsent
      · exact wake_start_pipeline p cfg T g P D samples selected c next hc i oracle hinit he hstep
      · apply hidle
        simp [algorithm, hcompute.2.2.1]
      · apply hidle
        simp [algorithm, hsent.2.1, hsent.2.2.2]

lemma step_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    Pipeline p cfg T g P D samples selected next := by
  classical
  cases he : event (system p.toParams g P) (algorithm p cfg T) c c.time with
  | none =>
      unfold step at hstep
      by_cases hlate : c.deadline < c.time
      · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
      · simp only [ite_eq_right hlate, he] at hstep
        by_cases hdone : c.time = c.deadline
        · simp only [ite_eq_left hdone, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdone, Option.some.injEq] at hstep
          subst next
          exact jump_pipeline p cfg T g P D samples selected c hp he
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      cases notification with
      | wake => exact wake_pipeline p cfg T g P D samples selected c next hp v oracle he hstep
      | computed reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p.toParams g P)
            (algorithm p cfg T) c c.time v reply oracle he
          cases reply with
          | computed input value =>
              induction v using Fin.cases with
              | zero =>
                  simp only [system, LongTails.Setups.StarNetwork.system,
                    LongTails.Setups.StarNetwork.computation,
                    Fin.cases_zero, reduceCtorEq] at ha
              | succ i =>
                  by_cases hmore : (c.workers i.succ).samples + 1 < cfg.batch
                  · exact computed_continue_pipeline p cfg T g P D samples selected c next hp htimely
                      i input value oracle he hmore hstep
                  · have hpend := (computed_worker_facts p cfg T g P D samples selected c hp htimely
                      i input value oracle he).1
                    have hcount := (pending_worker p cfg T g P D samples selected c hp i hpend).2.1
                    exact computed_finish_pipeline p cfg T g P D samples selected c next hp htimely
                      i input value oracle he (by omega) hstep
      | received reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p.toParams g P)
            (algorithm p cfg T) c c.time v reply oracle he
          cases reply with
          | received source bits =>
              have hm := (received_at_finish p cfg T g P c htimely source v bits oracle he).1
              induction source using Fin.cases with
              | zero =>
                  induction v using Fin.cases with
                  | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
                  | succ i =>
                      exact received_broadcast_pipeline p cfg T g P D samples selected
                        c next hp htimely i bits oracle he hstep
              | succ i =>
                  induction v using Fin.cases with
                  | zero =>
                      by_cases hcomplete : insert i (c.workers 0).arrived = Finset.univ
                      · exact received_complete_pipeline p cfg T g P D samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                      · exact received_partial_pipeline p cfg T g P D samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                  | succ j =>
                      simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                        ite_false, reduceCtorEq] at hm

lemma run_pipeline (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (deadline : Time) (k : ℕ) :
    Pipeline p cfg T g P D samples selected (run (system p.toParams g P) (algorithm p cfg T) k
      (DistributedTemplate.initial (system p.toParams g P) (algorithm p cfg T) deadline ((selected, D), samples))) := by
  have hrun : ∀ j (c : ExecutionState (system p.toParams g P) (algorithm p cfg T)),
      Pipeline p cfg T g P D samples selected c → Timely p cfg T g P c →
      Pipeline p cfg T g P D samples selected (run (system p.toParams g P) (algorithm p cfg T) j c) := by
    intro j
    induction j with
    | zero => intro c hp _; exact hp
    | succ j ih =>
        intro c hp ht
        cases hs : step (system p.toParams g P) (algorithm p cfg T) c with
        | none => simpa only [run, hs] using hp
        | some next =>
            simpa only [run, hs] using ih next (step_pipeline p cfg T g P D samples selected c next hp ht hs)
              (step_timely p cfg T g P c next ht hs)
  exact hrun k _ (initial_pipeline p cfg T g P D samples selected deadline)
    (initial_timely p cfg T g P deadline ((selected, D), samples))

lemma unfinished_round_time (p : Params) (cfg : Config) (r : ℕ) (hr : r < cfg.iterations) :
    roundStart p cfg r + cfg.batch * Finset.univ.sup p.h +
      (p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ)) ≤ executionTime p cfg := by
  calc
    _ = roundStart p cfg r + (cfg.batch * Finset.univ.sup p.h + p.l +
        p.b * (uplinkPayload p cfg + clockBits : ℕ)) := by ring
    _ ≤ roundStart p cfg r + roundTime p cfg r := by
      unfold roundTime
      exact add_le_add le_rfl (le_add_of_nonneg_right (by positivity))
    _ = roundStart p cfg (r + 1) := (roundStart_succ p cfg r).symm
    _ ≤ roundStart p cfg cfg.iterations := roundStart_mono p cfg (Nat.succ_le_of_lt hr)
    _ = executionTime p cfg := rfl

lemma quiet_pipeline_complete (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (htime : executionTime p cfg ≤ c.time)
    (hquiet : event (system p.toParams g P) (algorithm p cfg T) c c.time = none) :
    (c.workers 0).iteration = cfg.iterations := by
  classical
  have htargets := quiet_targets_empty p cfg T g P D samples selected c hc hquiet
  by_contra hdone
  have hr : (c.workers 0).iteration < cfg.iterations := lt_of_le_of_ne hc.root_limit hdone
  obtain ⟨hcompute, hcomm, hwake⟩ := quiet_future p cfg T g P c hquiet
  have hall (i : Fin p.n) : i ∈ (c.workers 0).arrived := by
    obtain ⟨hle, hnear⟩ := hc.rounds i
    have hsame : (c.workers i.succ).iteration = (c.workers 0).iteration := by
      by_contra hne
      have hbehind : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration := by omega
      have hlink := hc.links 0 i.succ
      simp only [Fin.cases_zero, Fin.cases_succ, hr, hbehind, htargets, List.not_mem_nil] at hlink
      have hfuture := hcomm 0 i.succ _ _ hlink
      have hb : roundStart p cfg (c.workers 0).iteration ≤ executionTime p cfg :=
        roundStart_mono p cfg hc.root_limit
      exact (not_lt_of_ge (hb.trans htime)) hfuture
    rcases hc.control i with hinit | hworking | hwaiting
    · have ht := hwake i.succ
      rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at ht
      exact (lt_irrefl _ ht).elim
    · have hlink := hc.pending i
      simp only [hworking.2.2.1, ite_true] at hlink
      have hfuture := hcompute i _ _ hlink
      have hsample := computation_finish_le p cfg (c.workers 0).iteration
        ((c.workers i.succ).samples + 1) i (Nat.succ_le_of_lt hworking.2.1)
      push_cast at hsample
      have hlimit := unfinished_round_time p cfg (c.workers 0).iteration hr
      rw [hsame] at hfuture
      exfalso
      exact (not_lt_of_ge (hsample.trans ((le_add_of_nonneg_right (by positivity)).trans
        (hlimit.trans htime)))) hfuture
    · by_contra hnot
      have hlink := hc.links i.succ 0
      simp only [Fin.cases_succ, hsame, hwaiting.2.2.2, hnot, not_false_eq_true,
        and_self, ite_true] at hlink
      have hfuture := hcomm i.succ 0 _ _ hlink
      have hworker := computation_finish_le p cfg (c.workers 0).iteration cfg.batch i le_rfl
      have hlimit := unfinished_round_time p cfg (c.workers 0).iteration hr
      exact (not_lt_of_ge ((add_le_add hworker le_rfl).trans (hlimit.trans htime))) hfuture
  apply hc.arrived_incomplete
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact hall i

lemma terminal_pipeline_output (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c)
    (htime : c.time ≤ c.deadline) (hbudget : executionTime p cfg ≤ c.deadline)
    (hterminal : step (system p.toParams g P) (algorithm p cfg T) c = none) :
    (algorithm p cfg T).output (c.workers 0) = output p cfg D g samples selected := by
  obtain ⟨ht, hquiet⟩ := (DistributedExecution.step_terminal_iff
    (system p.toParams g P) (algorithm p cfg T) c htime).mp hterminal
  have hdone := quiet_pipeline_complete p cfg T g P D samples selected c hc
    (by simpa only [ht] using hbudget) hquiet
  exact completed_output p cfg T g P D samples selected c hc hdone

lemma query_worker_progress_or_idle (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (i : Fin p.n) (s : State p) (clock : ClockReading) :
    workerProgress p cfg i.succ s < workerProgress p cfg i.succ ((algorithm p cfg T).query i.succ s clock).2 ∨
      (algorithm p cfg T).query i.succ s clock = (.advance 0, s) := by
  classical
  simp only [algorithm, Fin.cases_succ]
  split_ifs with hready hcount hsent
  · left
    have hp : s.pending = false := by simpa using hready.2
    simp [workerProgress, hp]
  · left
    have hs : s.sent = false := by simpa using hsent
    simp [workerProgress, hs]
  · exact Or.inr rfl
  · exact Or.inr rfl

lemma receive_progress (p : Params) (cfg : Config)
    (i : Fin p.n) (s : State p) (bits : List Bool)
    (hcount : s.samples ≤ cfg.batch) (hp : s.pending = false) (hs : s.sent = true) :
    workerProgress p cfg i.succ s < workerProgress p cfg i.succ (receive p cfg s i bits) := by
  simp only [workerProgress, Fin.cases_succ, receive, hp, hs, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_add, Nat.mul_one]
  omega

lemma computed_progress (p : Params) (cfg : Config) (i : Fin p.n) (s : State p) (value : Point p) :
    workerProgress p cfg i.succ s < workerProgress p cfg i.succ
      { s with accumulator := s.accumulator + value, samples := s.samples + 1, pending := false } := by
  cases hp : s.pending <;> simp only [workerProgress, Fin.cases_succ, hp, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_add, Nat.mul_one] <;> omega

lemma accept_progress (p : Params) (cfg : Config) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hnot : i ∉ s.arrived) (hk : s.iteration < cfg.iterations) :
    workerProgress p cfg 0 s < workerProgress p cfg 0 (accept p cfg s i.succ bits) := by
  classical
  have hc : s.arrived.card ≤ p.n := by simpa using Finset.card_le_univ s.arrived
  have htargets := Nat.sub_le p.n s.targets.length
  unfold accept
  simp only [Fin.cases_succ, ite_eq_left (show i ∉ s.arrived ∧ s.iteration < cfg.iterations from ⟨hnot, hk⟩)]
  split_ifs <;> simp only [workerProgress, Fin.cases_zero, finish, Finset.card_empty,
    Finset.card_insert_of_notMem hnot, Nat.mul_add, Nat.mul_one] <;> omega

lemma event_progress_or_idle (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (v : Fin (p.n + 1)) (notification : Event (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams) (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams))
    (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((v, notification), oracle)) :
    workerProgress p cfg v (c.workers v) < workerProgress p cfg v
      ((algorithm p cfg T).query v ((algorithm p cfg T).update v (c.workers v)
        ((algorithm p cfg T).clock c.time) notification) ((algorithm p cfg T).clock c.time)).2 ∨
    (notification = .wake ∧ (algorithm p cfg T).query v (c.workers v) ((algorithm p cfg T).clock c.time) =
      (.advance 0,
        c.workers v)) := by
  classical
  cases notification with
  | wake =>
      induction v using Fin.cases with
      | zero =>
          cases ht : (c.workers 0).targets with
          | nil =>
              right
              exact ⟨rfl, by simp [algorithm, ht]⟩
          | cons i rest =>
              left
              have hlength : rest.length + 1 ≤ p.n := by
                simpa only [ht, List.length_cons, Fintype.card_fin] using hp.targets_nodup.length_le_card
              simp only [algorithm, Fin.cases_zero, ht, workerProgress, List.length_cons]
              omega
      | succ i =>
          rcases query_worker_progress_or_idle p cfg T i (c.workers i.succ) 0 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨rfl, h⟩
  | computed reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p.toParams g P)
        (algorithm p cfg T) c c.time v reply oracle he
      cases reply with
      | computed input value =>
          induction v using Fin.cases with
          | zero =>
              simp only [system, LongTails.Setups.StarNetwork.system,
                LongTails.Setups.StarNetwork.computation,
                Fin.cases_zero, reduceCtorEq] at ha
          | succ i =>
              left
              have h := (computed_progress p cfg i (c.workers i.succ) value).trans_le
                (query_progress p cfg T i.succ _ 0)
              simpa only [compute_update, show (algorithm p cfg T).clock c.time = 0 from rfl] using h
  | received reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p.toParams g P)
        (algorithm p cfg T) c c.time v reply oracle he
      cases reply with
      | received source bits =>
          have hm := (received_at_finish p cfg T g P c htimely source v bits oracle he).1
          induction source using Fin.cases with
          | zero =>
              induction v using Fin.cases with
              | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
              | succ i =>
                  left
                  obtain ⟨_, _, _, hcount, hpend, hsent, _⟩ :=
                    received_broadcast_facts p cfg T g P D samples selected c hp htimely i bits oracle he
                  have h := (receive_progress p cfg i (c.workers i.succ) bits hcount.le hpend hsent).trans_le
                    (query_progress p cfg T i.succ _ 0)
                  simpa only [worker_receive, show (algorithm p cfg T).clock c.time = 0 from rfl] using h
          | succ i =>
              induction v using Fin.cases with
              | zero =>
                  left
                  obtain ⟨hr, hs, hnot, _⟩ := received_worker_facts p cfg T g P D samples selected
                    c hp htimely i bits oracle he
                  have hk : (c.workers 0).iteration < cfg.iterations := by
                    rw [← hr]
                    exact (sent_worker p cfg T g P D samples selected c hp i hs).1
                  have h := (accept_progress p cfg (c.workers 0) i bits hnot hk).trans_le
                    (query_progress p cfg T 0 _ 0)
                  simpa only [root_receive, show (algorithm p cfg T).clock c.time = 0 from rfl] using h
              | succ j =>
                  simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                    ite_false, reduceCtorEq] at hm

def workerProgressBound (p : Params) (cfg : Config) (v : Fin (p.n + 1)) : ℕ :=
  Fin.cases ((3 * p.n + 1) * ((cfg.iterations : ℕ) + 1))
    (fun _ => (2 * cfg.batch + 2) * ((cfg.iterations : ℕ) + 1)) v

lemma worker_progress_le (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hc : Pipeline p cfg T g P D samples selected c) (v : Fin (p.n + 1)) :
    workerProgress p cfg v (c.workers v) ≤ workerProgressBound p cfg v := by
  classical
  induction v using Fin.cases with
  | zero =>
      have hcard : (c.workers 0).arrived.card ≤ p.n := by simpa using Finset.card_le_univ (c.workers 0).arrived
      have hm := Nat.mul_le_mul_left (3 * p.n + 1) hc.root_limit
      have ht := Nat.sub_le p.n (c.workers 0).targets.length
      simp only [workerProgress, workerProgressBound, Fin.cases_zero, Nat.mul_add, Nat.mul_one]
      omega
  | succ i =>
      have hk : (c.workers i.succ).iteration ≤ cfg.iterations := (hc.rounds i).1.trans hc.root_limit
      have hm := Nat.mul_le_mul_left (2 * cfg.batch + 2) hk
      have hcount := (hc.workers i).count
      have hpend : (c.workers i.succ).pending.toNat ≤ 1 := by cases (c.workers i.succ).pending <;> decide
      have hsent : (c.workers i.succ).sent.toNat ≤ 1 := by cases (c.workers i.succ).sent <;> decide
      simp only [workerProgress, workerProgressBound, Fin.cases_succ, Nat.mul_add, Nat.mul_one]
      omega

noncomputable def workerRank (p : Params) (cfg : Config) (T : Time) (v : Fin (p.n + 1))
    (s : State p) (wake : Time) : ℕ :=
  2 * (workerProgressBound p cfg v - workerProgress p cfg v s) + if wake ≤ T then 1 else 0

lemma workerRank_decrease (p : Params) (cfg : Config) (T : Time) (v : Fin (p.n + 1))
    (old next : State p) (oldWake newWake : Time)
    (hbound : workerProgress p cfg v next ≤ workerProgressBound p cfg v)
    (hprogress : workerProgress p cfg v old < workerProgress p cfg v next) :
    workerRank p cfg T v next newWake < workerRank p cfg T v old oldWake := by
  unfold workerRank
  split_ifs <;> omega

lemma event_rank_decrease (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ T) (v : Fin (p.n + 1))
    (notification : Event (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams) (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams)) (oracle : OracleState (system p.toParams g P))
    (he : event (system p.toParams g P) (algorithm p cfg T) c c.time = some ((v, notification), oracle))
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    (∑ j, workerRank p cfg c.deadline j (next.workers j) (next.wakeTime j)) <
      ∑ j, workerRank p cfg c.deadline j (c.workers j) (c.wakeTime j) := by
  classical
  generalize hquery : (algorithm p cfg T).query v ((algorithm p cfg T).update v (c.workers v)
    ((algorithm p cfg T).clock c.time) notification) ((algorithm p cfg T).clock c.time) = pair
  obtain ⟨action, state⟩ := pair
  obtain ⟨hworkers, hwakes⟩ := DistributedExecution.step_event_state (system p.toParams g P)
    (algorithm p cfg T) c next v notification oracle action state he hquery hstep
  have hstrict : workerRank p cfg c.deadline v (next.workers v) (next.wakeTime v) <
      workerRank p cfg c.deadline v (c.workers v) (c.wakeTime v) := by
    rcases event_progress_or_idle p cfg T g P D samples selected c hp htimely v notification oracle he with
      hprogress | ⟨hn, hidle⟩
    · have hbound := worker_progress_le p cfg T g P D samples selected next
        (step_pipeline p cfg T g P D samples selected c next hp htimely hstep) v
      simp only [hquery] at hprogress
      simp only [hworkers, Function.update_self] at hbound ⊢
      exact workerRank_decrease p cfg c.deadline v (c.workers v) state (c.wakeTime v)
        (next.wakeTime v) hbound hprogress
    · subst notification
      change (algorithm p cfg T).query v (c.workers v) ((algorithm p cfg T).clock c.time) = (action, state) at hquery
      rw [hidle] at hquery
      cases hquery
      have hw := (DistributedExecution.wake_event (system p.toParams g P) (algorithm p cfg T)
        c c.time v oracle he).2
      simp only [hworkers, hwakes, Function.update_self, workerRank]
      have hready : c.wakeTime v ≤ c.deadline := hw.trans htime
      have hafter : ¬ max c.time ((algorithm p cfg T).timer 0) ≤ c.deadline := by
        apply not_le.mpr
        exact (hbudget.trans_lt (lt_add_of_pos_right _ zero_lt_one)).trans_le (le_max_right _ _)
      simp only [ite_eq_left hready, ite_eq_right hafter, Nat.add_zero]
      exact Nat.lt_succ_self _
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = v
    · subst j; exact hstrict.le
    · simp only [hworkers, hwakes, Function.update_of_ne hj]
      exact le_rfl
  · exact ⟨v, Finset.mem_univ _, hstrict⟩

noncomputable def executionRank (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams))
    (c : ExecutionState (system p.toParams g P) (algorithm p cfg T)) : ℕ :=
  2 * (∑ v, workerRank p cfg c.deadline v (c.workers v) (c.wakeTime v)) +
    if c.time = c.deadline ∨ (event (system p.toParams g P) (algorithm p cfg T) c c.time).isSome then 0 else 1

lemma step_rank_decrease (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p) (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p.toParams g P) (algorithm p cfg T))
    (hp : Pipeline p cfg T g P D samples selected c) (htimely : Timely p cfg T g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ T)
    (hstep : step (system p.toParams g P) (algorithm p cfg T) c = some next) :
    executionRank p cfg T g P next < executionRank p cfg T g P c := by
  classical
  cases he : event (system p.toParams g P) (algorithm p cfg T) c c.time with
  | none =>
      have hdone : c.time ≠ c.deadline := by
        intro h
        have hn := (DistributedExecution.step_terminal_iff (system p.toParams g P) (algorithm p cfg T) c htime).mpr ⟨h, he⟩
        rw [hn] at hstep
        cases hstep
      simp only [step, ite_eq_right (not_lt.mpr htime), he, ite_eq_right hdone, Option.some.injEq] at hstep
      subst next
      have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
        (fun i x (samples : Samples p.toParams) k => g i x (samples i k)) P (algorithm p cfg T) c htime
      have hn := (DistributedExecution.nextTime_spec (event (system p.toParams g P) (algorithm p cfg T) c)
        c.time c.deadline hex).1.2.2
      have hready :
          (nextTime (event (system p.toParams g P) (algorithm p cfg T) c) c.time c.deadline = c.deadline ∨
          (event (system p.toParams g P) (algorithm p cfg T)
            { c with time := nextTime (event (system p.toParams g P) (algorithm p cfg T) c) c.time c.deadline }
            (nextTime (event (system p.toParams g P) (algorithm p cfg T) c) c.time c.deadline)).isSome) := hn
      simp only [executionRank, hready, ite_true, he, Option.isSome_none, Bool.false_eq_true,
        or_false, hdone, ite_false, Nat.add_zero]
      exact Nat.lt_succ_self _
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      have hr := event_rank_decrease p cfg T g P D samples selected c next hp htimely htime hbudget v notification oracle he hstep
      have hd := DistributedExecution.step_deadline (system p.toParams g P) (algorithm p cfg T) c next hstep
      unfold executionRank
      rw [hd]
      split_ifs <;> omega

lemma finiteEvents (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations) :
    FiniteEvents (system p.toParams g P) (algorithm p cfg T) T ((selected, D), samples) := by
  intro deadline hdeadline
  apply DistributedExecution.termination_of_rank (system p.toParams g P) (algorithm p cfg T)
    (fun c => Pipeline p cfg T g P D samples selected c ∧ Timely p cfg T g P c ∧
      c.time ≤ c.deadline ∧ c.deadline ≤ T)
    (executionRank p cfg T g P)
  · intro c next hc hs
    refine ⟨⟨step_pipeline p cfg T g P D samples selected c next hc.1 hc.2.1 hs,
      step_timely p cfg T g P c next hc.2.1 hs,
      DistributedExecution.step_time_le_deadline (system p.toParams g P) (algorithm p cfg T) c next hc.2.2.1 hs,
      by simpa only [DistributedExecution.step_deadline _ _ _ _ hs] using hc.2.2.2⟩, ?_⟩
    exact step_rank_decrease p cfg T g P D samples selected c next hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hs
  · exact ⟨initial_pipeline p cfg T g P D samples selected deadline,
      initial_timely p cfg T g P deadline ((selected, D), samples), by exact zero_le, hdeadline⟩

lemma execute_output (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p.toParams)) (D : Draws p)
    (samples : Samples p.toParams) (selected : Fin cfg.iterations)
    (hbudget : executionTime p cfg ≤ T) :
    execute (system p.toParams g P) (algorithm p cfg T) T (selected, D) samples =
      output p cfg D g samples selected := by
  have hfinite := finiteEvents p cfg T g P D samples selected
  obtain ⟨k, hk⟩ := hfinite T le_rfl
  rw [DistributedExecution.execute_eq_terminal (system p.toParams g P) (algorithm p cfg T)
    T ((selected, D), samples) k hk]
  apply terminal_pipeline_output p cfg T g P D samples selected _
    (run_pipeline p cfg T g P D samples selected T k)
  · exact DistributedExecution.run_time_le_deadline (system p.toParams g P) (algorithm p cfg T) _ k (by exact zero_le)
  · simpa only [DistributedExecution.run_deadline, DistributedTemplate.initial] using hbudget
  · exact hk

end LongTails.Proofs.DistributedNormalizedExecution
