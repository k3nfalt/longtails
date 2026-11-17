import LongTails.Proofs.DistributedBatchedSgd
import LongTails.Proofs.DistributedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedBatchedExecution

open DistributedTemplate
open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

variable {p : Params}

structure Points (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (s : State p) : Prop where
  point : s.point = trajectory p cfg g samples s.iteration
  index : s.outputIndex = selected.val
  selected_point : s.selected =
    if selected.val ≤ s.iteration then trajectory p cfg g samples selected.val else p.x0

structure WorkerData (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (i : Fin p.n) (s : State p)
    (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) (Samples p)) : Prop where
  points : Points cfg g samples selected s
  count : s.samples ≤ cfg.batch i
  accumulator : s.accumulator = ∑ j ∈ Finset.range s.samples,
    g i s.point (samples i (s.iteration * cfg.batch i + j))
  seed : oracle.seed = samples
  used : oracle.used = s.iteration * cfg.batch i + s.samples

structure RootData (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (s : State p) : Prop where
  points : Points cfg g samples selected s
  arrived : s.arrived ⊆ active p cfg
  accumulator : s.accumulator = ∑ i ∈ s.arrived, ((cfg.batch i : ℝ) / totalBatch p cfg) •
    decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point s.iteration samples i))

noncomputable def workerMessage (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (i : Fin p.n) : List Bool :=
  encode p cfg (trajectory p cfg g samples k)
    (batchMean p cfg g (trajectory p cfg g samples k) k samples i)

noncomputable def broadcastMessage (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) : List Bool :=
  encode p cfg (trajectory p cfg g samples k)
    (∑ i, ((cfg.batch i : ℝ) / totalBatch p cfg) •
      decode p cfg (trajectory p cfg g samples k) (workerMessage cfg g samples k i))

lemma decode_workerMessage_frame (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (i : Fin p.n) (x : Point p) :
    decode p cfg x (workerMessage cfg g samples k i ++ List.replicate clockBits false) =
      decode p cfg x (workerMessage cfg g samples k i) :=
  DistributedBatchedSgd.decode_append cfg x _ _ (DistributedBatchedSgd.encode_length cfg _ _)

lemma decode_broadcastMessage_frame (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (x : Point p) :
    decode p cfg x (broadcastMessage cfg g samples k ++ List.replicate clockBits false) =
      decode p cfg x (broadcastMessage cfg g samples k) :=
  DistributedBatchedSgd.decode_append cfg x _ _ (DistributedBatchedSgd.encode_length cfg _ _)

def WorkerControl (cfg : Config p) (i : Fin p.n) (time wake : Time) (s : State p) : Prop :=
  if cfg.batch i = 0 then s.iteration = 0 ∧ s.samples = 0 ∧ s.pending = false ∧ s.sent = false
  else
    (s.iteration = 0 ∧ s.samples = 0 ∧ s.pending = false ∧ s.sent = false ∧ time = 0 ∧ wake = 0) ∨
    (s.iteration < cfg.iterations ∧ s.samples < cfg.batch i ∧ s.pending = true ∧ s.sent = false) ∨
    (s.iteration < cfg.iterations ∧ s.samples = cfg.batch i ∧ s.pending = false ∧ s.sent = true) ∨
    (s.iteration = cfg.iterations ∧ s.samples = 0 ∧ s.pending = false ∧ s.sent = false)

structure BroadcastControl (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p)
    (c : ExecutionState (system p g P) (algorithm p cfg)) : Prop where
  message : (c.workers 0).outbox = if (c.workers 0).targets = [] then none else
    some (broadcastMessage cfg g samples ((c.workers 0).iteration - 1))
  nodup : (c.workers 0).targets.Nodup
  queued : ∀ i ∈ (c.workers 0).targets, i ∈ active p cfg ∧
    (c.workers i.succ).iteration + 1 = (c.workers 0).iteration
  ready : (c.workers 0).targets ≠ [] → c.wakeTime 0 ≤ c.time
  finish : (c.workers 0).targets ≠ [] →
    c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) =
      (c.workers 0).iteration * roundTime p cfg

structure Pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) : Prop where
  root : RootData cfg g samples selected (c.workers 0)
  workers : ∀ i, WorkerData cfg g samples selected i (c.workers i.succ) (c.oracle.computation i.succ)
  root_limit : (c.workers 0).iteration ≤ cfg.iterations
  outbox : BroadcastControl cfg g P samples c
  arrived_incomplete : (c.workers 0).arrived ≠ active p cfg
  rounds : ∀ i ∈ active p cfg, (c.workers i.succ).iteration ≤ (c.workers 0).iteration ∧
    (c.workers 0).iteration ≤ (c.workers i.succ).iteration + 1
  behind : ∀ i ∈ active p cfg, (c.workers i.succ).iteration < (c.workers 0).iteration →
    (c.workers i.succ).samples = cfg.batch i ∧ (c.workers i.succ).sent = true
  control : ∀ i, WorkerControl cfg i c.time (c.wakeTime i.succ) (c.workers i.succ)
  root_pending : (c.oracle.computation 0).pending = none
  pending : ∀ i, (c.oracle.computation i.succ).pending =
    if (c.workers i.succ).pending then
      some ((c.workers i.succ).iteration * roundTime p cfg + ((c.workers i.succ).samples + 1) * p.h i,
        (c.workers i.succ).point) else none
  arrived_current : ∀ i ∈ (c.workers 0).arrived,
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧ (c.workers i.succ).sent = true
  arrived_time : ∀ i ∈ (c.workers 0).arrived,
    (c.workers 0).iteration * roundTime p cfg + cfg.batch i * p.h i +
      (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) ≤ c.time
  links : ∀ source target, c.oracle.communication.messages source target =
    Fin.cases
      (Fin.cases none (fun i =>
        if i ∈ active p cfg ∧ (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧
            i ∉ (c.workers 0).targets then
          some ((c.workers 0).iteration * roundTime p cfg,
            broadcastMessage cfg g samples ((c.workers 0).iteration - 1) ++ List.replicate clockBits false) else none) target)
      (fun i =>
        if target = 0 ∧ i ∈ active p cfg ∧ (c.workers i.succ).iteration = (c.workers 0).iteration ∧
            (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived then
          some ((c.workers i.succ).iteration * roundTime p cfg + cfg.batch i * p.h i +
              (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)),
            workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false) else none) source

lemma broadcast_update_worker (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hb : BroadcastControl cfg g P samples c)
    (i : Fin p.n) (state : State p) (wake : Time) (oracle : OracleState (system p g P)) (turn : ℕ)
    (hiter : i ∈ (c.workers 0).targets → state.iteration = (c.workers i.succ).iteration) :
    BroadcastControl cfg g P samples
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ wake
        oracle := oracle
        turn := turn } := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  constructor
  · simpa only [Function.update_of_ne hz] using hb.message
  · simpa only [Function.update_of_ne hz] using hb.nodup
  · intro j hj
    simp only [Function.update_of_ne hz] at hj ⊢
    obtain ⟨hactive, hround⟩ := hb.queued j hj
    refine ⟨hactive, ?_⟩
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self, hiter hj] using hround
    · simpa only [Function.update_of_ne (fun h => he (Fin.succ_inj.mp h))] using hround
  · simpa only [Function.update_of_ne hz] using hb.ready
  · simpa only [Function.update_of_ne hz] using hb.finish

lemma quiet_targets_empty (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hb : BroadcastControl cfg g P samples c)
    (hquiet : event (system p g P) (algorithm p cfg) c c.time = none) :
    (c.workers 0).targets = [] := by
  by_contra h
  have he := (DistributedExecution.event_ready (system p g P) (algorithm p cfg) c c.time).mpr
    (Or.inr ⟨0, hb.ready h⟩)
  simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he

lemma initial_points (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (v : Fin (p.n + 1)) :
    Points cfg g samples selected ((algorithm p cfg).initial v selected) := by
  refine ⟨rfl, rfl, ?_⟩
  by_cases h : selected.val = 0
  · simp [algorithm, h, trajectory]
  · simp only [algorithm, Nat.le_zero, ite_eq_right h]

lemma initial_worker_data (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p)
    (selected : Fin cfg.iterations) (i : Fin p.n) :
    WorkerData cfg g samples selected i ((algorithm p cfg).initial i.succ selected)
      ((system p g P).computation.initial i.succ samples) := by
  refine ⟨initial_points cfg g samples selected i.succ, ?_, ?_, rfl, ?_⟩
  · exact Nat.zero_le _
  · simp [algorithm]
  · simp [algorithm, system, LongTails.Setups.StarNetwork.system, LongTails.Setups.StarNetwork.computation]

lemma initial_root_data (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) :
    RootData cfg g samples selected ((algorithm p cfg).initial 0 selected) := by
  refine ⟨initial_points cfg g samples selected 0, Finset.empty_subset _, ?_⟩
  simp [algorithm]

lemma initial_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p)
    (selected : Fin cfg.iterations) (T : Time) (hactive : (active p cfg).Nonempty) :
    Pipeline cfg g P samples selected
      (initial (system p g P) (algorithm p cfg) T (selected, samples)) := by
  refine {
    root := initial_root_data cfg g samples selected
    workers := fun i => initial_worker_data cfg g P samples selected i
    root_limit := Nat.zero_le _
    outbox := by constructor <;> simp [initial, algorithm]
    arrived_incomplete := ?_
    rounds := ?_
    behind := ?_
    control := ?_
    root_pending := rfl
    pending := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · simpa only [initial, algorithm] using hactive.ne_empty.symm
  · intro i _
    simp [initial, algorithm]
  · intro i _ hlt
    simp [initial, algorithm] at hlt
  · intro i
    simp [WorkerControl, initial, algorithm]
  · intro i
    simp [initial, algorithm, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
      LongTails.Setups.StarNetwork.computation]
  · intro i hi
    simp [initial, algorithm] at hi
  · intro i hi
    simp [initial, algorithm] at hi
  · intro source target
    refine Fin.cases ?_ (fun i => ?_) source
    · refine Fin.cases ?_ (fun i => ?_) target <;>
        simp [initial, algorithm, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
          LongTails.Setups.StarNetwork.communication]
    · simp [initial, algorithm, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
        LongTails.Setups.StarNetwork.communication]

lemma advance_points (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (s : State p)
    (hpoints : Points cfg g samples selected s) :
    Points cfg g samples selected (advance p s (estimate p cfg g s.point s.iteration samples)) := by
  refine ⟨?_, hpoints.index, ?_⟩
  · change s.point - (1 / p.L) • estimate p cfg g s.point s.iteration samples = _
    rw [hpoints.point]
    rfl
  · change (if s.iteration + 1 = s.outputIndex then
      s.point - (1 / p.L) • estimate p cfg g s.point s.iteration samples else s.selected) = _
    rw [hpoints.index, hpoints.point, hpoints.selected_point]
    change (if s.iteration + 1 = selected.val then trajectory p cfg g samples (s.iteration + 1)
      else if selected.val ≤ s.iteration then trajectory p cfg g samples selected.val else p.x0) =
      if selected.val ≤ s.iteration + 1 then trajectory p cfg g samples selected.val else p.x0
    by_cases he : s.iteration + 1 = selected.val
    · simp [he]
    · have hle : selected.val ≤ s.iteration + 1 ↔ selected.val ≤ s.iteration := by omega
      simp [he, hle]

lemma compute_worker_data (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (i : Fin p.n) (s : State p)
    (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) (Samples p))
    (hd : WorkerData cfg g samples selected i s oracle) (hcount : s.samples < cfg.batch i) :
    WorkerData cfg g samples selected i
      { s with
        accumulator := s.accumulator + g i s.point (oracle.seed i oracle.used)
        samples := s.samples + 1
        pending := false }
      { oracle with pending := none, used := oracle.used + 1 } := by
  refine ⟨⟨hd.points.point, hd.points.index, hd.points.selected_point⟩,
    Nat.succ_le_of_lt hcount, ?_, hd.seed, ?_⟩
  · change s.accumulator + g i s.point (oracle.seed i oracle.used) =
      ∑ j ∈ Finset.range (s.samples + 1), g i s.point (samples i (s.iteration * cfg.batch i + j))
    rw [Finset.sum_range_succ, ← hd.accumulator, hd.seed, hd.used]
  · change oracle.used + 1 = s.iteration * cfg.batch i + (s.samples + 1)
    rw [hd.used, Nat.add_assoc]

lemma advance_worker_data (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (i : Fin p.n) (s : State p)
    (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) (Samples p))
    (hd : WorkerData cfg g samples selected i s oracle) (hcount : s.samples = cfg.batch i) :
    WorkerData cfg g samples selected i
      (advance p s (estimate p cfg g s.point s.iteration samples)) oracle := by
  refine ⟨advance_points cfg g samples selected s hd.points, Nat.zero_le _, ?_, hd.seed, ?_⟩
  · simp [advance]
  · change oracle.used = (s.iteration + 1) * cfg.batch i + 0
    rw [hd.used, hcount]
    simp [Nat.add_mul]

lemma completed_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (s : State p)
    (hpoints : Points cfg g samples selected s) (hdone : cfg.iterations ≤ s.iteration) :
    (algorithm p cfg).output s = output p cfg g (selected, samples) := by
  have hi : selected.val ≤ s.iteration := selected.isLt.le.trans hdone
  exact hpoints.selected_point.trans (ite_eq_left hi)

def Timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg)) : Prop :=
  (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time ≤ finish) ∧
  (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
    c.time ≤ finish) ∧ ∀ v, c.time ≤ c.wakeTime v

lemma initial_timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (seed : (algorithm p cfg).Seed × (system p g P).Seed) :
    Timely cfg g P (initial (system p g P) (algorithm p cfg) T seed) := by
  simp [Timely, initial, system, LongTails.Setups.StarNetwork.system, Oracle.initial,
    LongTails.Setups.StarNetwork.computation, LongTails.Setups.StarNetwork.communication]

lemma jump_timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hc : c.time ≤ c.deadline) (htimely : Timely cfg g P c) :
    Timely cfg g P { c with time := nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline } := by
  let O := system p g P
  let A := algorithm p cfg
  have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p) k => g i x (samples i k)) P A c hc
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
      (fun i x (samples : Samples p) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) finish).mpr ⟨finish, input, hpending, le_rfl⟩
  · intro source target finish bits hpending
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline finish hex
      (hcomm source target finish bits hpending)
    apply (DistributedExecution.event_ready O A c finish).mpr
    apply Or.inl
    apply (DistributedExecution.oracle_ready O c.oracle finish).mpr
    apply Or.inr
    exact (DistributedExecution.communication_ready (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication finish).mpr ⟨source, target, finish, bits, hpending, le_rfl⟩
  · intro v
    apply DistributedExecution.nextTime_le_ready (event O A c) c.time c.deadline (c.wakeTime v) hex (hwake v)
    exact (DistributedExecution.event_ready O A c (c.wakeTime v)).mpr (Or.inr ⟨v, le_rfl⟩)

lemma event_timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg)) (htimely : Timely cfg g P c)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p cfg) c c.time = some ((v, notification), next)) :
    Timely cfg g P { c with oracle := next } := by
  classical
  rcases DistributedExecution.event_cases (system p g P) (algorithm p cfg)
    c c.time v notification next hevent with horacle | ⟨_, hnext, _⟩
  · rcases htimely with ⟨hcompute, hcomm, hwake⟩
    rcases DistributedExecution.oracle_answer_cases (system p g P) c.oracle next c.time v notification horacle with
      ⟨reply, state, _, ha, rfl⟩ | ⟨reply, state, _, ha, rfl⟩
    · refine ⟨?_, hcomm, hwake⟩
      intro i finish input hpending
      by_cases hv : i.succ = v
      · have hp : state.pending = some (finish, input) := by simpa [hv] using hpending
        rcases DistributedExecution.computation_answer_pending ⟨p.h, p.l, p.b⟩
          (fun i x (samples : Samples p) k => g i x (samples i k)) v
          (c.oracle.computation v) state c.time reply ha with hnone | hold
        · simp [hnone] at hp
        · apply hcompute i finish input
          simpa [hv, ← hold] using hp
      · apply hcompute i finish input
        simpa [hv] using hpending
    · refine ⟨hcompute, ?_, hwake⟩
      intro source target finish bits hpending
      rcases DistributedExecution.communication_answer_pending (Seed := Samples p) ⟨p.h, p.l, p.b⟩
        c.oracle.communication state c.time v reply ha source target with hnone | hold
      · simp [hnone] at hpending
      · exact hcomm source target finish bits (hold ▸ hpending)
  · simpa only [hnext] using htimely

lemma step_timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (htimely : Timely cfg g P c)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) : Timely cfg g P next := by
  classical
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate] at hstep
    have hc : c.time ≤ c.deadline := le_of_not_gt hlate
    cases he : event (system p g P) (algorithm p cfg) c c.time with
    | none =>
        rw [he] at hstep
        by_cases hdeadline : c.time = c.deadline
        · simp only [ite_eq_left hdeadline, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdeadline] at hstep
          have hn := Option.some.inj hstep
          subst next
          exact jump_timely cfg g P c hc htimely
    | some value =>
        rcases value with ⟨⟨v, notification⟩, oracle⟩
        have ho := event_timely cfg g P c htimely v notification oracle he
        rcases ho with ⟨hcompute, hcomm, hwake⟩
        rw [he] at hstep
        cases hq : (algorithm p cfg).query v
            ((algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) notification)
            ((algorithm p cfg).clock c.time) with
        | mk action state =>
            simp only [hq] at hstep
            cases action with
            | compute query =>
                have hn := Option.some.inj hstep
                subst next
                refine ⟨?_, hcomm, ?_⟩
                · intro i finish input hpending
                  by_cases hv : i.succ = v
                  · have hp : ((system p g P).computation.submit i.succ
                        (oracle.computation i.succ) c.time query).pending = some (finish, input) := by
                      simpa [← hv] using hpending
                    exact DistributedExecution.computation_submit_timely ⟨p.h, p.l, p.b⟩
                      (fun i x (samples : Samples p) k => g i x (samples i k)) i
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
                · exact DistributedExecution.communication_submit_timely (Seed := Samples p)
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

lemma run_timely (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (seed : (algorithm p cfg).Seed × (system p g P).Seed) (k : ℕ) :
    Timely cfg g P (run (system p g P) (algorithm p cfg) k
      (initial (system p g P) (algorithm p cfg) T seed)) := by
  have hrun : ∀ j (c : ExecutionState (system p g P) (algorithm p cfg)),
      Timely cfg g P c → Timely cfg g P (run (system p g P) (algorithm p cfg) j c) := by
    intro j
    induction j with
    | zero => intro c hc; exact hc
    | succ j ih =>
        intro c hc
        cases hs : step (system p g P) (algorithm p cfg) c with
        | none => simpa only [run, hs] using hc
        | some next =>
            simpa only [run, hs] using ih next (step_timely cfg g P c next hc hs)
  exact hrun k _ (initial_timely cfg g P T seed)

lemma computed_at_finish (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg)) (htimely : Timely cfg g P c)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.oracle.computation i.succ).pending = some (c.time, input) ∧
      value = g i input ((c.oracle.computation i.succ).seed i (c.oracle.computation i.succ).used) ∧
      next = { c.oracle with computation := (Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := none, used := (c.oracle.computation i.succ).used + 1 }) } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.computed_event (system p g P) (algorithm p cfg)
    c c.time i.succ (.computed input value) next hevent
  obtain ⟨finish, hp, ht, hv, hs⟩ := DistributedExecution.computation_completed_data ⟨p.h, p.l, p.b⟩
    (fun i x (samples : Samples p) k => g i x (samples i k)) i
    (c.oracle.computation i.succ) state c.time input value ha
  have hf : finish = c.time := le_antisymm ht (htimely.1 i finish input hp)
  subst finish
  exact ⟨hp, hv, by simpa only [hs] using hn⟩

lemma received_at_finish (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg)) (htimely : Timely cfg g P c)
    (source target : Fin (p.n + 1)) (bits : List Bool) (next : OracleState (system p g P))
    (hevent : event (system p g P) (algorithm p cfg) c c.time =
      some ((target, .received (.received source bits)), next)) :
    c.oracle.communication.messages source target = some (c.time, bits) ∧
      next = { c.oracle with communication := { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages source
          (Function.update (c.oracle.communication.messages source) target none)) } } := by
  obtain ⟨state, ha, hn⟩ := DistributedExecution.received_event (system p g P) (algorithm p cfg)
    c c.time target (.received source bits) next hevent
  obtain ⟨finish, hp, ht, hs⟩ := DistributedExecution.communication_received_data (Seed := Samples p)
    ⟨p.h, p.l, p.b⟩ c.oracle.communication state c.time source target bits ha
  have hf : finish = c.time := le_antisymm ht (htimely.2.1 source target finish bits hp)
  subst finish
  exact ⟨hp, by simpa only [hs] using hn⟩

lemma quiet_future (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hquiet : event (system p g P) (algorithm p cfg) c c.time = none) :
    (∀ (i : Fin p.n) finish input, (c.oracle.computation i.succ).pending = some (finish, input) → c.time < finish) ∧
    (∀ source target finish bits, c.oracle.communication.messages source target = some (finish, bits) →
      c.time < finish) ∧ ∀ v, c.time < c.wakeTime v := by
  have hnot : ¬ (event (system p g P) (algorithm p cfg) c c.time).isSome := by simp [hquiet]
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready] at hnot
  refine ⟨?_, ?_, ?_⟩
  · intro i finish input hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inl ⟨i.succ, ?_⟩)
    exact (DistributedExecution.computation_ready ⟨p.h, p.l, p.b⟩
      (fun i x (samples : Samples p) k => g i x (samples i k)) i
      (c.oracle.computation i.succ) c.time).mpr ⟨finish, input, hp, ht⟩
  · intro source target finish bits hp
    apply lt_of_not_ge
    intro ht
    apply hnot
    refine Or.inl (Or.inr ?_)
    exact (DistributedExecution.communication_ready (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time).mpr ⟨source, target, finish, bits, hp, ht⟩
  · intro v
    exact lt_of_not_ge (fun ht => hnot (Or.inr ⟨v, ht⟩))

lemma jump_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (hquiet : event (system p g P) (algorithm p cfg) c c.time = none) :
    Pipeline cfg g P samples selected
      { c with time := nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline } := by
  have htargets := quiet_targets_empty cfg g P samples c hp.outbox hquiet
  have hbc : BroadcastControl cfg g P samples
      { c with time := nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline } := by
    refine ⟨hp.outbox.message, hp.outbox.nodup, hp.outbox.queued, ?_, ?_⟩ <;> simp [htargets]
  refine ⟨hp.root, hp.workers, hp.root_limit, hbc, hp.arrived_incomplete, hp.rounds, hp.behind,
    ?_, hp.root_pending, hp.pending, hp.arrived_current, ?_, hp.links⟩
  · intro i
    by_cases hz : cfg.batch i = 0
    · simpa only [WorkerControl, hz, ite_true] using hp.control i
    · have hcontrol := hp.control i
      simp only [WorkerControl, ite_eq_right hz] at hcontrol ⊢
      rcases hcontrol with hinit | hworking | hwaiting | hfinished
      · have hw := (quiet_future cfg g P c hquiet).2.2 i.succ
        rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at hw
        exact (lt_irrefl _ hw).elim
      · exact Or.inr (Or.inl hworking)
      · exact Or.inr (Or.inr (Or.inl hwaiting))
      · exact Or.inr (Or.inr (Or.inr hfinished))
  · intro i hi
    exact (hp.arrived_time i hi).trans (DistributedExecution.nextTime_ge _ _ _)

lemma unfinished_round_time (cfg : Config p) (r : ℕ) (hr : r < cfg.iterations) :
    r * roundTime p cfg + computationTime p cfg + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) ≤ timeBudget p cfg := by
  have hround : computationTime p cfg + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) ≤ roundTime p cfg := by
    unfold roundTime
    rw [two_mul]
    exact add_le_add_right (le_add_of_nonneg_right zero_le) _
  calc
    _ = r * roundTime p cfg + (computationTime p cfg + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ))) := by ring
    _ ≤ r * roundTime p cfg + roundTime p cfg := add_le_add_right hround _
    _ = ((r + 1 : ℕ) : Time) * roundTime p cfg := by push_cast; ring
    _ ≤ (cfg.iterations : ℕ) * roundTime p cfg := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hr) zero_le
    _ ≤ timeBudget p cfg := le_add_of_nonneg_right zero_le

lemma quiet_pipeline_complete (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (htime : timeBudget p cfg ≤ c.time)
    (hquiet : event (system p g P) (algorithm p cfg) c c.time = none) :
    (c.workers 0).iteration = cfg.iterations := by
  classical
  have htargets := quiet_targets_empty cfg g P samples c hp.outbox hquiet
  by_contra hdone
  have hr : (c.workers 0).iteration < cfg.iterations := lt_of_le_of_ne hp.root_limit hdone
  obtain ⟨hcompute, hcomm, hwake⟩ := quiet_future cfg g P c hquiet
  have hall (i : Fin p.n) (hi : i ∈ active p cfg) : i ∈ (c.workers 0).arrived := by
    have hbatch : 0 < cfg.batch i := (Finset.mem_filter.mp hi).2
    obtain ⟨hle, hnear⟩ := hp.rounds i hi
    have hsame : (c.workers i.succ).iteration = (c.workers 0).iteration := by
      by_contra hne
      have hbehind : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration := by omega
      have hlink := hp.links 0 i.succ
      simp [hi, hbehind] at hlink
      simp only [htargets, List.not_mem_nil] at hlink
      have hfuture := hcomm 0 i.succ _ _ hlink
      have hb : (c.workers 0).iteration * roundTime p cfg ≤ timeBudget p cfg :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hp.root_limit) zero_le).trans
          (show (cfg.iterations : ℕ) * roundTime p cfg ≤ timeBudget p cfg from le_add_of_nonneg_right zero_le)
      exact (not_lt_of_ge (hb.trans htime)) hfuture
    have hcontrol := hp.control i
    simp only [WorkerControl, ite_eq_right (Nat.ne_of_gt hbatch)] at hcontrol
    rcases hcontrol with hinit | hworking | hwaiting | hfinished
    · have ht := hwake i.succ
      rw [hinit.2.2.2.2.1, hinit.2.2.2.2.2] at ht
      exact (lt_irrefl _ ht).elim
    · have hlink := hp.pending i
      simp only [hworking.2.2.1, ite_true] at hlink
      have hfuture := hcompute i _ _ hlink
      have hsample : ((c.workers i.succ).samples + 1 : ℕ) * p.h i ≤ computationTime p cfg :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hworking.2.1) zero_le).trans
          (DistributedBatchedSgd.worker_time_le_computationTime cfg i)
      have hlimit := unfinished_round_time cfg (c.workers 0).iteration hr
      rw [hsame] at hfuture
      push_cast at hsample
      exfalso
      exact (not_lt_of_ge ((add_le_add_right hsample _).trans
        ((le_add_of_nonneg_right zero_le).trans (hlimit.trans htime)) )) hfuture
    · by_contra hnot
      have hlink := hp.links i.succ 0
      simp [hi, hsame, hwaiting.2.2.2, hnot] at hlink
      have hfuture := hcomm i.succ 0 _ _ hlink
      have hworker := DistributedBatchedSgd.worker_time_le_computationTime cfg i
      have hlimit := unfinished_round_time cfg (c.workers 0).iteration hr
      push_cast at hlimit
      exact (not_lt_of_ge ((add_le_add_left (add_le_add_right hworker _) _).trans
        (hlimit.trans htime))) hfuture
    · have hk := hfinished.1
      omega
  exact hp.arrived_incomplete (Finset.Subset.antisymm hp.root.arrived hall)

lemma terminal_pipeline_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (htime : c.time ≤ c.deadline) (hbudget : timeBudget p cfg ≤ c.deadline)
    (hterminal : step (system p g P) (algorithm p cfg) c = none) :
    (algorithm p cfg).output (c.workers 0) = output p cfg g (selected, samples) := by
  obtain ⟨ht, hquiet⟩ := (DistributedExecution.step_terminal_iff (system p g P) (algorithm p cfg) c htime).mp hterminal
  have hdone := quiet_pipeline_complete cfg g P samples selected c hp (by simpa [ht] using hbudget) hquiet
  exact completed_output cfg g samples selected (c.workers 0) hp.root.points hdone.ge

lemma weighted_active_sum (cfg : Config p) (values : Fin p.n → Point p) :
    (∑ i ∈ active p cfg, ((cfg.batch i : ℝ) / totalBatch p cfg) • values i) =
      ∑ i, ((cfg.batch i : ℝ) / totalBatch p cfg) • values i := by
  classical
  simp only [active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < cfg.batch i
  · simp [hi]
  · have hz : cfg.batch i = 0 := by omega
    simp [hz]

lemma accept_last (cfg : Config p) (s : State p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p) (k : ℕ)
    (i : Fin p.n) (hi : i ∈ active p cfg)
    (harrived : s.arrived = (active p cfg).erase i)
    (hacc : s.accumulator = ∑ j ∈ s.arrived, ((cfg.batch j : ℝ) / totalBatch p cfg) •
      decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point k samples j))) :
    let aggregate := ∑ j, ((cfg.batch j : ℝ) / totalBatch p cfg) •
      decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point k samples j))
    accept p cfg s i.succ (encode p cfg s.point (batchMean p cfg g s.point k samples i)) =
      { advance p s (estimate p cfg g s.point k samples) with
        outbox := some (encode p cfg s.point aggregate), targets := (active p cfg).toList } := by
  classical
  intro aggregate
  have hnot : i ∉ s.arrived := by simp [harrived]
  have hinsert : insert i s.arrived = active p cfg := by rw [harrived, Finset.insert_erase hi]
  have hsum : s.accumulator + ((cfg.batch i : ℝ) / totalBatch p cfg) •
      decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point k samples i)) = aggregate := by
    rw [hacc]
    calc
      _ = ∑ j ∈ insert i s.arrived, ((cfg.batch j : ℝ) / totalBatch p cfg) •
          decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point k samples j)) := by
        rw [Finset.sum_insert hnot]
        exact add_comm _ _
      _ = aggregate := by rw [hinsert, weighted_active_sum]
  simp only [accept, Fin.cases_succ, hi, hnot, ite_true, hsum, hinsert]
  rfl

lemma accept_partial (cfg : Config p) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hi : i ∈ active p cfg) (hnot : i ∉ s.arrived)
    (hmore : insert i s.arrived ≠ active p cfg) :
    accept p cfg s i.succ bits =
      { s with accumulator := s.accumulator + ((cfg.batch i : ℝ) / totalBatch p cfg) •
          decode p cfg s.point bits, arrived := insert i s.arrived } := by
  simp [accept, hi, hnot, hmore]

lemma accept_root_data (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (selected : Fin cfg.iterations) (s : State p)
    (hd : RootData cfg g samples selected s) (i : Fin p.n)
    (hi : i ∈ active p cfg) (hnot : i ∉ s.arrived) :
    RootData cfg g samples selected
      (accept p cfg s i.succ (encode p cfg s.point (batchMean p cfg g s.point s.iteration samples i))) := by
  classical
  by_cases hcomplete : insert i s.arrived = active p cfg
  · have harrived : s.arrived = (active p cfg).erase i := by
      rw [← hcomplete, Finset.erase_insert hnot]
    rw [accept_last cfg s g samples s.iteration i hi harrived hd.accumulator]
    have hp := advance_points cfg g samples selected s hd.points
    refine ⟨⟨hp.point, hp.index, hp.selected_point⟩, Finset.empty_subset _, ?_⟩
    simp [advance]
  · rw [accept_partial cfg s i _ hi hnot hcomplete]
    refine ⟨⟨hd.points.point, hd.points.index, hd.points.selected_point⟩,
      Finset.insert_subset hi hd.arrived, ?_⟩
    change s.accumulator + ((cfg.batch i : ℝ) / totalBatch p cfg) •
      decode p cfg s.point (encode p cfg s.point (batchMean p cfg g s.point s.iteration samples i)) = _
    rw [Finset.sum_insert hnot, hd.accumulator]
    exact add_comm _ _

lemma worker_query_compute (cfg : Config p) (s : State p) (i : Fin p.n)
    (clock : ClockReading) (hi : 0 < cfg.batch i) (hk : s.iteration < cfg.iterations)
    (hpending : s.pending = false) (hsamples : s.samples < cfg.batch i) :
    (algorithm p cfg).query i.succ s clock =
      (.compute (.evaluate s.point), { s with pending := true }) := by
  simp [algorithm, hi, hk, hpending, hsamples]

lemma worker_query_send (cfg : Config p) (s : State p) (i : Fin p.n)
    (clock : ClockReading) (hi : 0 < cfg.batch i) (hk : s.iteration < cfg.iterations)
    (hpending : s.pending = false) (hsamples : cfg.batch i ≤ s.samples) (hsent : s.sent = false) :
    (algorithm p cfg).query i.succ s clock =
      (.communicate ⟨0, encode p cfg s.point ((cfg.batch i : ℝ)⁻¹ • s.accumulator)⟩,
        { s with sent := true }) := by
  simp [algorithm, hi, hk, hpending, not_lt.mpr hsamples, hsent]

lemma root_query_send (cfg : Config p) (s : State p) (clock : ClockReading) (bits : List Bool)
    (i : Fin p.n) (rest : List (Fin p.n)) (houtbox : s.outbox = some bits) (htargets : s.targets = i :: rest) :
    (algorithm p cfg).query 0 s clock =
      (.communicate (i.succ, bits),
        { s with outbox := if rest.isEmpty then none else some bits, targets := rest }) := by
  simp [algorithm, houtbox, htargets]

lemma worker_receive (cfg : Config p) (s : State p) (i : Fin p.n) (clock : ClockReading)
    (bits : List Bool) :
    (algorithm p cfg).update i.succ s clock (.received (.received 0 bits)) =
      advance p s (decode p cfg s.point bits) := by
  simp [algorithm, Fin.succ_ne_zero]

lemma compute_update (cfg : Config p) (s : State p) (v : Fin (p.n + 1))
    (clock : ClockReading) (input value : Point p) :
    (algorithm p cfg).update v s clock (.computed (.computed input value)) =
      { s with accumulator := s.accumulator + value, samples := s.samples + 1, pending := false } := rfl

lemma query_advance_state (cfg : Config p) (s next : State p) (v : Fin (p.n + 1))
    (clock : ClockReading) (target : ClockReading)
    (hquery : (algorithm p cfg).query v s clock = (.advance target, next)) :
    target = 0 ∧ next = { s with wakeAt := timeBudget p cfg + 1 } := by
  have hidle (he : (.advance 0,
        { s with wakeAt := timeBudget p cfg + 1 }) =
        (Action.advance (ComputeQuery := ComputeQuery p) (numWorkers := p.n + 1) target, next)) :
      target = 0 ∧ next = { s with wakeAt := timeBudget p cfg + 1 } := by
    have ht := Action.advance.inj (congrArg Prod.fst he)
    have hs := congrArg Prod.snd he
    exact ⟨ht.symm, by simpa only [ht] using hs.symm⟩
  induction v using Fin.cases with
  | zero =>
      cases ho : s.outbox with
      | none =>
          simpa only [ho] using hidle (by simpa [algorithm, ho] using hquery)
      | some bits =>
          cases ht : s.targets with
          | nil => simpa only [ho, ht] using hidle (by simpa [algorithm, ho, ht] using hquery)
          | cons i rest => simp [algorithm, ho, ht] at hquery
  | succ i =>
      by_cases ha : 0 < cfg.batch i ∧ s.iteration < cfg.iterations ∧ s.pending = false
      · by_cases hs : s.samples < cfg.batch i
        · simp [algorithm, ha, hs] at hquery
        · by_cases hsent : s.sent = false
          · simp [algorithm, ha, hs, hsent] at hquery
          · exact hidle (by simpa [algorithm, ha, hs, hsent] using hquery)
      · exact hidle (by simpa [algorithm, ha] using hquery)

lemma advance_target_after_budget (cfg : Config p) (s next : State p) (v : Fin (p.n + 1))
    (clock : ClockReading) (target : ClockReading)
    (_hquery : (algorithm p cfg).query v s clock = (.advance target, next)) :
    timeBudget p cfg < (algorithm p cfg).timer target := by
  exact lt_add_of_pos_right _ zero_lt_one

lemma idle_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (v : Fin (p.n + 1)) (clock : ClockReading) (target : ClockReading) (next : State p)
    (hq : (algorithm p cfg).query v (c.workers v) clock = (.advance target, next)) :
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers v next
        wakeTime := Function.update c.wakeTime v (max c.time ((algorithm p cfg).timer target))
        turn := v.val + 1 } := by
  classical
  obtain ⟨_, hstate⟩ := query_advance_state cfg (c.workers v) next v clock target hq
  have hbc : BroadcastControl cfg g P samples
      { c with
        workers := Function.update c.workers v next
        wakeTime := Function.update c.wakeTime v (max c.time ((algorithm p cfg).timer target))
        turn := v.val + 1 } := by
    induction v using Fin.cases with
    | zero =>
        have ht : (c.workers 0).targets = [] := by
          cases hl : (c.workers 0).targets with
          | nil => rfl
          | cons i rest =>
              have ho := hp.outbox.message
              simp only [hl, List.cons_ne_nil, ite_false] at ho
              simp [algorithm, ho, hl] at hq
        constructor <;> simp [Function.update_self, hstate, ht, hp.outbox.message]
    | succ i =>
        exact broadcast_update_worker cfg g P samples c hp.outbox i next _ c.oracle _
          (fun _ => by rw [hstate])
  have hw : Function.update c.workers v next =
      fun w => { c.workers w with wakeAt := if w = v then timeBudget p cfg + 1 else (c.workers w).wakeAt } := by
    funext w
    by_cases he : w = v
    · simp [he, hstate]
    · simp only [Function.update_of_ne he, ite_eq_right he]
      rfl
  rw [hw] at hbc ⊢
  refine ⟨⟨⟨hp.root.points.point, hp.root.points.index, hp.root.points.selected_point⟩,
      hp.root.arrived, hp.root.accumulator⟩,
    (fun i => ⟨⟨(hp.workers i).points.point, (hp.workers i).points.index,
      (hp.workers i).points.selected_point⟩, (hp.workers i).count, (hp.workers i).accumulator,
      (hp.workers i).seed, (hp.workers i).used⟩),
    hp.root_limit, hbc, hp.arrived_incomplete, hp.rounds, hp.behind, ?_, hp.root_pending,
    hp.pending, hp.arrived_current, hp.arrived_time, hp.links⟩
  intro i
  by_cases hz : cfg.batch i = 0
  · simpa only [WorkerControl, ite_eq_left hz] using hp.control i
  · have hcontrol := hp.control i
    simp only [WorkerControl, ite_eq_right hz] at hcontrol ⊢
    by_cases hv : i.succ = v
    · rcases hcontrol with hinit | hworking | hwaiting | hfinished
      · have hb : 0 < cfg.batch i := Nat.pos_of_ne_zero hz
        have hk : (c.workers i.succ).iteration < cfg.iterations := by
          rw [hinit.1]
          exact cfg.iterations.pos
        have hj : (c.workers i.succ).samples < cfg.batch i := by rwa [hinit.2.1]
        have hcompute := worker_query_compute cfg (c.workers i.succ) i clock hb hk hinit.2.2.1 hj
        have hq' : (algorithm p cfg).query i.succ (c.workers i.succ) clock = (.advance target, next) := by
          simpa only [hv] using hq
        rw [hcompute] at hq'
        cases congrArg Prod.fst hq'
      · exact Or.inr (Or.inl hworking)
      · exact Or.inr (Or.inr (Or.inl hwaiting))
      · exact Or.inr (Or.inr (Or.inr hfinished))
    · simpa only [Function.update_of_ne hv] using hcontrol

lemma wake_idle_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p g P)) (target : ClockReading) (state : State p)
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((v, .wake), oracle))
    (hq : (algorithm p cfg).query v (c.workers v) ((algorithm p cfg).clock c.time) = (.advance target, state))
    (hs : step (system p g P) (algorithm p cfg) c = some next) : Pipeline cfg g P samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p g P) (algorithm p cfg) c c.time v oracle he).1
  subst oracle
  have hup : (algorithm p cfg).update v (c.workers v) ((algorithm p cfg).clock c.time) .wake = c.workers v := rfl
  unfold step at hs
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hs
  · simp only [ite_eq_right hlate, he, hup, hq, Function.update_idem, Option.some.injEq] at hs
    subst next
    exact idle_pipeline cfg g P samples selected c hp v ((algorithm p cfg).clock c.time) target state hq

lemma start_worker_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hi : 0 < cfg.batch i)
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0) :
    Pipeline cfg g P samples selected
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
    have he : c.time = c.wakeTime i.succ := hinit.2.2.2.2.1.trans hinit.2.2.2.2.2.symm
    rw [he, Function.update_eq_self]
  rw [hw, ho, hwake]
  refine ⟨⟨⟨hp.root.points.point, hp.root.points.index, hp.root.points.selected_point⟩,
      hp.root.arrived, hp.root.accumulator⟩,
    (fun j => ⟨⟨(hp.workers j).points.point, (hp.workers j).points.index,
      (hp.workers j).points.selected_point⟩, (hp.workers j).count, (hp.workers j).accumulator,
      (hp.workers j).seed, (hp.workers j).used⟩),
    hp.root_limit, (by exact ⟨hp.outbox.message, hp.outbox.nodup, hp.outbox.queued, hp.outbox.ready, hp.outbox.finish⟩), hp.arrived_incomplete, hp.rounds, hp.behind, ?_, ?_, ?_,
    hp.arrived_current, hp.arrived_time, hp.links⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [WorkerControl, ite_eq_right (Nat.ne_of_gt hi), ite_true]
      apply Or.inr
      apply Or.inl
      refine ⟨?_, ?_, trivial, hinit.2.2.2.1⟩
      · simpa only [hinit.1] using cfg.iterations.pos
      · simpa only [hinit.2.1] using hi
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [WorkerControl, ite_eq_right hs] using hp.control j
  · have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simpa only [ite_eq_right hz] using hp.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [hinit.1, hinit.2.1, hinit.2.2.2.2.1]
    · have hs : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
      simpa only [ite_eq_right hs] using hp.pending j

lemma pending_worker (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hpending : (c.workers i.succ).pending = true) :
    0 < cfg.batch i ∧ (c.workers i.succ).iteration < cfg.iterations ∧
      (c.workers i.succ).samples < cfg.batch i ∧ (c.workers i.succ).sent = false ∧
      (c.workers i.succ).iteration = (c.workers 0).iteration := by
  have hc := hp.control i
  by_cases hz : cfg.batch i = 0
  · simp [WorkerControl, hz, hpending] at hc
  · have hb := Nat.pos_of_ne_zero hz
    simp only [WorkerControl, ite_eq_right hz, hpending, Bool.true_eq_false, false_and,
      and_false, false_or, true_and, or_false] at hc
    obtain ⟨hk, hj, hs⟩ := hc
    refine ⟨hb, hk, hj, hs, ?_⟩
    have hi : i ∈ active p cfg := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hb⟩
    have hle := (hp.rounds i hi).1
    by_contra hne
    have hbehind := (hp.behind i hi (lt_of_le_of_ne hle hne)).2
    rw [hs] at hbehind
    cases hbehind

lemma computed_worker_facts (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (htimely : Timely cfg g P c) (i : Fin p.n) (input value : Point p)
    (next : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.workers i.succ).pending = true ∧ input = (c.workers i.succ).point ∧
      c.time = (c.workers i.succ).iteration * roundTime p cfg +
        ((c.workers i.succ).samples + 1) * p.h i ∧
      value = g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch i + (c.workers i.succ).samples)) := by
  obtain ⟨hready, hv, _⟩ := computed_at_finish cfg g P c htimely i input value next he
  rw [hp.pending i] at hready
  cases hb : (c.workers i.succ).pending with
  | false => simp [hb] at hready
  | true =>
      simp only [hb, ite_true, Option.some.injEq, Prod.mk.injEq] at hready
      obtain ⟨ht, hx⟩ := hready
      refine ⟨rfl, hx.symm, ht.symm, ?_⟩
      rw [← hx, (hp.workers i).seed, (hp.workers i).used] at hv
      exact hv

lemma continue_worker_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hpending : (c.workers i.succ).pending = true)
    (hmore : (c.workers i.succ).samples + 1 < cfg.batch i)
    (htime : c.time = (c.workers i.succ).iteration * roundTime p cfg +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch i + (c.workers i.succ).samples))
      samples := (c.workers i.succ).samples + 1 }
    let localState := { c.oracle.computation i.succ with
      pending := some (c.time + p.h i, (c.workers i.succ).point)
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with computation := Function.update c.oracle.computation i.succ localState } } := by
  classical
  dsimp only
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hb, hk, hj, hs, hr⟩ := pending_worker cfg g P samples selected c hp i hpending
  constructor
  · simpa only [Function.update_of_ne hz] using hp.root
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      refine ⟨⟨(hp.workers i).points.point, (hp.workers i).points.index,
        (hp.workers i).points.selected_point⟩, hmore.le, ?_, (hp.workers i).seed, ?_⟩
      · dsimp only
        rw [Finset.sum_range_succ, ← (hp.workers i).accumulator]
      · dsimp only
        rw [(hp.workers i).used, Nat.add_assoc]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.workers j
  · simpa only [Function.update_of_ne hz] using hp.root_limit
  · apply broadcast_update_worker cfg g P samples c hp.outbox i
    intro _
    rfl
  · simpa only [Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j hactive
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne hz] using hp.rounds i hactive
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.rounds j hactive
  · intro j hactive hbehind
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz] at hbehind
      exact (lt_irrefl _ (hr ▸ hbehind)).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [Function.update_of_ne hne, Function.update_of_ne hz] at hbehind ⊢
      exact hp.behind j hactive hbehind
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, WorkerControl, ite_eq_right (Nat.ne_of_gt hb)]
      exact Or.inr (Or.inl ⟨hk, hmore, hpending, hs⟩)
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.control j
  · simpa only [Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, hpending, ite_true]
      congr 2
      rw [htime]
      push_cast
      ring
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.pending j
  · intro j hmem
    simp only [Function.update_of_ne hz] at hmem
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne hz] using hp.arrived_current i hmem
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.arrived_current j hmem
  · simpa only [Function.update_of_ne hz] using hp.arrived_time
  · intro source target
    simp only [Function.update_of_ne hz]
    rw [hp.links source target]
    induction source using Fin.cases with
    | zero =>
        induction target using Fin.cases with
        | zero => rfl
        | succ j =>
            by_cases he : j = i
            · subst j; simp only [Fin.cases_zero, Fin.cases_succ, Function.update_self]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne hne]
    | succ j =>
        by_cases he : j = i
        · subst j; simp only [Fin.cases_succ, Function.update_self]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simp only [Fin.cases_succ, Function.update_of_ne hne]

lemma finish_worker_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hpending : (c.workers i.succ).pending = true)
    (hlast : (c.workers i.succ).samples + 1 = cfg.batch i)
    (htime : c.time = (c.workers i.succ).iteration * roundTime p cfg +
      ((c.workers i.succ).samples + 1) * p.h i) :
    let state := { c.workers i.succ with
      accumulator := (c.workers i.succ).accumulator + g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch i + (c.workers i.succ).samples))
      samples := (c.workers i.succ).samples + 1
      pending := false
      sent := true }
    let localState := { c.oracle.computation i.succ with
      pending := none
      used := (c.oracle.computation i.succ).used + 1 }
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers i.succ state
        wakeTime := Function.update c.wakeTime i.succ c.time
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := Function.update c.oracle.computation i.succ localState
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages i.succ
              (Function.update (c.oracle.communication.messages i.succ) 0
                (some (c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)),
                  workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } } } := by
  classical
  dsimp only
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  obtain ⟨hb, hk, hj, hs, hr⟩ := pending_worker cfg g P samples selected c hp i hpending
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have hf := (hp.arrived_current i hm).2
    rw [hs] at hf
    cases hf
  have hi : i ∈ active p cfg := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hb⟩
  constructor
  · simpa only [Function.update_of_ne hz] using hp.root
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      refine ⟨⟨(hp.workers i).points.point, (hp.workers i).points.index,
        (hp.workers i).points.selected_point⟩, hlast.le, ?_, (hp.workers i).seed, ?_⟩
      · dsimp only
        rw [Finset.sum_range_succ, ← (hp.workers i).accumulator]
      · dsimp only
        rw [(hp.workers i).used, Nat.add_assoc]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.workers j
  · simpa only [Function.update_of_ne hz] using hp.root_limit
  · apply broadcast_update_worker cfg g P samples c hp.outbox i
    intro _
    rfl
  · simpa only [Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j hactive
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne hz] using hp.rounds i hactive
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.rounds j hactive
  · intro j hactive hbehind
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz] at hbehind
      exact (lt_irrefl _ (hr ▸ hbehind)).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [Function.update_of_ne hne, Function.update_of_ne hz] at hbehind ⊢
      exact hp.behind j hactive hbehind
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, WorkerControl, ite_eq_right (Nat.ne_of_gt hb)]
      exact Or.inr (Or.inr (Or.inl ⟨hk, hlast, trivial, trivial⟩))
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.control j
  · simpa only [Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Bool.false_eq_true, ite_false]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.pending j
  · intro j hmem
    simp only [Function.update_of_ne hz] at hmem
    by_cases he : j = i
    · subst j
      exact (hnot hmem).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.arrived_current j hmem
  · simpa only [Function.update_of_ne hz] using hp.arrived_time
  · intro source target
    simp only [Function.update_of_ne hz]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_of_ne hz]
        rw [hp.links 0 target]
        induction target using Fin.cases with
        | zero => rfl
        | succ j =>
            by_cases he : j = i
            · subst j; simp only [Fin.cases_zero, Fin.cases_succ, Function.update_self]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne hne]
    | succ j =>
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Fin.cases_succ]
          by_cases ht : target = 0
          · subst target
            simp only [Function.update_self, hi, hr, hnot, and_self, ite_true,
              not_false_eq_true]
            congr 2
            rw [htime]
            have hc : (((c.workers i.succ).samples : Time) + 1) = (cfg.batch i : Time) := by
              exact_mod_cast hlast
            rw [hc, hr]
          · rw [Function.update_of_ne ht, hp.links i.succ target]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          rw [Function.update_of_ne hne, hp.links j.succ target]
          simp only [Fin.cases_succ, Function.update_of_ne hne]

lemma computed_continue_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hmore : (c.workers i.succ).samples + 1 < cfg.batch i)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts cfg g P samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish cfg g P c htimely i input value oracle he
  obtain ⟨hb, hk, _, _, _⟩ := pending_worker cfg g P samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hb, hk, hmore, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system,
      LongTails.Setups.StarNetwork.computation, Function.update_self, Fin.cases_succ,
      Function.update_idem, Option.some.injEq] at hstep
    subst next
    have h := continue_worker_pipeline cfg g P samples selected c hp i hpending hmore ht
    simpa only [hpending] using h

lemma computed_finish_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (input value : Point p) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), oracle))
    (hlast : (c.workers i.succ).samples + 1 = cfg.batch i)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  obtain ⟨hpending, hx, ht, hv⟩ := computed_worker_facts cfg g P samples selected c hp htimely
    i input value oracle he
  obtain ⟨_, _, ho⟩ := computed_at_finish cfg g P c htimely i input value oracle he
  obtain ⟨hb, hk, _, hs, _⟩ := pending_worker cfg g P samples selected c hp i hpending
  subst input
  subst value
  subst oracle
  have hbits : encode p cfg (c.workers i.succ).point
      ((cfg.batch i : ℝ)⁻¹ • ((c.workers i.succ).accumulator + g i (c.workers i.succ).point
        (samples i ((c.workers i.succ).iteration * cfg.batch i + (c.workers i.succ).samples)))) =
      workerMessage cfg g samples (c.workers i.succ).iteration i := by
    simp only [workerMessage, ← (hp.workers i).points.point, batchMean]
    congr 2
    rw [show Finset.range (cfg.batch i) = Finset.range ((c.workers i.succ).samples + 1) by rw [hlast],
      Finset.sum_range_succ, ← (hp.workers i).accumulator]
  have hfree : c.oracle.communication.messages i.succ 0 = none := by
    rw [hp.links]
    simp only [Fin.cases_succ, hs, Bool.false_eq_true, false_and, and_false, ite_false]
  have hsubmit : (system p g P).communication.submit c.oracle.communication c.time i.succ
      ⟨0, workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ =
      { c.oracle.communication with messages :=
        (Function.update c.oracle.communication.messages i.succ
          (Function.update (c.oracle.communication.messages i.succ) 0
            (some (c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)),
              workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } := by
    change (LongTails.Setups.StarNetwork.communication (Seed := Samples p) ⟨p.h, p.l, p.b⟩).submit
      c.oracle.communication c.time i.succ
      ⟨0, workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false⟩ = _
    rw [DistributedExecution.communication_submit_free (Seed := Samples p) ⟨p.h, p.l, p.b⟩
      c.oracle.communication c.time i.succ 0
      (workerMessage cfg g samples (c.workers i.succ).iteration i ++ List.replicate clockBits false)
      (Or.inr ⟨Fin.succ_ne_zero i, rfl⟩) hfree]
    simp only [List.length_append, List.length_replicate, workerMessage, DistributedBatchedSgd.encode_length]
    congr 1
    funext source target
    by_cases hv : source = i.succ
    · subst source
      simp only [Function.update_self, Function.update_apply]
      (split_ifs; congr 2) <;> ring
    · simp only [Function.update_of_ne hv]
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, compute_update] at hstep
    simp only [algorithm, Fin.cases_succ, hb, hk, not_lt.mpr hlast.ge, hs, Bool.not_false,
      and_self, ite_true, ite_false, hbits] at hstep
    rw [hsubmit] at hstep
    simp only [Option.some.injEq] at hstep
    subst next
    exact finish_worker_pipeline cfg g P samples selected c hp i hpending hlast ht

lemma received_worker_facts (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), oracle)) :
    i ∈ active p cfg ∧ (c.workers i.succ).iteration = (c.workers 0).iteration ∧
      (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived ∧
      c.time = (c.workers 0).iteration * roundTime p cfg + cfg.batch i * p.h i +
        (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) ∧
      bits = workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish cfg g P c htimely i.succ 0 bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_succ, true_and] at hm
  split_ifs at hm with hvalid
  · obtain ⟨hi, hr, hs, hnot⟩ := hvalid
    have heq := Option.some.inj hm
    obtain ⟨ht, hb⟩ := Prod.mk.inj heq
    exact ⟨hi, hr, hs, hnot, by simpa only [hr] using ht.symm,
      by simpa only [hr] using hb.symm⟩

lemma broadcast_send_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (rest : List (Fin p.n)) (htargets : (c.workers 0).targets = i :: rest) :
    let bits := broadcastMessage cfg g samples ((c.workers 0).iteration - 1)
    let state := { c.workers 0 with outbox := if rest.isEmpty then none else some bits, targets := rest }
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers 0 state
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)),
                bits ++ List.replicate clockBits false)))) } } } := by
  classical
  dsimp only
  have hn : (c.workers 0).targets ≠ [] := by simp [htargets]
  have hnodup : (i :: rest).Nodup := htargets ▸ hp.outbox.nodup
  have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
  obtain ⟨hi, hr⟩ := hp.outbox.queued i (by simp [htargets])
  have hf := hp.outbox.finish hn
  constructor
  · exact ⟨⟨hp.root.points.point, hp.root.points.index, hp.root.points.selected_point⟩,
      hp.root.arrived, hp.root.accumulator⟩
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simpa only [Function.update_self] using hp.root_limit
  · constructor
    · simp only [Function.update_self, List.isEmpty_iff]
    · simpa only [Function.update_self] using (List.nodup_cons.mp hnodup).2
    · intro j hj
      simp only [Function.update_self] at hj
      simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using
        hp.outbox.queued j (by simp only [htargets, List.mem_cons]; exact Or.inr hj)
    · intro _; simp only [Function.update_self]; exact le_rfl
    · intro _; simpa only [Function.update_self] using hf
  · simpa only [Function.update_self] using hp.arrived_incomplete
  · intro j hj
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.rounds j hj
  · intro j hj
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.behind j hj
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · intro j hj
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.arrived_current j hj
  · simpa only [Function.update_self] using hp.arrived_time
  · intro source target
    simp only [Function.update_self]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero =>
            rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, hp.links]
            rfl
        | succ j =>
            simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
            by_cases he : j = i
            · subst j
              simp only [Function.update_self, hi, hr, hnot, not_false_eq_true, and_self, ite_true, hf]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hp.links]
              simp only [Fin.cases_zero, Fin.cases_succ, htargets, List.mem_cons, he, false_or]
    | succ j =>
        rw [Function.update_of_ne (Fin.succ_ne_zero j), hp.links]
        simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]

lemma root_query_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c) :
    match (algorithm p cfg).query 0 (c.workers 0) 0 with
    | (.compute _, _) => False
    | (.communicate (target, bits), state) =>
        Pipeline cfg g P samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 c.time
            turn := 1
            oracle := { c.oracle with communication := ((system p g P).communication.submit
              c.oracle.communication c.time 0 (target, bits ++ List.replicate clockBits false)) } }
    | (.advance target, state) =>
        Pipeline cfg g P samples selected
          { c with
            workers := Function.update c.workers 0 state
            wakeTime := Function.update c.wakeTime 0 (max c.time ((algorithm p cfg).timer target))
            turn := 1 } := by
  classical
  cases ht : (c.workers 0).targets with
  | nil =>
      have ho : (c.workers 0).outbox = none := by simpa only [ht, ite_true] using hp.outbox.message
      have hq : (algorithm p cfg).query 0 (c.workers 0) 0 =
          (.advance 0, { c.workers 0 with wakeAt := timeBudget p cfg + 1 }) := by simp [algorithm, ho]
      rw [hq]
      exact idle_pipeline cfg g P samples selected c hp 0 0 0 _ hq
  | cons i rest =>
      let bits := broadcastMessage cfg g samples ((c.workers 0).iteration - 1)
      have ho : (c.workers 0).outbox = some bits := by simpa only [ht, List.cons_ne_nil, ite_false] using hp.outbox.message
      rw [root_query_send cfg (c.workers 0) 0 bits i rest ho ht]
      dsimp only
      have hfree : c.oracle.communication.messages 0 i.succ = none := by
        simp only [hp.links, Fin.cases_zero, Fin.cases_succ, ht, List.mem_cons_self,
          not_true_eq_false, and_false, ite_false]
      have hsubmit : (system p g P).communication.submit c.oracle.communication c.time 0
          (i.succ, bits ++ List.replicate clockBits false) =
          { c.oracle.communication with messages := (Function.update c.oracle.communication.messages 0
            (Function.update (c.oracle.communication.messages 0) i.succ
              (some (c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)),
                bits ++ List.replicate clockBits false)))) } := by
        change (LongTails.Setups.StarNetwork.communication (Seed := Samples p) ⟨p.h, p.l, p.b⟩).submit
          c.oracle.communication c.time 0 (i.succ, bits ++ List.replicate clockBits false) = _
        rw [DistributedExecution.communication_submit_free (Seed := Samples p) ⟨p.h, p.l, p.b⟩
          c.oracle.communication c.time 0 i.succ (bits ++ List.replicate clockBits false)
          (Or.inl ⟨rfl, Fin.succ_ne_zero i⟩) hfree]
        have hlength : bits.length = p.d * cfg.width := DistributedBatchedSgd.encode_length cfg _ _
        simp only [List.length_append, List.length_replicate, hlength]
        congr 1
        funext source target
        by_cases hs : source = 0
        · subst source
          simp only [Function.update_self, Function.update_apply]
          (split_ifs; congr 2) <;> ring
        · simp only [Function.update_of_ne hs]
      rw [hsubmit]
      exact broadcast_send_pipeline cfg g P samples selected c hp i rest ht

lemma root_event_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (notification : Event (ComputeReply p) (CommReply p)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((0, notification), oracle))
    (hp : Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers 0 ((algorithm p cfg).update 0 (c.workers 0) 0 notification)
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := oracle })
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  have h := root_query_pipeline cfg g P samples selected _ hp
  simp only [Function.update_self, Function.update_idem] at h
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    have hclock : (algorithm p cfg).clock c.time = 0 := rfl
    rw [hclock] at hstep
    cases hq : (algorithm p cfg).query 0 ((algorithm p cfg).update 0 (c.workers 0) 0 notification) 0 with
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

lemma root_ready_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c) :
    Pipeline cfg g P samples selected { c with wakeTime := Function.update c.wakeTime 0 c.time, turn := 1 } := by
  refine ⟨hp.root, hp.workers, hp.root_limit, ?_, hp.arrived_incomplete, hp.rounds, hp.behind,
    ?_, hp.root_pending, hp.pending, hp.arrived_current, hp.arrived_time, hp.links⟩
  · exact ⟨hp.outbox.message, hp.outbox.nodup, hp.outbox.queued,
      fun _ => by simp only [Function.update_self]; exact le_rfl, hp.outbox.finish⟩
  · intro i
    simpa only [Function.update_of_ne (Fin.succ_ne_zero i)] using hp.control i

lemma root_partial_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (i : Fin p.n)
    (hi : i ∈ active p cfg) (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hpartial : insert i (c.workers 0).arrived ≠ active p cfg)
    (htime : c.time = (c.workers 0).iteration * roundTime p cfg + cfg.batch i * p.h i +
      (p.l + p.b * (p.d * cfg.width + clockBits : ℕ))) (wake : Time) :
    let state := { c.workers 0 with
      accumulator := (c.workers 0).accumulator + ((cfg.batch i : ℝ) / totalBatch p cfg) •
        decode p cfg (c.workers 0).point (workerMessage cfg g samples (c.workers 0).iteration i)
      arrived := insert i (c.workers 0).arrived
      wakeAt := wake }
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers 0 state
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (Function.update c.oracle.communication.messages i.succ
            (Function.update (c.oracle.communication.messages i.succ) 0 none)) } } } := by
  classical
  dsimp only
  constructor
  · simp only [Function.update_self]
    refine ⟨⟨hp.root.points.point, hp.root.points.index, hp.root.points.selected_point⟩,
      Finset.insert_subset hi hp.root.arrived, ?_⟩
    dsimp only
    rw [Finset.sum_insert hnot, hp.root.accumulator]
    simp only [workerMessage, ← hp.root.points.point]
    rw [add_comm]
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simpa only [Function.update_self] using hp.root_limit
  · constructor
    · simpa only [Function.update_self] using hp.outbox.message
    · simpa only [Function.update_self] using hp.outbox.nodup
    · intro j hj
      simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.outbox.queued j hj
    · intro _; simp only [Function.update_self]; exact le_rfl
    · simpa only [Function.update_self] using hp.outbox.finish
  · simpa only [Function.update_self] using hpartial
  · intro j hj
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.rounds j hj
  · intro j hj
    simpa only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.behind j hj
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · intro j hj
    simp only [Function.update_self, Finset.mem_insert] at hj
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)]
    rcases hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hp.arrived_current j hj
  · intro j hj
    simp only [Function.update_self, Finset.mem_insert] at hj
    simp only [Function.update_self]
    rcases hj with rfl | hj
    · exact htime.ge
    · exact hp.arrived_time j hj
  · intro source target
    simp only [Function.update_self]
    induction source using Fin.cases with
    | zero =>
        rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, hp.links]
        induction target using Fin.cases with
        | zero => rfl
        | succ j => simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
    | succ j =>
        simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j)]
        by_cases he : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, not_true_eq_false,
            and_false, ite_false]
          by_cases ht : target = 0
          · subst target; simp only [Function.update_self]
          · rw [Function.update_of_ne ht, hp.links]
            simp only [Fin.cases_succ, ht, false_and, ite_false]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          rw [Function.update_of_ne hne, hp.links]
          simp only [Fin.cases_succ, Finset.mem_insert, he, false_or]

lemma received_partial_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hpartial : insert i (c.workers 0).arrived ≠ active p cfg)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  obtain ⟨hi, hr, hs, hnot, ht, hbits⟩ := received_worker_facts cfg g P samples selected c hp htimely
    i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish cfg g P c htimely i.succ 0 bits oracle he
  subst bits
  apply root_event_pipeline cfg g P samples selected c next (.received (.received i.succ
    (workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false))) oracle he _ hstep
  have hu : (algorithm p cfg).update 0 (c.workers 0) 0 (.received (.received i.succ
      (workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false))) =
      { c.workers 0 with
        accumulator := (c.workers 0).accumulator + ((cfg.batch i : ℝ) / totalBatch p cfg) •
          decode p cfg (c.workers 0).point (workerMessage cfg g samples (c.workers 0).iteration i)
        arrived := insert i (c.workers 0).arrived } := by
    simp only [algorithm, ite_true, accept_partial cfg _ i _ hi hnot hpartial, decode_workerMessage_frame]
  rw [hu, ho]
  exact root_partial_pipeline cfg g P samples selected c hp i hi hr hs hnot hpartial ht (c.workers 0).wakeAt

lemma last_arrival_time (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (i : Fin p.n)
    (hcomplete : insert i (c.workers 0).arrived = active p cfg)
    (htime : c.time = (c.workers 0).iteration * roundTime p cfg + cfg.batch i * p.h i +
      (p.l + p.b * (p.d * cfg.width + clockBits : ℕ))) :
    c.time = (c.workers 0).iteration * roundTime p cfg + computationTime p cfg +
      (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) := by
  have hmax : computationTime p cfg = cfg.batch i * p.h i := by
    apply le_antisymm _ (DistributedBatchedSgd.worker_time_le_computationTime cfg i)
    apply DistributedBatchedSgd.computationTime_le
    intro j
    by_cases hj : j ∈ active p cfg
    · rw [← hcomplete, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact le_rfl
      · have hbefore := hp.arrived_time j hj
        rw [htime] at hbefore
        exact le_of_add_le_add_left (le_of_add_le_add_right hbefore)
    · have hz : cfg.batch j = 0 := by
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
          Nat.le_zero] using hj
      simp only [hz, Nat.cast_zero, zero_mul]
      exact zero_le
  rw [hmax]
  exact htime

lemma sent_worker (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hsent : (c.workers i.succ).sent = true) :
    (c.workers i.succ).iteration < cfg.iterations ∧ (c.workers i.succ).samples = cfg.batch i ∧
      (c.workers i.succ).pending = false := by
  have hc := hp.control i
  by_cases hz : cfg.batch i = 0
  · simp [WorkerControl, hz, hsent] at hc
  · simpa only [WorkerControl, ite_eq_right hz, hsent, Bool.true_eq_false, false_and,
      and_false, false_or, true_and, or_false, and_true] using hc

lemma complete_workers (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (hcomplete : insert i (c.workers 0).arrived = active p cfg) :
    ∀ j ∈ active p cfg, (c.workers j.succ).iteration = (c.workers 0).iteration ∧
      (c.workers j.succ).samples = cfg.batch j ∧ (c.workers j.succ).pending = false ∧
      (c.workers j.succ).sent = true := by
  intro j hj
  have hstate : (c.workers j.succ).iteration = (c.workers 0).iteration ∧
      (c.workers j.succ).sent = true := by
    rw [← hcomplete, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ⟨hr, hs⟩
    · exact hp.arrived_current j hj
  obtain ⟨_, hjcount, hjpending⟩ := sent_worker cfg g P samples selected c hp j hstate.2
  exact ⟨hstate.1, hjcount, hjpending, hstate.2⟩

lemma root_complete_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (hactive : (active p cfg).Nonempty) (hk : (c.workers 0).iteration < cfg.iterations)
    (hall : ∀ j ∈ active p cfg, (c.workers j.succ).iteration = (c.workers 0).iteration ∧
      (c.workers j.succ).samples = cfg.batch j ∧ (c.workers j.succ).pending = false ∧
      (c.workers j.succ).sent = true)
    (hfinish : c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) =
      ((c.workers 0).iteration + 1) * roundTime p cfg) :
    let state := { advance p (c.workers 0)
      (estimate p cfg g (c.workers 0).point (c.workers 0).iteration samples) with
        outbox := some (broadcastMessage cfg g samples (c.workers 0).iteration)
        targets := (active p cfg).toList }
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers 0 state
        wakeTime := Function.update c.wakeTime 0 c.time
        turn := 1
        oracle := { c.oracle with communication := { c.oracle.communication with messages :=
          (fun _ _ => none) } } } := by
  classical
  dsimp only
  have hpoints := advance_points cfg g samples selected (c.workers 0) hp.root.points
  constructor
  · simp only [Function.update_self]
    refine ⟨⟨hpoints.point, hpoints.index, hpoints.selected_point⟩, Finset.empty_subset _, ?_⟩
    simp [advance]
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simp only [Function.update_self, advance]
    exact Nat.succ_le_of_lt hk
  · constructor
    · have hn : (active p cfg).toList ≠ [] := fun h => hactive.ne_empty (Finset.toList_eq_nil.mp h)
      simp only [Function.update_self, advance, hn, ite_false, Nat.add_sub_cancel]
    · simpa only [Function.update_self] using (active p cfg).nodup_toList
    · intro j hj
      simp only [Function.update_self, Finset.mem_toList] at hj
      simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), advance]
      exact ⟨hj, congrArg (· + 1) (hall j hj).1⟩
    · intro _; simp only [Function.update_self]; exact le_rfl
    · intro _; simpa only [Function.update_self, advance, Nat.cast_add, Nat.cast_one] using hfinish
  · simpa only [Function.update_self, advance] using hactive.ne_empty.symm
  · intro j hj
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j), advance]
    rw [(hall j hj).1]
    exact ⟨Nat.le_succ _, le_rfl⟩
  · intro j hj _
    simp only [Function.update_of_ne (Fin.succ_ne_zero j)]
    exact ⟨(hall j hj).2.1, (hall j hj).2.2.2⟩
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · intro j hj
    simp only [Function.update_self, advance, Finset.notMem_empty] at hj
  · intro j hj
    simp only [Function.update_self, advance, Finset.notMem_empty] at hj
  · intro source target
    simp only [Function.update_self, advance]
    induction source using Fin.cases with
    | zero =>
        simp only [Fin.cases_zero]
        induction target using Fin.cases with
        | zero => rfl
        | succ j =>
            simp only [Fin.cases_succ, Function.update_of_ne (Fin.succ_ne_zero j), Finset.mem_toList]
            by_cases hj : j ∈ active p cfg <;> simp only [hj, not_true_eq_false, false_and, and_false, ite_false]
    | succ j =>
        simp only [Fin.cases_succ,
          Function.update_of_ne (Fin.succ_ne_zero j)]
        by_cases hj : j ∈ active p cfg
        · have hn : (c.workers 0).iteration ≠ (c.workers 0).iteration + 1 := by omega
          simp only [hj, (hall j hj).1, hn, false_and, and_false, ite_false]
        · simp only [hj, false_and, and_false, ite_false]

lemma complete_messages (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hi : i ∈ active p cfg)
    (hr : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true) (hnot : i ∉ (c.workers 0).arrived)
    (hcomplete : insert i (c.workers 0).arrived = active p cfg)
    (htime : c.time = (c.workers 0).iteration * roundTime p cfg + cfg.batch i * p.h i +
      (p.l + p.b * (p.d * cfg.width + clockBits : ℕ))) :
    ∀ source target, c.oracle.communication.messages source target =
      if source = i.succ ∧ target = 0 then
        some (c.time, workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false) else none := by
  classical
  have hall := complete_workers cfg g P samples selected c hp i hr hs hcomplete
  intro source target
  rw [hp.links]
  induction source using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero, (Fin.succ_ne_zero i).symm, false_and, ite_false]
      induction target using Fin.cases with
      | zero => rfl
      | succ j =>
          simp only [Fin.cases_succ]
          by_cases hj : j ∈ active p cfg
          · have hn : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
            simp only [hj, (hall j hj).1, hn, false_and, and_false, ite_false]
          · simp only [hj, false_and, ite_false]
  | succ j =>
      simp only [Fin.cases_succ]
      by_cases he : j = i
      · subst j
        simp only [hi, hr, hs, hnot, not_false_eq_true, and_self, and_true, true_and, ← htime]
      · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
        simp only [hne, false_and, ite_false]
        by_cases hj : j ∈ active p cfg
        · have hmem : j ∈ (c.workers 0).arrived := by
            rw [← hcomplete, Finset.mem_insert] at hj
            exact hj.resolve_left he
          simp only [hmem, not_true_eq_false, and_false, ite_false]
        · simp only [hj, false_and, and_false, ite_false]

lemma received_complete_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), oracle))
    (hcomplete : insert i (c.workers 0).arrived = active p cfg)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  obtain ⟨hi, hr, hs, hnot, ht, hbits⟩ := received_worker_facts cfg g P samples selected c hp htimely
    i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish cfg g P c htimely i.succ 0 bits oracle he
  have hall := complete_workers cfg g P samples selected c hp i hr hs hcomplete
  have hk : (c.workers 0).iteration < cfg.iterations := by
    simpa only [hr] using (sent_worker cfg g P samples selected c hp i hs).1
  have hlast := last_arrival_time cfg g P samples selected c hp i hcomplete ht
  have hm := complete_messages cfg g P samples selected c hp i hi hr hs hnot hcomplete ht
  have harrived : (c.workers 0).arrived = (active p cfg).erase i := by
    rw [← hcomplete, Finset.erase_insert hnot]
  have haccept : accept p cfg (c.workers 0) i.succ
      (workerMessage cfg g samples (c.workers 0).iteration i) =
      { advance p (c.workers 0)
          (estimate p cfg g (c.workers 0).point (c.workers 0).iteration samples) with
        outbox := some (broadcastMessage cfg g samples (c.workers 0).iteration)
        targets := (active p cfg).toList } := by
    simpa only [workerMessage, broadcastMessage, ← hp.root.points.point] using
      accept_last cfg (c.workers 0) g samples (c.workers 0).iteration i hi harrived hp.root.accumulator
  let clean : LongTails.Setups.StarNetwork.CommunicationState p.n :=
    { c.oracle.communication with messages := (Function.update c.oracle.communication.messages i.succ
      (Function.update (c.oracle.communication.messages i.succ) 0 none)) }
  have hempty : ∀ source target, clean.messages source target = none := by
    intro source target
    dsimp only [clean]
    by_cases hv : source = i.succ
    · subst source
      simp only [Function.update_self]
      by_cases ht : target = 0
      · subst target; simp only [Function.update_self]
      · rw [Function.update_of_ne ht, hm]
        simp only [ht, and_false, ite_false]
    · rw [Function.update_of_ne hv, hm]
      simp only [hv, false_and, ite_false]
  have hfinish : c.time + (p.l + p.b * (p.d * cfg.width + clockBits : ℕ)) =
      ((c.workers 0).iteration + 1) * roundTime p cfg := by
    rw [hlast]
    unfold roundTime
    push_cast
    ring
  subst bits
  apply root_event_pipeline cfg g P samples selected c next (.received (.received i.succ
    (workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false))) oracle he _ hstep
  have hu : (algorithm p cfg).update 0 (c.workers 0) 0 (.received (.received i.succ
      (workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false))) =
      { advance p (c.workers 0) (estimate p cfg g (c.workers 0).point (c.workers 0).iteration samples) with
        outbox := some (broadcastMessage cfg g samples (c.workers 0).iteration)
        targets := (active p cfg).toList } := by
    change accept p cfg (c.workers 0) i.succ _ = _
    have hf : accept p cfg (c.workers 0) i.succ
        (workerMessage cfg g samples (c.workers 0).iteration i ++ List.replicate clockBits false) =
        accept p cfg (c.workers 0) i.succ (workerMessage cfg g samples (c.workers 0).iteration i) := by
      simp only [accept, Fin.cases_succ, decode_workerMessage_frame]
    rw [hf, haccept]
  rw [hu, ho]
  have hclean : clean = { c.oracle.communication with messages := fun _ _ => none } := by
    dsimp only [clean]
    congr 1
    funext source target
    exact hempty source target
  change Pipeline cfg g P samples selected
    { c with
      workers := Function.update c.workers 0
        { advance p (c.workers 0) (estimate p cfg g (c.workers 0).point (c.workers 0).iteration samples) with
          outbox := some (broadcastMessage cfg g samples (c.workers 0).iteration)
          targets := (active p cfg).toList }
      wakeTime := Function.update c.wakeTime 0 c.time
      turn := 1
      oracle := { c.oracle with communication := clean } }
  rw [hclean]
  exact root_complete_pipeline cfg g P samples selected c hp ⟨i, hi⟩ hk hall hfinish

lemma received_broadcast_facts (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle)) :
    i ∈ active p cfg ∧ (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧
      i ∉ (c.workers 0).targets ∧
      (c.workers i.succ).samples = cfg.batch i ∧ (c.workers i.succ).pending = false ∧
      (c.workers i.succ).sent = true ∧ c.time = (c.workers 0).iteration * roundTime p cfg ∧
      bits = broadcastMessage cfg g samples (c.workers i.succ).iteration ++ List.replicate clockBits false := by
  obtain ⟨hm, _⟩ := received_at_finish cfg g P c htimely 0 i.succ bits oracle he
  rw [hp.links] at hm
  simp only [Fin.cases_zero, Fin.cases_succ] at hm
  split_ifs at hm with hvalid
  obtain ⟨hi, hr, hnot⟩ := hvalid
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  obtain ⟨hcount, hsent⟩ := hp.behind i hi hbefore
  have hpending := (sent_worker cfg g P samples selected c hp i hsent).2.2
  obtain ⟨ht, hb⟩ := Prod.mk.inj (Option.some.inj hm)
  have hk : (c.workers 0).iteration - 1 = (c.workers i.succ).iteration := by omega
  exact ⟨hi, hr, hnot, hcount, hpending, hsent, ht.symm, by simpa only [hk] using hb.symm⟩

lemma broadcast_worker_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hi : i ∈ active p cfg) (hqueued : i ∉ (c.workers 0).targets)
    (hr : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration)
    (hcount : (c.workers i.succ).samples = cfg.batch i)
    (htime : c.time = (c.workers 0).iteration * roundTime p cfg) (wake : Time) :
    let advanced := advance p (c.workers i.succ)
      (estimate p cfg g (c.workers i.succ).point (c.workers i.succ).iteration samples)
    let running := decide ((c.workers 0).iteration < cfg.iterations)
    Pipeline cfg g P samples selected
      { c with
        workers := Function.update c.workers i.succ { advanced with
          pending := running
          wakeAt := if running then advanced.wakeAt else timeBudget p cfg + 1 }
        wakeTime := Function.update c.wakeTime i.succ wake
        turn := i.succ.val + 1
        oracle := { c.oracle with
          computation := (Function.update c.oracle.computation i.succ
            { c.oracle.computation i.succ with pending :=
              (if running then some (c.time + p.h i, advanced.point) else none) })
          communication := { c.oracle.communication with messages :=
            (Function.update c.oracle.communication.messages 0
              (Function.update (c.oracle.communication.messages 0) i.succ none)) } } } := by
  classical
  dsimp only
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hb : 0 < cfg.batch i := (Finset.mem_filter.mp hi).2
  have hbefore : (c.workers i.succ).iteration < (c.workers 0).iteration := by omega
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hm
    have he := (hp.arrived_current i hm).1
    omega
  have hd := advance_worker_data cfg g samples selected i (c.workers i.succ)
    (c.oracle.computation i.succ) (hp.workers i) hcount
  constructor
  · simpa only [Function.update_of_ne hz] using hp.root
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self]
      exact ⟨⟨hd.points.point, hd.points.index, hd.points.selected_point⟩,
        hd.count, hd.accumulator, hd.seed, hd.used⟩
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.workers j
  · simpa only [Function.update_of_ne hz] using hp.root_limit
  · apply broadcast_update_worker cfg g P samples c hp.outbox i
    intro h
    exact (hqueued h).elim
  · simpa only [Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j hj
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, advance, hr]
      exact ⟨le_rfl, Nat.le_succ _⟩
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.rounds j hj
  · intro j hj hbehind
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, Function.update_of_ne hz, advance, hr, lt_self_iff_false] at hbehind
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simp only [Function.update_of_ne hne, Function.update_of_ne hz] at hbehind ⊢
      exact hp.behind j hj hbehind
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, WorkerControl, ite_eq_right (Nat.ne_of_gt hb), advance, hr]
      by_cases hk : (c.workers 0).iteration < cfg.iterations
      · simp only [hk, decide_true]
        exact Or.inr (Or.inl ⟨by trivial, hb, by trivial, by trivial⟩)
      · have hdone : (c.workers 0).iteration = cfg.iterations := le_antisymm hp.root_limit (Nat.le_of_not_gt hk)
        simp only [hk, decide_false]
        exact Or.inr (Or.inr (Or.inr ⟨hdone, by trivial, by trivial, by trivial⟩))
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.control j
  · simpa only [Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases he : j = i
    · subst j
      simp only [Function.update_self, advance, hr, htime, zero_add, Nat.cast_zero, zero_add, one_mul]
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne] using hp.pending j
  · intro j hj
    simp only [Function.update_of_ne hz] at hj
    by_cases he : j = i
    · subst j; exact (hnot hj).elim
    · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
      simpa only [Function.update_of_ne hne, Function.update_of_ne hz] using hp.arrived_current j hj
  · simpa only [Function.update_of_ne hz] using hp.arrived_time
  · intro source target
    simp only [Function.update_of_ne hz]
    induction source using Fin.cases with
    | zero =>
        simp only [Function.update_self, Fin.cases_zero]
        induction target using Fin.cases with
        | zero => simp only [Function.update_of_ne hz]; exact hp.links 0 0
        | succ j =>
            by_cases he : j = i
            · subst j
              have hn : (c.workers 0).iteration + 1 ≠ (c.workers 0).iteration := by omega
              simp only [Function.update_self, Fin.cases_succ, advance, hr, hn, false_and, and_false, ite_false]
            · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
              rw [Function.update_of_ne hne, hp.links]
              simp only [Fin.cases_zero, Fin.cases_succ, Function.update_of_ne hne]
    | succ j =>
        rw [Function.update_of_ne (Fin.succ_ne_zero j), hp.links]
        simp only [Fin.cases_succ]
        by_cases he : j = i
        · subst j
          have hn : (c.workers i.succ).iteration ≠ (c.workers 0).iteration := by omega
          simp only [Function.update_self, advance, hn, false_and, and_false, ite_false, Bool.false_eq_true]
        · have hne : j.succ ≠ i.succ := fun h => he (Fin.succ_inj.mp h)
          simp only [Function.update_of_ne hne]

lemma received_broadcast_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (i : Fin p.n) (bits : List Bool) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time =
      some ((i.succ, .received (.received 0 bits)), oracle))
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  obtain ⟨hi, hr, hnot, hcount, hpending, hsent, ht, hbits⟩ :=
    received_broadcast_facts cfg g P samples selected c hp htimely i bits oracle he
  obtain ⟨_, ho⟩ := received_at_finish cfg g P c htimely 0 i.succ bits oracle he
  have hb : 0 < cfg.batch i := (Finset.mem_filter.mp hi).2
  have hnone : (c.oracle.computation i.succ).pending = none := by
    rw [hp.pending, hpending]
    rfl
  have hdecode : decode p cfg (c.workers i.succ).point bits =
      estimate p cfg g (c.workers i.succ).point (c.workers i.succ).iteration samples := by
    rw [hbits, decode_broadcastMessage_frame]
    simp only [broadcastMessage, workerMessage, ← (hp.workers i).points.point, estimate]
  subst oracle
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he, worker_receive, hdecode] at hstep
    by_cases hk : (c.workers 0).iteration < cfg.iterations
    · simp only [algorithm, Fin.cases_succ, advance, hb, hr, hk, Bool.not_false,
        and_self, ite_true] at hstep
      simp only [system, LongTails.Setups.StarNetwork.system, LongTails.Setups.StarNetwork.computation,
        Fin.cases_succ, hnone, Option.some.injEq] at hstep
      subst next
      have h := broadcast_worker_pipeline cfg g P samples selected c hp i hi hnot hr hcount ht c.time
      simpa only [hk, decide_true, ite_true, advance, hr] using h
    · simp only [algorithm, Fin.cases_succ, advance, hb, hr, hk, Bool.not_false,
        false_and, and_false, ite_false, Function.update_idem, Option.some.injEq] at hstep
      subst next
      have h := broadcast_worker_pipeline cfg g P samples selected c hp i hi hnot hr hcount ht
        (max c.time (timeBudget p cfg + 1))
      have hlocal : { c.oracle.computation i.succ with pending := none } =
          c.oracle.computation i.succ := by
        rw [← hnone]
        rfl
      simpa only [hk, decide_false, Bool.false_eq_true, ite_false, advance, hr, hlocal,
        Function.update_eq_self] using h

lemma wake_start_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (i : Fin p.n) (hi : 0 < cfg.batch i) (oracle : OracleState (system p g P))
    (hinit : (c.workers i.succ).iteration = 0 ∧ (c.workers i.succ).samples = 0 ∧
      (c.workers i.succ).pending = false ∧ (c.workers i.succ).sent = false ∧ c.time = 0 ∧ c.wakeTime i.succ = 0)
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((i.succ, .wake), oracle))
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  have ho := (DistributedExecution.wake_event (system p g P) (algorithm p cfg) c c.time i.succ oracle he).1
  subst oracle
  have hk : (c.workers i.succ).iteration < cfg.iterations := by
    rw [hinit.1]
    exact cfg.iterations.pos
  have hj : (c.workers i.succ).samples < cfg.batch i := by rwa [hinit.2.1]
  have hnone : (c.oracle.computation i.succ).pending = none := by
    rw [hp.pending, hinit.2.2.1]
    rfl
  unfold step at hstep
  by_cases hlate : c.deadline < c.time
  · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
  · simp only [ite_eq_right hlate, he] at hstep
    simp only [algorithm, Fin.cases_succ, hi, hk, hj, hinit.2.2.1, Bool.not_false,
      and_self, ite_true] at hstep
    simp only [system, LongTails.Setups.StarNetwork.system, LongTails.Setups.StarNetwork.computation,
      Fin.cases_succ, hnone, Option.some.injEq] at hstep
    subst next
    exact start_worker_pipeline cfg g P samples selected c hp i hi hinit

lemma wake_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (v : Fin (p.n + 1)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((v, .wake), oracle))
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  have hidle (hq : (algorithm p cfg).query v (c.workers v) ((algorithm p cfg).clock c.time) =
      (.advance 0,
        { c.workers v with wakeAt := timeBudget p cfg + 1 })) :
      Pipeline cfg g P samples selected next :=
    wake_idle_pipeline cfg g P samples selected c next hp v oracle _ _ he hq hstep
  induction v using Fin.cases with
  | zero =>
      have ho := (DistributedExecution.wake_event (system p g P) (algorithm p cfg) c c.time 0 oracle he).1
      subst oracle
      apply root_event_pipeline cfg g P samples selected c next .wake c.oracle he _ hstep
      simpa only [show (algorithm p cfg).update 0 (c.workers 0) 0 .wake = c.workers 0 from rfl,
        Function.update_eq_self] using root_ready_pipeline cfg g P samples selected c hp
  | succ i =>
      have hc := hp.control i
      by_cases hz : cfg.batch i = 0
      · apply hidle
        simp [algorithm, hz]
      · simp only [WorkerControl, ite_eq_right hz] at hc
        rcases hc with hinit | hcompute | hsent | hdone
        · exact wake_start_pipeline cfg g P samples selected c next hp i (Nat.pos_of_ne_zero hz)
            oracle hinit he hstep
        · apply hidle
          simp [algorithm, hcompute.2.2.1]
        · apply hidle
          simp [algorithm, hsent.2.1, hsent.2.2.2]
        · apply hidle
          simp [algorithm, hdone.1]

lemma step_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    Pipeline cfg g P samples selected next := by
  classical
  cases he : event (system p g P) (algorithm p cfg) c c.time with
  | none =>
      unfold step at hstep
      by_cases hlate : c.deadline < c.time
      · simp only [ite_eq_left hlate, reduceCtorEq] at hstep
      · simp only [ite_eq_right hlate, he] at hstep
        by_cases hdone : c.time = c.deadline
        · simp only [ite_eq_left hdone, reduceCtorEq] at hstep
        · simp only [ite_eq_right hdone, Option.some.injEq] at hstep
          subst next
          exact jump_pipeline cfg g P samples selected c hp he
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      cases notification with
      | wake => exact wake_pipeline cfg g P samples selected c next hp v oracle he hstep
      | computed reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p g P)
            (algorithm p cfg) c c.time v reply oracle he
          cases reply with
          | computed input value =>
              induction v using Fin.cases with
              | zero =>
                  simp only [system, LongTails.Setups.StarNetwork.system,
                    LongTails.Setups.StarNetwork.computation,
                    Fin.cases_zero, reduceCtorEq] at ha
              | succ i =>
                  by_cases hmore : (c.workers i.succ).samples + 1 < cfg.batch i
                  · exact computed_continue_pipeline cfg g P samples selected c next hp htimely
                      i input value oracle he hmore hstep
                  · have hpend := (computed_worker_facts cfg g P samples selected c hp htimely
                      i input value oracle he).1
                    have hcount := (pending_worker cfg g P samples selected c hp i hpend).2.2.1
                    exact computed_finish_pipeline cfg g P samples selected c next hp htimely
                      i input value oracle he (by omega) hstep
      | received reply =>
          obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p g P)
            (algorithm p cfg) c c.time v reply oracle he
          cases reply with
          | received source bits =>
              have hm := (received_at_finish cfg g P c htimely source v bits oracle he).1
              induction source using Fin.cases with
              | zero =>
                  induction v using Fin.cases with
                  | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
                  | succ i =>
                      exact received_broadcast_pipeline cfg g P samples selected
                        c next hp htimely i bits oracle he hstep
              | succ i =>
                  induction v using Fin.cases with
                  | zero =>
                      by_cases hcomplete : insert i (c.workers 0).arrived = active p cfg
                      · exact received_complete_pipeline cfg g P samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                      · exact received_partial_pipeline cfg g P samples selected c next hp htimely
                          i bits oracle he hcomplete hstep
                  | succ j =>
                      simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                        ite_false, reduceCtorEq] at hm

lemma run_pipeline (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (T : Time) (hactive : (active p cfg).Nonempty) (k : ℕ) :
    Pipeline cfg g P samples selected (run (system p g P) (algorithm p cfg) k
      (initial (system p g P) (algorithm p cfg) T (selected, samples))) := by
  have hrun : ∀ j (c : ExecutionState (system p g P) (algorithm p cfg)),
      Pipeline cfg g P samples selected c → Timely cfg g P c →
      Pipeline cfg g P samples selected (run (system p g P) (algorithm p cfg) j c) := by
    intro j
    induction j with
    | zero => intro c hp _; exact hp
    | succ j ih =>
        intro c hp ht
        cases hs : step (system p g P) (algorithm p cfg) c with
        | none => simpa only [run, hs] using hp
        | some next =>
            simpa only [run, hs] using ih next (step_pipeline cfg g P samples selected c next hp ht hs)
              (step_timely cfg g P c next ht hs)
  exact hrun k _ (initial_pipeline cfg g P samples selected T hactive)
    (initial_timely cfg g P T (selected, samples))

lemma execute_eq_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (T : Time) (hactive : (active p cfg).Nonempty) (hbudget : timeBudget p cfg ≤ T)
    (hfinite : FiniteEvents (system p g P) (algorithm p cfg) T (selected, samples)) :
    execute (system p g P) (algorithm p cfg) T selected samples = output p cfg g (selected, samples) := by
  obtain ⟨k, hk⟩ := hfinite T le_rfl
  rw [DistributedExecution.execute_eq_terminal (system p g P) (algorithm p cfg) T (selected, samples) k hk]
  apply terminal_pipeline_output cfg g P samples selected _
    (run_pipeline cfg g P samples selected T hactive k)
  · exact DistributedExecution.run_time_le_deadline (system p g P) (algorithm p cfg) _ k (by exact zero_le)
  · simpa only [DistributedExecution.run_deadline, initial] using hbudget
  · exact hk

def workerProgress (cfg : Config p) (v : Fin (p.n + 1)) (s : State p) : ℕ :=
  Fin.cases ((2 * p.n + 1) * s.iteration + s.arrived.card + (p.n - s.targets.length))
    (fun i => (cfg.batch i + 2) * s.iteration + s.samples + s.pending.toNat + s.sent.toNat) v

lemma query_progress (cfg : Config p) (v : Fin (p.n + 1)) (s : State p) (clock : ClockReading) :
    workerProgress cfg v s ≤ workerProgress cfg v ((algorithm p cfg).query v s clock).2 := by
  classical
  induction v using Fin.cases with
  | zero =>
      cases h : s.outbox <;> cases ht : s.targets <;> simp [algorithm, h, ht, workerProgress]
      omega
  | succ i =>
      simp only [algorithm, Fin.cases_succ]
      split_ifs with hready hcount hsent
      · have hp : s.pending = false := by simpa using hready.2.2
        simp [workerProgress, hp]
      · have hs : s.sent = false := by simpa using hsent
        simp [workerProgress, hs]
      · simp [workerProgress]
      · simp [workerProgress]

lemma query_worker_progress (cfg : Config p) (i : Fin p.n) (s : State p) (clock : ClockReading)
    (hb : 0 < cfg.batch i) (hk : s.iteration < cfg.iterations)
    (hp : s.pending = false) (hs : s.sent = false) :
    workerProgress cfg i.succ s < workerProgress cfg i.succ ((algorithm p cfg).query i.succ s clock).2 := by
  classical
  simp only [algorithm, Fin.cases_succ, hb, hk, hp, Bool.not_false, and_self, ite_true]
  split_ifs <;> simp_all [workerProgress]

lemma query_worker_progress_or_idle (cfg : Config p) (i : Fin p.n) (s : State p)
    (clock : ClockReading) :
    workerProgress cfg i.succ s < workerProgress cfg i.succ ((algorithm p cfg).query i.succ s clock).2 ∨
      (algorithm p cfg).query i.succ s clock =
        (.advance 0,
          { s with wakeAt := timeBudget p cfg + 1 }) := by
  classical
  simp only [algorithm, Fin.cases_succ]
  split_ifs with hready hcount hsent
  · left
    have hp : s.pending = false := by simpa using hready.2.2
    simp [workerProgress, hp]
  · left
    have hs : s.sent = false := by simpa using hsent
    simp [workerProgress, hs]
  · exact Or.inr rfl
  · exact Or.inr rfl

lemma advance_progress (cfg : Config p) (i : Fin p.n) (s : State p) (value : Point p)
    (hcount : s.samples ≤ cfg.batch i) (hp : s.pending = false) (hs : s.sent = true) :
    workerProgress cfg i.succ s < workerProgress cfg i.succ (advance p s value) := by
  simp only [workerProgress, Fin.cases_succ, advance, hp, hs, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_add, Nat.mul_one]
  omega

lemma accept_progress (cfg : Config p) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hi : i ∈ active p cfg) (hnot : i ∉ s.arrived) :
    workerProgress cfg 0 s < workerProgress cfg 0 (accept p cfg s i.succ bits) := by
  classical
  have hc : s.arrived.card ≤ p.n := by simpa using Finset.card_le_univ s.arrived
  have htargets := Nat.sub_le p.n s.targets.length
  unfold accept
  simp only [Fin.cases_succ, ite_eq_left (show i ∈ active p cfg ∧ i ∉ s.arrived from ⟨hi, hnot⟩)]
  split_ifs <;> simp only [workerProgress, Fin.cases_zero, advance, Finset.card_empty,
    Finset.card_insert_of_notMem hnot, Nat.mul_add, Nat.mul_one] <;> omega

lemma event_progress_or_idle (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (v : Fin (p.n + 1)) (notification : Event (ComputeReply p) (CommReply p))
    (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((v, notification), oracle)) :
    workerProgress cfg v (c.workers v) < workerProgress cfg v
      ((algorithm p cfg).query v ((algorithm p cfg).update v (c.workers v)
        ((algorithm p cfg).clock c.time) notification) ((algorithm p cfg).clock c.time)).2 ∨
    (notification = .wake ∧ (algorithm p cfg).query v (c.workers v) ((algorithm p cfg).clock c.time) =
      (.advance 0,
        { c.workers v with wakeAt := timeBudget p cfg + 1 })) := by
  classical
  cases notification with
  | wake =>
      induction v using Fin.cases with
      | zero =>
          cases ht : (c.workers 0).targets with
          | nil =>
              right
              have ho : (c.workers 0).outbox = none := by simpa only [ht, ite_true] using hp.outbox.message
              exact ⟨rfl, by simp [algorithm, ho]⟩
          | cons i rest =>
              left
              have ho : (c.workers 0).outbox = some (broadcastMessage cfg g samples ((c.workers 0).iteration - 1)) := by
                simpa only [ht, List.cons_ne_nil, ite_false] using hp.outbox.message
              have hlength : rest.length + 1 ≤ p.n := by
                simpa only [ht, List.length_cons, Fintype.card_fin] using hp.outbox.nodup.length_le_card
              simp only [algorithm, Fin.cases_zero, ho, ht, workerProgress, List.length_cons]
              omega
      | succ i =>
          rcases query_worker_progress_or_idle cfg i (c.workers i.succ) 0 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨rfl, h⟩
  | computed reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.computed_event (system p g P)
        (algorithm p cfg) c c.time v reply oracle he
      cases reply with
      | computed input value =>
          induction v using Fin.cases with
          | zero =>
              simp only [system, LongTails.Setups.StarNetwork.system,
                LongTails.Setups.StarNetwork.computation,
                Fin.cases_zero, reduceCtorEq] at ha
          | succ i =>
              left
              have hpend := (computed_worker_facts cfg g P samples selected c hp htimely
                i input value oracle he).1
              obtain ⟨hb, hk, _, hs, _⟩ := pending_worker cfg g P samples selected c hp i hpend
              let s := (algorithm p cfg).update i.succ (c.workers i.succ) 0 (.computed (.computed input value))
              have hsame : workerProgress cfg i.succ (c.workers i.succ) = workerProgress cfg i.succ s := by
                simp [s, algorithm, workerProgress, hpend, hs, Nat.add_assoc]
              rw [hsame]
              exact query_worker_progress cfg i s 0 hb hk rfl hs
  | received reply =>
      obtain ⟨state, ha, _⟩ := DistributedExecution.received_event (system p g P)
        (algorithm p cfg) c c.time v reply oracle he
      cases reply with
      | received source bits =>
          have hm := (received_at_finish cfg g P c htimely source v bits oracle he).1
          induction source using Fin.cases with
          | zero =>
              induction v using Fin.cases with
              | zero => simp only [hp.links, Fin.cases_zero, reduceCtorEq] at hm
              | succ i =>
                  left
                  obtain ⟨_, _, _, hcount, hpend, hsent, _⟩ :=
                    received_broadcast_facts cfg g P samples selected c hp htimely i bits oracle he
                  have h := (advance_progress cfg i (c.workers i.succ)
                    (decode p cfg (c.workers i.succ).point bits) hcount.le hpend hsent).trans_le
                    (query_progress cfg i.succ _ 0)
                  simpa only [worker_receive, show (algorithm p cfg).clock c.time = 0 from rfl] using h
          | succ i =>
              induction v using Fin.cases with
              | zero =>
                  left
                  obtain ⟨hi, _, _, hnot, _⟩ := received_worker_facts cfg g P samples selected
                    c hp htimely i bits oracle he
                  have h := (accept_progress cfg (c.workers 0) i bits hi hnot).trans_le
                    (query_progress cfg 0 _ 0)
                  simpa only [algorithm, ite_true] using h
              | succ j =>
                  simp only [hp.links, Fin.cases_succ, Fin.succ_ne_zero, false_and,
                    ite_false, reduceCtorEq] at hm

def workerProgressBound (cfg : Config p) (v : Fin (p.n + 1)) : ℕ :=
  Fin.cases ((2 * p.n + 1) * cfg.iterations + 2 * p.n)
    (fun i => (cfg.batch i + 2) * cfg.iterations + cfg.batch i + 2) v

lemma worker_progress_le (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c : ExecutionState (system p g P) (algorithm p cfg)) (hp : Pipeline cfg g P samples selected c)
    (v : Fin (p.n + 1)) : workerProgress cfg v (c.workers v) ≤ workerProgressBound cfg v := by
  classical
  induction v using Fin.cases with
  | zero =>
      have hc : (c.workers 0).arrived.card ≤ p.n := by simpa using Finset.card_le_univ (c.workers 0).arrived
      have hm := Nat.mul_le_mul_left (2 * p.n + 1) hp.root_limit
      have ht := Nat.sub_le p.n (c.workers 0).targets.length
      simp only [workerProgress, workerProgressBound, Fin.cases_zero]
      omega
  | succ i =>
      have hk : (c.workers i.succ).iteration ≤ cfg.iterations := by
        by_cases hz : cfg.batch i = 0
        · have hc := hp.control i
          simp only [WorkerControl, hz, ite_true] at hc
          rw [hc.1]
          exact Nat.zero_le _
        · exact ((hp.rounds i (by simp [active, Nat.pos_of_ne_zero hz])).1).trans hp.root_limit
      have hm := Nat.mul_le_mul_left (cfg.batch i + 2) hk
      have hc := (hp.workers i).count
      have hpend : (c.workers i.succ).pending.toNat ≤ 1 := by cases (c.workers i.succ).pending <;> decide
      have hsent : (c.workers i.succ).sent.toNat ≤ 1 := by cases (c.workers i.succ).sent <;> decide
      simp only [workerProgress, workerProgressBound, Fin.cases_succ]
      omega

noncomputable def workerRank (cfg : Config p) (T : Time) (v : Fin (p.n + 1))
    (s : State p) (wake : Time) : ℕ :=
  2 * (workerProgressBound cfg v - workerProgress cfg v s) + if wake ≤ T then 1 else 0

lemma workerRank_decrease (cfg : Config p) (T : Time) (v : Fin (p.n + 1))
    (old next : State p) (oldWake newWake : Time)
    (hbound : workerProgress cfg v next ≤ workerProgressBound cfg v)
    (hprogress : workerProgress cfg v old < workerProgress cfg v next) :
    workerRank cfg T v next newWake < workerRank cfg T v old oldWake := by
  unfold workerRank
  split_ifs <;> omega

lemma event_rank_decrease (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ timeBudget p cfg) (v : Fin (p.n + 1))
    (notification : Event (ComputeReply p) (CommReply p)) (oracle : OracleState (system p g P))
    (he : event (system p g P) (algorithm p cfg) c c.time = some ((v, notification), oracle))
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    (∑ j, workerRank cfg c.deadline j (next.workers j) (next.wakeTime j)) <
      ∑ j, workerRank cfg c.deadline j (c.workers j) (c.wakeTime j) := by
  classical
  generalize hquery : (algorithm p cfg).query v ((algorithm p cfg).update v (c.workers v)
    ((algorithm p cfg).clock c.time) notification) ((algorithm p cfg).clock c.time) = pair
  obtain ⟨action, state⟩ := pair
  obtain ⟨hworkers, hwakes⟩ := DistributedExecution.step_event_state (system p g P)
    (algorithm p cfg) c next v notification oracle action state he hquery hstep
  have hstrict : workerRank cfg c.deadline v (next.workers v) (next.wakeTime v) <
      workerRank cfg c.deadline v (c.workers v) (c.wakeTime v) := by
    rcases event_progress_or_idle cfg g P samples selected c hp htimely v notification oracle he with
      hprogress | ⟨hn, hidle⟩
    · have hbound := worker_progress_le cfg g P samples selected next
        (step_pipeline cfg g P samples selected c next hp htimely hstep) v
      simp only [hquery] at hprogress
      simp only [hworkers, Function.update_self] at hbound ⊢
      exact workerRank_decrease cfg c.deadline v (c.workers v) state (c.wakeTime v)
        (next.wakeTime v) hbound hprogress
    · subst notification
      change (algorithm p cfg).query v (c.workers v) ((algorithm p cfg).clock c.time) = (action, state) at hquery
      rw [hidle] at hquery
      cases hquery
      have hw := (DistributedExecution.wake_event (system p g P) (algorithm p cfg)
        c c.time v oracle he).2
      simp only [hworkers, hwakes, Function.update_self, workerRank]
      have heq : workerProgress cfg v { c.workers v with
          wakeAt := timeBudget p cfg + 1 } = workerProgress cfg v (c.workers v) := by
        induction v using Fin.cases <;> rfl
      rw [heq]
      have hready : c.wakeTime v ≤ c.deadline := hw.trans htime
      have hafter : ¬ max c.time ((algorithm p cfg).timer 0) ≤ c.deadline := by
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

noncomputable def executionRank (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p))
    (c : ExecutionState (system p g P) (algorithm p cfg)) : ℕ :=
  2 * (∑ v, workerRank cfg c.deadline v (c.workers v) (c.wakeTime v)) +
    if c.time = c.deadline ∨ (event (system p g P) (algorithm p cfg) c c.time).isSome then 0 else 1

lemma step_rank_decrease (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (c next : ExecutionState (system p g P) (algorithm p cfg))
    (hp : Pipeline cfg g P samples selected c) (htimely : Timely cfg g P c)
    (htime : c.time ≤ c.deadline) (hbudget : c.deadline ≤ timeBudget p cfg)
    (hstep : step (system p g P) (algorithm p cfg) c = some next) :
    executionRank cfg g P next < executionRank cfg g P c := by
  classical
  cases he : event (system p g P) (algorithm p cfg) c c.time with
  | none =>
      have hdone : c.time ≠ c.deadline := by
        intro h
        have hn := (DistributedExecution.step_terminal_iff (system p g P) (algorithm p cfg) c htime).mpr ⟨h, he⟩
        rw [hn] at hstep
        cases hstep
      simp only [step, ite_eq_right (not_lt.mpr htime), he, ite_eq_right hdone, Option.some.injEq] at hstep
      subst next
      have hex := DistributedExecution.star_nextTime_exists ⟨p.h, p.l, p.b⟩
        (fun i x (samples : Samples p) k => g i x (samples i k)) P (algorithm p cfg) c htime
      have hn := (DistributedExecution.nextTime_spec (event (system p g P) (algorithm p cfg) c)
        c.time c.deadline hex).1.2.2
      have hready :
          (nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline = c.deadline ∨
          (event (system p g P) (algorithm p cfg)
            { c with time := nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline }
            (nextTime (event (system p g P) (algorithm p cfg) c) c.time c.deadline)).isSome) := hn
      simp only [executionRank, hready, ite_true, he, Option.isSome_none, Bool.false_eq_true,
        or_false, hdone, ite_false, Nat.add_zero]
      exact Nat.lt_succ_self _
  | some result =>
      rcases result with ⟨⟨v, notification⟩, oracle⟩
      have hr := event_rank_decrease cfg g P samples selected c next hp htimely htime hbudget v notification oracle he hstep
      have hd := DistributedExecution.step_deadline (system p g P) (algorithm p cfg) c next hstep
      unfold executionRank
      rw [hd]
      split_ifs <;> omega

lemma finiteEvents (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (hactive : (active p cfg).Nonempty)
    (selected : Fin cfg.iterations) (samples : Samples p) :
    FiniteEvents (system p g P) (algorithm p cfg) (timeBudget p cfg) (selected, samples) := by
  intro T hT
  apply DistributedExecution.termination_of_rank (system p g P) (algorithm p cfg)
    (fun c => Pipeline cfg g P samples selected c ∧ Timely cfg g P c ∧ c.time ≤ c.deadline ∧ c.deadline ≤ timeBudget p cfg)
    (executionRank cfg g P)
  · intro c next hc hs
    refine ⟨⟨step_pipeline cfg g P samples selected c next hc.1 hc.2.1 hs,
      step_timely cfg g P c next hc.2.1 hs,
      DistributedExecution.step_time_le_deadline (system p g P) (algorithm p cfg) c next hc.2.2.1 hs,
      by simpa only [DistributedExecution.step_deadline _ _ _ _ hs] using hc.2.2.2⟩, ?_⟩
    exact step_rank_decrease cfg g P samples selected c next hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hs
  · exact ⟨initial_pipeline cfg g P samples selected T hactive,
      initial_timely cfg g P T (selected, samples), by exact zero_le, hT⟩

lemma execute_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : MeasureTheory.ProbabilityMeasure (Samples p)) (samples : Samples p) (selected : Fin cfg.iterations)
    (hactive : (active p cfg).Nonempty) :
    execute (system p g P) (algorithm p cfg) (timeBudget p cfg) selected samples = output p cfg g (selected, samples) :=
  execute_eq_output cfg g P samples selected (timeBudget p cfg) hactive le_rfl
    (finiteEvents cfg g P hactive selected samples)

end LongTails.Proofs.DistributedBatchedExecution
