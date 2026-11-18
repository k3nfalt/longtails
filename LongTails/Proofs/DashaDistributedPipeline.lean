import LongTails.Proofs.DashaDistributedExecution
import LongTails.Proofs.DashaDistributedTiming

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedPipeline

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming

variable {p : Params}

def WorkerControl (cfg : Config p) (time wake : Time) (s : State p) : Prop :=
  (s.iteration = 0 ∧ s.pending = false ∧ s.sent = false ∧ time = 0 ∧ wake = 0) ∨
  (s.iteration < cfg.iterations ∧ s.pending = true ∧ s.sent = false) ∨
  (s.iteration < cfg.iterations ∧ s.pending = false ∧ s.sent = true) ∨
  (s.iteration = cfg.iterations ∧ s.pending = false ∧ s.sent = false)

structure BroadcastControl (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) : Prop where
  message : (c.workers 0).outbox = if (c.workers 0).targets = [] then none else
    some (broadcastMessage cfg f seed ((c.workers 0).iteration - 1))
  nodup : (c.workers 0).targets.Nodup
  queued : ∀ i ∈ (c.workers 0).targets, (c.workers i.succ).iteration + 1 = (c.workers 0).iteration
  ready : (c.workers 0).targets ≠ [] → c.wakeTime 0 ≤ c.time
  finish : (c.workers 0).targets ≠ [] →
    c.time =
      roundStart p cfg (c.workers 0).iteration

structure Pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg)) : Prop where
  root : RootData cfg f seed selected (c.workers 0)
  workers : ∀ i, WorkerData cfg f seed selected i (c.workers i.succ) (c.oracle.computation i.succ)
  root_limit : (c.workers 0).iteration ≤ cfg.iterations
  outbox : BroadcastControl cfg f seed c
  arrived_incomplete : (c.workers 0).arrived ≠ Finset.univ
  rounds : ∀ i : Fin p.n, (c.workers i.succ).iteration ≤ (c.workers 0).iteration ∧
    (c.workers 0).iteration ≤ (c.workers i.succ).iteration + 1
  behind : ∀ i : Fin p.n, (c.workers i.succ).iteration < (c.workers 0).iteration → (c.workers i.succ).sent = true
  control : ∀ i : Fin p.n, WorkerControl cfg c.time (c.wakeTime i.succ) (c.workers i.succ)
  root_pending : (c.oracle.computation 0).pending = none
  pending : ∀ i : Fin p.n, (c.oracle.computation i.succ).pending =
    if (c.workers i.succ).pending then
      some (roundStart p cfg (c.workers i.succ).iteration + p.h i, (c.workers i.succ).point) else none
  arrived_current : ∀ i ∈ (c.workers 0).arrived,
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧ (c.workers i.succ).sent = true
  arrived_time : ∀ i ∈ (c.workers 0).arrived,
    roundStart p cfg (c.workers 0).iteration + p.h i +
      uploadTime p cfg (c.workers i.succ).iteration ≤ c.time
  links : ∀ source target, c.oracle.communication.messages source target =
    Fin.cases
      (Fin.cases none (fun i =>
        if (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧ i ∉ (c.workers 0).targets then
          some (roundStart p cfg (c.workers 0).iteration,
            broadcastMessage cfg f seed ((c.workers 0).iteration - 1) ++ List.replicate clockBits false) else none) target)
      (fun i =>
        if target = 0 ∧ (c.workers i.succ).iteration = (c.workers 0).iteration ∧
            (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived then
          some (roundStart p cfg (c.workers i.succ).iteration + p.h i +
              uploadTime p cfg (c.workers i.succ).iteration,
            workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false) else none) source

lemma initial_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (T : Time) :
    Pipeline cfg f seed selected (initial (system p f) (algorithm p cfg) T ((selected, seed), ())) := by
  let : Nonempty (Fin p.n) := ⟨⟨0, p.n.pos⟩⟩
  refine {
    root := initial_root_data cfg f seed selected
    workers := fun i => initial_worker_data cfg f seed selected i
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
  · simpa only [initial, algorithm] using (Finset.univ_nonempty (α := Fin p.n)).ne_empty.symm
  · intro i
    simp [initial, algorithm]
  · intro i hlt
    simp [initial, algorithm] at hlt
  · intro i
    simp [WorkerControl, initial, algorithm]
  · intro i
    simp [initial, algorithm, system, communication, Oracle.initial,
      LongTails.Setups.StarNetwork.computation]
  · intro i hi
    simp [initial, algorithm] at hi
  · intro i hi
    simp [initial, algorithm] at hi
  · intro source target
    refine Fin.cases ?_ (fun i => ?_) source
    · refine Fin.cases ?_ (fun i => ?_) target <;>
        simp [initial, algorithm, system, communication, Oracle.initial,
          LongTails.Setups.StarNetwork.communication]
    · simp [initial, algorithm, system, communication, Oracle.initial,
        LongTails.Setups.StarNetwork.communication]

lemma broadcast_update_worker (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (hb : BroadcastControl cfg f seed c)
    (i : Fin p.n) (state : State p) (wake : Time) (oracle : OracleState (system p f)) (turn : ℕ)
    (hiter : i ∈ (c.workers 0).targets → state.iteration = (c.workers i.succ).iteration) :
    BroadcastControl cfg f seed
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
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self, hiter hj] using hb.queued i hj
    · simpa only [Function.update_of_ne (fun h => he (Fin.succ_inj.mp h))] using hb.queued j hj
  · simpa only [Function.update_of_ne hz] using hb.ready
  · simpa only [Function.update_of_ne hz] using hb.finish

lemma quiet_targets_empty (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (hb : BroadcastControl cfg f seed c)
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none) :
    (c.workers 0).targets = [] := by
  by_contra h
  have he := (DistributedExecution.event_ready (system p f) (algorithm p cfg) c c.time).mpr
    (Or.inr ⟨0, hb.ready h⟩)
  simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he

lemma jump_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c)
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none) :
    Pipeline cfg f seed selected
      { c with time := nextTime (event (system p f) (algorithm p cfg) c) c.time c.deadline } := by
  have ht := DistributedExecution.nextTime_ge (event (system p f) (algorithm p cfg) c) c.time c.deadline
  have hempty := quiet_targets_empty cfg f seed c hp.outbox hquiet
  refine {
    root := hp.root
    workers := hp.workers
    root_limit := hp.root_limit
    outbox := ?_
    arrived_incomplete := hp.arrived_incomplete
    rounds := hp.rounds
    behind := hp.behind
    control := ?_
    root_pending := hp.root_pending
    pending := hp.pending
    arrived_current := hp.arrived_current
    arrived_time := ?_
    links := hp.links }
  · exact ⟨hp.outbox.message, hp.outbox.nodup, hp.outbox.queued,
      fun h => False.elim (h hempty), fun h => False.elim (h hempty)⟩
  · intro i
    rcases hp.control i with hi | hi | hi | hi
    · have hw : c.wakeTime i.succ ≤ c.time := by rw [hi.2.2.2.1, hi.2.2.2.2]
      have he := (DistributedExecution.event_ready (system p f) (algorithm p cfg) c c.time).mpr
        (Or.inr ⟨i.succ, hw⟩)
      simp only [hquiet, Option.isSome_none, Bool.false_eq_true] at he
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))
  · intro i hi
    exact (hp.arrived_time i hi).trans ht

lemma computed_facts (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    (c.workers i.succ).pending = true ∧ (c.workers i.succ).sent = false ∧
    (c.workers i.succ).iteration < cfg.iterations ∧
    c.time = roundStart p cfg (c.workers i.succ).iteration + p.h i ∧
    input = (c.workers i.succ).point ∧ value = gradient (f i) (c.workers i.succ).point := by
  obtain ⟨hpend, hvalue, _⟩ := computed_at_finish cfg f c htimely i input value next hevent
  rw [hp.pending i] at hpend
  by_cases hflag : (c.workers i.succ).pending = true
  · simp only [hflag, ite_true] at hpend
    have he := Option.some.inj hpend
    have hx : input = (c.workers i.succ).point := (congrArg Prod.snd he).symm
    have ht : c.time = roundStart p cfg (c.workers i.succ).iteration + p.h i := (congrArg Prod.fst he).symm
    have hcontrol : (c.workers i.succ).iteration < cfg.iterations ∧ (c.workers i.succ).sent = false := by
      rcases hp.control i with h | h | h | h
      · simp [hflag] at h
      · exact ⟨h.1, h.2.2⟩
      · simp [hflag] at h
      · simp [hflag] at h
    exact ⟨hflag, hcontrol.2, hcontrol.1, ht, hx, by simpa only [hx] using hvalue⟩
  · simp [hflag] at hpend

lemma received_worker_facts (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next)) :
    (c.workers i.succ).iteration = (c.workers 0).iteration ∧
    (c.workers i.succ).sent = true ∧ i ∉ (c.workers 0).arrived ∧
    c.time = roundStart p cfg (c.workers i.succ).iteration + p.h i + uploadTime p cfg (c.workers i.succ).iteration ∧
    bits = workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false := by
  have hmsg := (received_at_finish cfg f c htimely i.succ 0 bits next hevent).1
  rw [hp.links i.succ 0] at hmsg
  simp only [Fin.cases_succ, true_and] at hmsg
  split_ifs at hmsg with h
  · have he := Option.some.inj hmsg
    exact ⟨h.1, h.2.1, h.2.2, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

lemma sent_iteration_lt (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (hs : (c.workers i.succ).sent = true) :
    (c.workers i.succ).iteration < cfg.iterations := by
  rcases hp.control i with h | h | h | h
  · simp [hs] at h
  · exact h.1
  · exact h.1
  · simp [hs] at h

lemma last_arrival_time (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (haligned : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + p.h i +
      uploadTime p cfg (c.workers 0).iteration)
    (hall : insert i (c.workers 0).arrived = Finset.univ) :
    c.time = roundStart p cfg ((c.workers 0).iteration + 1) ∧
      ∀ j : Fin p.n, (c.workers j.succ).iteration = (c.workers 0).iteration := by
  classical
  have hmem (j : Fin p.n) : j = i ∨ j ∈ (c.workers 0).arrived := by
    have hj : j ∈ insert i (c.workers 0).arrived := by rw [hall]; exact Finset.mem_univ j
    exact Finset.mem_insert.mp hj
  have ha (j : Fin p.n) : (c.workers j.succ).iteration = (c.workers 0).iteration := by
    rcases hmem j with rfl | hj
    · exact haligned
    · exact (hp.arrived_current j hj).1
  refine ⟨?_, ha⟩
  rw [roundStart_succ]
  apply le_antisymm
  · rw [htime]
    exact add_le_add (add_le_add le_rfl (computationTime_le i)) le_rfl
  · obtain ⟨j, hj⟩ := computationTime_attained (p := p)
    rw [hj]
    rcases hmem j with rfl | hmem
    · exact htime.ge
    · simpa only [ha j] using hp.arrived_time j hmem

lemma received_broadcast_facts (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .received (.received 0 bits)), next)) :
    (c.workers i.succ).iteration + 1 = (c.workers 0).iteration ∧
    i ∉ (c.workers 0).targets ∧ (c.workers i.succ).sent = true ∧
    c.time = roundStart p cfg (c.workers 0).iteration ∧
    bits = broadcastMessage cfg f seed (c.workers i.succ).iteration ++ List.replicate clockBits false := by
  have hmsg := (received_at_finish cfg f c htimely 0 i.succ bits next hevent).1
  rw [hp.links 0 i.succ] at hmsg
  simp only [Fin.cases_zero, Fin.cases_succ] at hmsg
  split_ifs at hmsg with h
  have he := Option.some.inj hmsg
  have hk : (c.workers 0).iteration - 1 = (c.workers i.succ).iteration := by omega
  refine ⟨h.1, h.2, hp.behind i (by omega), (congrArg Prod.fst he).symm, ?_⟩
  simpa only [hk] using (congrArg Prod.snd he).symm

noncomputable def afterComputed (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers i.succ
      { computed p cfg i (c.workers i.succ) (gradient (f i) (c.workers i.succ).point) with
        outbox := none, sent := true }
    wakeTime := Function.update c.wakeTime i.succ c.time
    turn := i.succ.val + 1
    oracle := { c.oracle with
      computation := Function.update c.oracle.computation i.succ
        { c.oracle.computation i.succ with pending := none, used := (c.oracle.computation i.succ).used + 1 }
      communication := { messages := (Function.update c.oracle.communication.messages i.succ
        (Function.update (c.oracle.communication.messages i.succ) 0
          (some (c.time + uploadTime p cfg (c.workers i.succ).iteration,
            workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false)))) } } }

lemma computed_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (i : Fin p.n)
    (hs : (c.workers i.succ).sent = false)
    (hk : (c.workers i.succ).iteration < cfg.iterations)
    (htime : c.time = roundStart p cfg (c.workers i.succ).iteration + p.h i) :
    Pipeline cfg f seed selected (afterComputed cfg f seed c i) := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have haligned : (c.workers i.succ).iteration = (c.workers 0).iteration := by
    have hr := hp.rounds i
    by_contra hne
    have hb := hp.behind i (by omega)
    simp [hs] at hb
  have hnot : i ∉ (c.workers 0).arrived := by
    intro hi
    have hb := (hp.arrived_current i hi).2
    simp [hs] at hb
  refine {
    root := ?_
    workers := ?_
    root_limit := ?_
    outbox := ?_
    arrived_incomplete := ?_
    rounds := ?_
    behind := ?_
    control := ?_
    root_pending := ?_
    pending := ?_
    arrived_current := ?_
    arrived_time := ?_
    links := ?_ }
  · simpa only [afterComputed, Function.update_of_ne hz] using hp.root
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [afterComputed, Function.update_self] using
        computed_worker_data cfg f seed selected hexact i _ _ (hp.workers i) hk hs
    · simpa only [afterComputed, Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h))] using hp.workers j
  · simpa only [afterComputed, Function.update_of_ne hz] using hp.root_limit
  · exact broadcast_update_worker cfg f seed c hp.outbox i _ _ _ _ (fun _ => rfl)
  · simpa only [afterComputed, Function.update_of_ne hz] using hp.arrived_incomplete
  · intro j
    by_cases hj : j = i
    · subst j
      simpa only [afterComputed, Function.update_self, Function.update_of_ne hz, computed] using hp.rounds i
    · simpa only [afterComputed, Function.update_of_ne hz,
        Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h))] using hp.rounds j
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [afterComputed, Function.update_self]
      exact fun _ => trivial
    · simpa only [afterComputed, Function.update_of_ne hz,
        Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h))] using hp.behind j
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [afterComputed, Function.update_self, computed, WorkerControl]
      exact Or.inr (Or.inr (Or.inl ⟨hk, trivial, trivial⟩))
    · simpa only [afterComputed, Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h))] using hp.control j
  · simpa only [afterComputed, Function.update_of_ne hz] using hp.root_pending
  · intro j
    by_cases hj : j = i
    · subst j
      simp [afterComputed, computed]
    · simpa only [afterComputed, Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h))] using hp.pending j
  · intro j hj
    simp only [afterComputed, Function.update_of_ne hz] at hj ⊢
    have hji : j ≠ i := fun he => hnot (he ▸ hj)
    simpa only [Function.update_of_ne (fun h => hji (Fin.succ_inj.mp h))] using hp.arrived_current j hj
  · intro j hj
    simp only [afterComputed, Function.update_of_ne hz] at hj ⊢
    have hji : j ≠ i := fun he => hnot (he ▸ hj)
    simpa only [Function.update_of_ne (fun h => hji (Fin.succ_inj.mp h))] using hp.arrived_time j hj
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterComputed, Function.update_of_ne hz, Fin.cases_zero] using hp.links 0 0
      · by_cases hj : j = i
        · subst j
          simpa only [afterComputed, Function.update_of_ne hz, Function.update_self, computed,
            Fin.cases_zero, Fin.cases_succ] using hp.links 0 i.succ
        · simpa only [afterComputed, Function.update_of_ne hz,
            Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h)), Fin.cases_zero, Fin.cases_succ] using hp.links 0 j.succ
    · by_cases hj : j = i
      · subst j
        by_cases ht : target = 0
        · subst target
          simp [afterComputed, Function.update_of_ne hz, computed, haligned, hnot, htime]
        · have hold := hp.links i.succ target
          simp only [Fin.cases_succ, ht, false_and, ite_false] at hold
          simp [afterComputed, Function.update_of_ne hz, computed, ht, hold]
      · simpa only [afterComputed, Function.update_of_ne hz,
          Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h)), Fin.cases_succ] using hp.links j.succ target

lemma computed_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    step (system p f) (algorithm p cfg) c = some (afterComputed cfg f seed c i) := by
  classical
  obtain ⟨hflag, hs, hk, _, _, hv⟩ := computed_facts cfg f seed selected c hp htimely i input value next hevent
  have hn := (computed_at_finish cfg f c htimely i input value next hevent).2.2
  have hc := (hp.workers i).code
  have hg := (hp.workers i).gradient
  simp only [hs, Bool.false_eq_true, ite_false] at hc hg
  have hvalues := computed_values cfg f seed hexact _ hk i (c.workers i.succ) rfl
    (hp.workers i).randomness hc hg
  have hm : (computed p cfg i (c.workers i.succ) value).outbox =
      some (workerMessage cfg f seed (c.workers i.succ).iteration i) := by
    simpa only [hv, (hp.workers i).points.point] using hvalues.2.2
  have hquery : (algorithm p cfg).query i.succ
      ((algorithm p cfg).update i.succ (c.workers i.succ) ((algorithm p cfg).clock c.time)
        (.computed (.computed input value))) ((algorithm p cfg).clock c.time) =
      (.communicate (0, workerMessage cfg f seed (c.workers i.succ).iteration i),
        { computed p cfg i (c.workers i.succ) value with outbox := none, sent := true }) := by
    change (algorithm p cfg).query i.succ (computed p cfg i (c.workers i.succ) value) _ = _
    rw [computed_query cfg i _ _ _ hk hs, hm]
    rfl
  have hempty : c.oracle.communication.messages i.succ 0 = none := by
    rw [hp.links i.succ 0]
    simp [hs]
  have hcomm : (communication p).submit c.oracle.communication c.time i.succ
      (0, workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false) =
      { messages := Function.update c.oracle.communication.messages i.succ
          (Function.update (c.oracle.communication.messages i.succ) 0
            (some (c.time + uploadTime p cfg (c.workers i.succ).iteration,
              workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false))) } := by
    simp [communication, LongTails.Setups.StarNetwork.communication, hempty,
      workerMessage_length, uploadTime, add_comm, add_left_comm]
  change (system p f).communication.submit c.oracle.communication c.time i.succ
    (0, workerMessage cfg f seed (c.workers i.succ).iteration i ++ List.replicate clockBits false) = _ at hcomm
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hquery, hn]
  change some _ = some _
  rw [hcomm]
  simp only [afterComputed, hv]

lemma computed_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (input value : Point p) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((i.succ, .computed (.computed input value)), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  obtain ⟨_, hs, hk, ht, _, _⟩ := computed_facts cfg f seed selected c hp htimely i input value next hevent
  exact ⟨_, computed_step_eq cfg f seed selected c hp hexact htimely hdeadline i input value next hevent,
    computed_pipeline cfg f seed selected c hp hexact i hs hk ht⟩

lemma computed_progress_strict (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n)
    (hflag : (c.workers i.succ).pending = true) (hs : (c.workers i.succ).sent = false) :
    workerProgress i.succ (c.workers i.succ) <
      workerProgress i.succ ((afterComputed cfg f seed c i).workers i.succ) := by
  simp [workerProgress, afterComputed, computed, hflag, hs, (hp.workers i).outbox]

lemma progress_bounded (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) :
    workerProgress 0 (c.workers 0) ≤ (2 * p.n + 1) * cfg.iterations + 2 * p.n ∧
      ∀ i : Fin p.n, workerProgress i.succ (c.workers i.succ) ≤ 4 * cfg.iterations + 3 := by
  constructor
  · have hc : (c.workers 0).arrived.card ≤ p.n := by
      simpa using Finset.card_le_univ (c.workers 0).arrived
    have ht := Nat.sub_le p.n (c.workers 0).targets.length
    have hr := Nat.mul_le_mul_left (2 * p.n + 1) hp.root_limit
    simp only [workerProgress, Fin.cases_zero]
    omega
  · intro i
    have hr := (hp.rounds i).1.trans hp.root_limit
    have ho := (hp.workers i).outbox
    simp only [workerProgress, Fin.cases_succ, ho, Option.isSome_none, Bool.toNat_false, mul_zero, add_zero]
    rcases hp.control i with h | h | h | h
    · simp only [h.2.1, h.2.2.1, Bool.toNat_false, mul_zero, add_zero]
      omega
    · simp only [h.2.1, h.2.2, Bool.toNat_true, Bool.toNat_false, mul_zero, add_zero]
      omega
    · simp only [h.2.1, h.2.2, Bool.toNat_true, Bool.toNat_false, add_zero]
      omega
    · simp only [h.2.1, h.2.2, Bool.toNat_false, mul_zero, add_zero]
      omega

lemma quiet_pipeline_complete (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htime : timeBudget p cfg ≤ c.time)
    (hquiet : event (system p f) (algorithm p cfg) c c.time = none) :
    (c.workers 0).iteration = cfg.iterations := by
  classical
  have hempty := quiet_targets_empty cfg f seed c hp.outbox hquiet
  have haligned (i : Fin p.n) : (c.workers i.succ).iteration = (c.workers 0).iteration := by
    by_contra hne
    have hs : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration := by
      have hr := hp.rounds i
      omega
    have hlink := hp.links 0 i.succ
    simp only [Fin.cases_zero, Fin.cases_succ, hs, hempty, List.not_mem_nil] at hlink
    have hf := quiet_message_future cfg f c hquiet 0 i.succ _ _ hlink
    have hb := (roundStart_le_budget cfg _ hp.root_limit).trans htime
    exact (not_lt_of_ge hb) hf
  have hnot : ¬ (c.workers 0).iteration < cfg.iterations := by
    intro hr
    have hall : ∀ i : Fin p.n, i ∈ (c.workers 0).arrived := by
      intro i
      rcases hp.control i with h | h | h | h
      · have hw := quiet_wake_future cfg f c hquiet i.succ
        rw [h.2.2.2.2] at hw
        exact False.elim ((not_lt_of_ge (show 0 ≤ c.time by positivity)) hw)
      · have hc := hp.pending i
        simp only [h.2.1, ite_true] at hc
        have hf := quiet_computation_future cfg f c hquiet i _ _ hc
        have hb : roundStart p cfg (c.workers i.succ).iteration + p.h i ≤ c.time :=
          (le_add_of_nonneg_right (show 0 ≤ uploadTime p cfg (c.workers i.succ).iteration by positivity)).trans
            ((worker_finish_le_budget cfg i _ h.1).trans htime)
        exact False.elim ((not_lt_of_ge hb) hf)
      · by_contra hnot
        have hlink := hp.links i.succ 0
        simp only [Fin.cases_succ, haligned i, h.2.2, hnot, true_and] at hlink
        have hf := quiet_message_future cfg f c hquiet i.succ 0 _ _ hlink
        have hb := (worker_finish_le_budget cfg i _ hr).trans htime
        exact (not_lt_of_ge hb) hf
      · have hs := haligned i
        omega
    exact hp.arrived_incomplete (Finset.eq_univ_iff_forall.mpr hall)
  have hr := hp.root_limit
  omega

lemma terminal_pipeline_output (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htime : c.time ≤ c.deadline)
    (hbudget : timeBudget p cfg ≤ c.deadline)
    (hterminal : step (system p f) (algorithm p cfg) c = none) :
    (algorithm p cfg).output (c.workers 0) = idealOutput p cfg f (selected, seed) := by
  obtain ⟨ht, hquiet⟩ := (DistributedExecution.step_terminal_iff (system p f) (algorithm p cfg) c htime).mp hterminal
  have hdone := quiet_pipeline_complete cfg f seed selected c hp (by simpa only [ht] using hbudget) hquiet
  change (c.workers 0).selected = _
  rw [hp.root.points.selected_point, ite_eq_left (show selected.val ≤ (c.workers 0).iteration by
    rw [hdone]
    exact selected.isLt.le)]
  rfl

end LongTails.Proofs.DashaDistributedPipeline
