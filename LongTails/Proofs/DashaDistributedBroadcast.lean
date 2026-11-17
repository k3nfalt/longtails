import LongTails.Proofs.DashaDistributedWake

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedBroadcast

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedWake

variable {p : Params}

noncomputable def afterSend (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) (rest : List (Fin p.n)) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers 0 { c.workers 0 with
      targets := rest
      outbox := if rest = [] then none else some (broadcastMessage cfg f seed ((c.workers 0).iteration - 1)) }
    wakeTime := Function.update c.wakeTime 0 c.time
    turn := 1
    oracle := { c.oracle with communication := {
      messages := Function.update c.oracle.communication.messages 0
        (Function.update (c.oracle.communication.messages 0) i.succ
          (some (c.time, broadcastMessage cfg f seed ((c.workers 0).iteration - 1) ++ List.replicate clockBits false))) } } }

lemma send_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n) (rest : List (Fin p.n))
    (ht : (c.workers 0).targets = i :: rest) :
    Pipeline cfg f seed selected (afterSend cfg f seed c i rest) := by
  classical
  have hn : i ∉ rest := (List.nodup_cons.mp (ht ▸ hp.outbox.nodup)).1
  have hi : (c.workers i.succ).iteration + 1 = (c.workers 0).iteration :=
    hp.outbox.queued i (by simp [ht])
  have htime : c.time = roundStart p cfg (c.workers 0).iteration :=
    hp.outbox.finish (by simp [ht])
  refine {
    root := ?_, workers := ?_, root_limit := ?_, outbox := ?_, arrived_incomplete := ?_
    rounds := ?_, behind := ?_, control := ?_, root_pending := ?_, pending := ?_
    arrived_current := ?_, arrived_time := ?_, links := ?_ }
  · have hr := hp.root
    simp only [afterSend, Function.update_self]
    exact ⟨⟨hr.points.point, hr.points.index, hr.points.selected_point⟩, hr.randomness, hr.code, hr.accumulator⟩
  · intro j
    simpa only [afterSend, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simpa only [afterSend, Function.update_self] using hp.root_limit
  · constructor
    · simp [afterSend]
    · simpa only [afterSend, Function.update_self] using (List.nodup_cons.mp (ht ▸ hp.outbox.nodup)).2
    · intro j hj
      simp only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] at hj ⊢
      exact hp.outbox.queued j (by simp [ht, hj])
    · intro _
      simp [afterSend]
    · intro _
      simpa only [afterSend, Function.update_self] using htime
  · simpa only [afterSend, Function.update_self] using hp.arrived_incomplete
  · intro j
    simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.rounds j
  · intro j
    simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.behind j
  · intro j
    simpa only [afterSend, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [afterSend, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · intro j hj
    simp only [afterSend, Function.update_self] at hj
    simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.arrived_current j hj
  · intro j hj
    simp only [afterSend, Function.update_self] at hj
    simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.arrived_time j hj
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm,
          Fin.cases_zero] using hp.links 0 0
      · by_cases hj : j = i
        · subst j
          simp [afterSend, hi, hn, htime]
        · have hji : j.succ ≠ i.succ := fun he => hj (Fin.succ_inj.mp he)
          simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j),
            Function.update_of_ne hji, Fin.cases_zero, Fin.cases_succ, ht, List.mem_cons,
            hj, false_or] using hp.links 0 j.succ
    · simpa only [afterSend, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero j),
        Fin.cases_succ] using hp.links j.succ target

lemma send_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (rest : List (Fin p.n)) (ht : (c.workers 0).targets = i :: rest)
    (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((0, .wake), next)) :
    step (system p f) (algorithm p cfg) c = some (afterSend cfg f seed c i rest) := by
  classical
  have hn := (DistributedExecution.wake_event (system p f) (algorithm p cfg) c c.time 0 next hevent).1
  have ho : (c.workers 0).outbox = some (broadcastMessage cfg f seed ((c.workers 0).iteration - 1)) := by
    simpa only [ht, List.cons_ne_nil, ite_false] using hp.outbox.message
  have hq : (algorithm p cfg).query 0
      ((algorithm p cfg).update 0 (c.workers 0) ((algorithm p cfg).clock c.time) .wake)
      ((algorithm p cfg).clock c.time) =
      (.communicate (i.succ, broadcastMessage cfg f seed ((c.workers 0).iteration - 1)),
        { c.workers 0 with
          targets := rest
          outbox := if rest = [] then none else some (broadcastMessage cfg f seed ((c.workers 0).iteration - 1)) }) := by
    simp [algorithm, ho, ht]
  have hempty : c.oracle.communication.messages 0 i.succ = none := by
    rw [hp.links 0 i.succ]
    simp [ht]
  have hcomm : (system p f).communication.submit c.oracle.communication c.time 0
      (i.succ, broadcastMessage cfg f seed ((c.workers 0).iteration - 1) ++ List.replicate clockBits false) =
      { messages := Function.update c.oracle.communication.messages 0
          (Function.update (c.oracle.communication.messages 0) i.succ
            (some (c.time, broadcastMessage cfg f seed ((c.workers 0).iteration - 1) ++ List.replicate clockBits false))) } := by
    simp [system, communication, LongTails.Setups.StarNetwork.communication, hempty]
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn, hcomm]
  rfl

lemma root_wake_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((0, .wake), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  cases ht : (c.workers 0).targets with
  | nil => exact root_idle_pipeline cfg f seed selected c hp hdeadline next hevent ht
  | cons i rest => exact ⟨_, send_step_eq cfg f seed selected c hp hdeadline i rest ht next hevent,
      send_pipeline cfg f seed selected c hp i rest ht⟩

lemma wake_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hdeadline : c.time ≤ c.deadline)
    (v : Fin (p.n + 1)) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time = some ((v, .wake), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  induction v using Fin.cases with
  | zero => exact root_wake_pipeline cfg f seed selected c hp hdeadline next hevent
  | succ i => exact worker_wake_pipeline cfg f seed selected c hp hdeadline i next hevent

lemma send_progress_strict (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n) (rest : List (Fin p.n))
    (ht : (c.workers 0).targets = i :: rest) :
    workerProgress 0 (c.workers 0) <
      workerProgress 0 ((afterSend cfg f seed c i rest).workers 0) := by
  have hlen : (c.workers 0).targets.length ≤ p.n := by simpa using hp.outbox.nodup.length_le_card
  simp only [ht, List.length_cons] at hlen
  simp only [workerProgress, afterSend, Function.update_self, Fin.cases_zero, ht, List.length_cons]
  omega

lemma idle_wake_future (cfg : Config p) (f : Functions p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (v : Fin (p.n + 1))
    (ht : c.time ≤ timeBudget p cfg) :
    c.time < (afterIdle cfg f c v).wakeTime v := by
  simp only [afterIdle, Function.update_self]
  exact lt_of_lt_of_le (lt_of_le_of_lt ht (lt_add_of_pos_right _ (by norm_num))) (le_max_right _ _)

lemma upload_targets_empty (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (i : Fin p.n) (hpos : 0 < p.h i)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + p.h i +
      uploadTime p cfg (c.workers 0).iteration) : (c.workers 0).targets = [] := by
  by_contra hn
  have he := hp.outbox.finish hn
  have hlt : roundStart p cfg (c.workers 0).iteration < c.time := by
    rw [htime]
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hpos) (le_add_of_nonneg_right (by positivity))
  rw [he] at hlt
  exact lt_irrefl _ hlt

lemma received_upload_targets_empty (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (htimely : Timely cfg f c)
    (i : Fin p.n) (hpos : 0 < p.h i) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next)) :
    (c.workers 0).targets = [] := by
  obtain ⟨haligned, _, _, ht, _⟩ := received_worker_facts cfg f seed selected c hp htimely i bits next hevent
  apply upload_targets_empty cfg f seed selected c hp i hpos
  simpa only [haligned] using ht

end LongTails.Proofs.DashaDistributedBroadcast
