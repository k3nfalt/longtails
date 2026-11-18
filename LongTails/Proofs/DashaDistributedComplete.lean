import LongTails.Proofs.DashaDistributedReceive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedComplete

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedTiming
open LongTails.Proofs.DashaDistributedPipeline
open LongTails.Proofs.DashaDistributedWake
open LongTails.Proofs.DashaDistributedBroadcast
open LongTails.Proofs.DashaDistributedReceive

variable {p : Params}

noncomputable def completedRoot (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (s : State p) : State p :=
  { advance p cfg s (fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j) with
    code := fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j
    outbox := some (broadcastMessage cfg f seed s.iteration)
    targets := List.finRange p.n }

lemma accept_complete (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (s : State p) (hr : RootData cfg f seed selected s)
    (hk : s.iteration < cfg.iterations) (i : Fin p.n) (hi : i ∉ s.arrived)
    (hall : insert i s.arrived = Finset.univ) :
    accept p cfg s i.succ (workerMessage cfg f seed s.iteration i ++ List.replicate clockBits false) =
      completedRoot cfg f seed s := by
  have hw := hexact.worker _ hk i (List.replicate clockBits false)
  have hb := hexact.broadcast _ hk []
  simp only [List.append_nil] at hb
  simp only [accept, Fin.cases_succ, ite_eq_left hi, hr.randomness, hw, hall, ite_true]
  rw [total_insert cfg f seed selected s hr hexact hk i hi hall]
  change { advance p cfg s (LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth
      (broadcastMessage cfg f seed s.iteration)) with
    code := fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j
    outbox := some (broadcastMessage cfg f seed s.iteration)
    targets := List.finRange p.n } = _
  rw [hb]
  rfl

noncomputable def afterComplete (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (c : ExecutionState (system p f) (algorithm p cfg)) (i : Fin p.n) :
    ExecutionState (system p f) (algorithm p cfg) :=
  { c with
    workers := Function.update c.workers 0 (completedRoot cfg f seed (c.workers 0))
    wakeTime := Function.update c.wakeTime 0 c.time
    turn := 1
    oracle := { c.oracle with communication := {
      messages := Function.update c.oracle.communication.messages i.succ
        (Function.update (c.oracle.communication.messages i.succ) 0 none) } } }

lemma complete_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed) (i : Fin p.n)
    (hi : i ∉ (c.workers 0).arrived) (hall : insert i (c.workers 0).arrived = Finset.univ)
    (haligned : (c.workers i.succ).iteration = (c.workers 0).iteration)
    (hs : (c.workers i.succ).sent = true)
    (htime : c.time = roundStart p cfg (c.workers 0).iteration + p.h i +
      uploadTime p cfg (c.workers 0).iteration) :
    Pipeline cfg f seed selected (afterComplete cfg f seed c i) := by
  classical
  have hz : (0 : Fin (p.n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← haligned]
    exact sent_iteration_lt cfg f seed selected c hp i hs
  obtain ⟨hfinish, ha⟩ := last_arrival_time cfg f seed selected c hp i haligned htime hall
  have hmem (j : Fin p.n) (hj : j ≠ i) : j ∈ (c.workers 0).arrived := by
    have hm : j ∈ insert i (c.workers 0).arrived := by rw [hall]; exact Finset.mem_univ j
    simpa only [Finset.mem_insert, hj, false_or] using hm
  refine {
    root := ?_, workers := ?_, root_limit := ?_, outbox := ?_, arrived_incomplete := ?_
    rounds := ?_, behind := ?_, control := ?_, root_pending := ?_, pending := ?_
    arrived_current := ?_, arrived_time := ?_, links := ?_ }
  · simp only [afterComplete, Function.update_self]
    rw [← accept_complete cfg f seed selected hexact _ hp.root hk i hi hall]
    exact accept_root_data cfg f seed selected hexact _ hp.root hk i hi
  · intro j
    simpa only [afterComplete, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.workers j
  · simpa only [afterComplete, Function.update_self, completedRoot, advance] using Nat.succ_le_of_lt hk
  · constructor
    · simp [afterComplete, completedRoot, advance, p.n.ne_zero]
    · simpa only [afterComplete, Function.update_self, completedRoot] using List.nodup_finRange p.n
    · intro j _
      simp [afterComplete, completedRoot, advance, ha j]
    · simp [afterComplete]
    · intro _
      simpa only [afterComplete, Function.update_self, completedRoot, advance] using hfinish
  · let : Nonempty (Fin p.n) := ⟨⟨0, p.n.pos⟩⟩
    simpa only [afterComplete, Function.update_self, completedRoot, advance] using
      (Finset.univ_nonempty (α := Fin p.n)).ne_empty.symm
  · intro j
    simp [afterComplete, completedRoot, advance, ha j]
  · intro j _
    simp only [afterComplete, Function.update_of_ne (Fin.succ_ne_zero j)]
    by_cases hj : j = i
    · subst j
      exact hs
    · exact (hp.arrived_current j (hmem j hj)).2
  · intro j
    simpa only [afterComplete, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.control j
  · exact hp.root_pending
  · intro j
    simpa only [afterComplete, Function.update_of_ne (Fin.succ_ne_zero j)] using hp.pending j
  · simp [afterComplete, completedRoot, advance]
  · simp [afterComplete, completedRoot, advance]
  · intro source target
    refine Fin.cases ?_ (fun j => ?_) source
    · refine Fin.cases ?_ (fun j => ?_) target
      · simpa only [afterComplete, Function.update_of_ne hz, Fin.cases_zero] using hp.links 0 0
      · have hold := hp.links 0 j.succ
        simp only [Fin.cases_zero, Fin.cases_succ, ha j, Nat.add_one_ne_self, false_and, ite_false] at hold
        simp [afterComplete, Function.update_of_ne hz, completedRoot, advance, hold]
    · by_cases hj : j = i
      · subst j
        by_cases ht : target = 0
        · subst target
          simp [afterComplete, completedRoot, advance, haligned]
        · have hold := hp.links i.succ target
          simp only [Fin.cases_succ, ht, false_and, ite_false] at hold
          simp [afterComplete, completedRoot, advance, ht, hold]
      · have hold := hp.links j.succ target
        simp only [Fin.cases_succ, hmem j hj, not_true_eq_false, and_false, ite_false] at hold
        simp [afterComplete, Function.update_of_ne (fun he => hj (Fin.succ_inj.mp he)), completedRoot,
          advance, ha j, hold]

lemma complete_step_eq (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next))
    (hall : insert i (c.workers 0).arrived = Finset.univ)
    (j : Fin p.n) (rest : List (Fin p.n)) (htargets : List.finRange p.n = j :: rest) :
    step (system p f) (algorithm p cfg) c = some (afterSend cfg f seed (afterComplete cfg f seed c i) j rest) := by
  classical
  obtain ⟨haligned, hs, hi, htime, hb⟩ := received_worker_facts cfg f seed selected c hp htimely i bits next hevent
  have hn : next = (afterComplete cfg f seed c i).oracle :=
    (received_at_finish cfg f c htimely i.succ 0 bits next hevent).2
  have hk : (c.workers 0).iteration < cfg.iterations := by
    rw [← haligned]
    exact sent_iteration_lt cfg f seed selected c hp i hs
  have ha : accept p cfg (c.workers 0) i.succ bits = completedRoot cfg f seed (c.workers 0) := by
    rw [hb, haligned]
    exact accept_complete cfg f seed selected hexact _ hp.root hk i hi hall
  have hcomplete := complete_pipeline cfg f seed selected c hp hexact i hi hall haligned hs
    (by simpa only [haligned] using htime)
  have hq : (algorithm p cfg).query 0
      ((algorithm p cfg).update 0 (c.workers 0) ((algorithm p cfg).clock c.time)
        (.received (.received i.succ bits))) ((algorithm p cfg).clock c.time) =
      (.communicate (j.succ, broadcastMessage cfg f seed (c.workers 0).iteration),
        { completedRoot cfg f seed (c.workers 0) with
          targets := rest
          outbox := if rest = [] then none else some (broadcastMessage cfg f seed (c.workers 0).iteration) }) := by
    change (algorithm p cfg).query 0 (accept p cfg (c.workers 0) i.succ bits) 0 = _
    rw [ha]
    simp [algorithm, completedRoot, htargets]
  have hempty : (afterComplete cfg f seed c i).oracle.communication.messages 0 j.succ = none := by
    rw [hcomplete.links 0 j.succ]
    simp [afterComplete, completedRoot]
  have hcomm : (system p f).communication.submit (afterComplete cfg f seed c i).oracle.communication c.time 0
      (j.succ, broadcastMessage cfg f seed (c.workers 0).iteration ++ List.replicate clockBits false) =
      { messages := Function.update (afterComplete cfg f seed c i).oracle.communication.messages 0
          (Function.update ((afterComplete cfg f seed c i).oracle.communication.messages 0) j.succ
            (some (c.time, broadcastMessage cfg f seed (c.workers 0).iteration ++ List.replicate clockBits false))) } := by
    simp [system, communication, LongTails.Setups.StarNetwork.communication, hempty]
  simp only [step, ite_eq_right (not_lt.mpr hdeadline), hevent, hq, hn, hcomm]
  simp only [afterSend, afterComplete, Function.update_self, Function.update_idem, completedRoot, advance,
    Nat.add_sub_cancel, Fin.val_zero, zero_add]

lemma complete_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next))
    (hall : insert i (c.workers 0).arrived = Finset.univ) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  obtain ⟨haligned, hs, hi, htime, _⟩ := received_worker_facts cfg f seed selected c hp htimely i bits next hevent
  have hcomplete := complete_pipeline cfg f seed selected c hp hexact i hi hall haligned hs
    (by simpa only [haligned] using htime)
  cases ht : List.finRange p.n with
  | nil => have hl := congrArg List.length ht; simp at hl
  | cons j rest =>
      refine ⟨_, complete_step_eq cfg f seed selected c hp hexact htimely hdeadline i bits next hevent hall j rest ht,
        send_pipeline cfg f seed selected _ hcomplete j rest ?_⟩
      simpa only [afterComplete, Function.update_self, completedRoot] using ht

lemma upload_step_pipeline (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (c : ExecutionState (system p f) (algorithm p cfg))
    (hp : Pipeline cfg f seed selected c) (hexact : TransportExact cfg f seed)
    (htimely : Timely cfg f c) (hdeadline : c.time ≤ c.deadline)
    (i : Fin p.n) (hpos : 0 < p.h i) (bits : List Bool) (next : OracleState (system p f))
    (hevent : event (system p f) (algorithm p cfg) c c.time =
      some ((0, .received (.received i.succ bits)), next)) :
    ∃ nextState, step (system p f) (algorithm p cfg) c = some nextState ∧
      Pipeline cfg f seed selected nextState := by
  by_cases hall : insert i (c.workers 0).arrived = Finset.univ
  · exact complete_step_pipeline cfg f seed selected c hp hexact htimely hdeadline i bits next hevent hall
  · exact partial_step_pipeline cfg f seed selected c hp hexact htimely hdeadline i hpos bits next hevent hall

end LongTails.Proofs.DashaDistributedComplete
