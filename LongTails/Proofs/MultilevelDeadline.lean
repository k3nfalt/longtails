import LongTails.Proofs.MultilevelWireTransitions

namespace LongTails.Proofs.MultilevelDeadline

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions

variable {p : Params}

abbrev Network (p : Params) : StarNetwork.Network p.n := ⟨fun i => 2*p.h i,p.l,p.b⟩
abbrev evalPair (g : Fin p.n → Point p → p.Ω → Point p) (i : Fin p.n)
    (q : Query p) (x : Samples p) (k : ℕ) := (g i q.1 (x i k), g i q.2 (x i k))

structure Context (p : Params) where
  t : Script p
  T : Time
  g : Fin p.n → Point p → p.Ω → Point p
  P : ProbabilityMeasure (Samples p)
  xs : Samples p
  seed : Selection p

noncomputable abbrev Context.A (u : Context p) := algorithm p u.t u.T
noncomputable abbrev Context.O (u : Context p) := system p u.g u.P
noncomputable abbrev Context.out (u : Context p) := reply u.t u.g u.xs
abbrev Context.Exec (u : Context p) := ExecutionState u.O u.A

def Forecast (u : Context p) (b : Book p) : Prop :=
  ∀ i, MultilevelWireState.Phase.within p u.t u.out i (b.pending i)

def Memory (u : Context p) (b : Book p) : Prop :=
  ∀ i j τ, b.pending i = .work j τ → b.memory i = payload u.t u.out j

structure Good (u : Context p) (b : Book p) (c : u.Exec) : Prop where
  valid : Valid u.t b
  memory : Memory u b
  forecast : Forecast u b
  workers : c.workers = nodes b u.seed u.out
  oracle : c.oracle = machine u.t u.g u.P u.xs b
  timely : MultilevelClock.Timely (Network p) (evalPair u.g) u.P u.A c
  frontier : b.issued < u.t.count → c.time ≤ u.t.start b.issued
  runnable : ready u.t (root b u.seed u.out) → c.wakeTime 0 ≤ c.time

lemma initial_good (u : Context p) (T : Time) : Good u {} (initial u.O u.A T (u.seed,u.xs)) := by
  refine ⟨initial_valid _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Memory]
  · simp [Forecast,MultilevelWireState.Phase.within]
  · funext v
    induction v using Fin.cases <;> rfl
  · unfold initial machine
    apply congrArg₂ OracleState.mk
    · funext v
      induction v using Fin.cases with
      | zero => rfl
      | succ i => simp [Context.O,system,StarNetwork.system,StarNetwork.computation,
          unitState,Phase.unused,count,MultilevelWireState.Phase.computing]
    · apply congrArg StarNetwork.CommunicationState.mk
      funext v w
      induction v using Fin.cases <;> induction w using Fin.cases <;> rfl
  · exact MultilevelClock.initial_timely _ _ _ _ _ _
  · intro _; exact zero_le
  · simp [initial]

noncomputable def workLeft (t : Script p) (b : Book p) :=
  4*(t.count-b.issued) + ∑ i, (b.pending i).remaining

lemma remaining_update (b : Book p) (i : Fin p.n) (u : Phase) :
    (∑ a, (Function.update b.pending i u a).remaining) + (b.pending i).remaining =
      (∑ a, (b.pending a).remaining) + u.remaining := by
  rw [update_job, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.add_sum_erase (Finset.univ : Finset (Fin p.n)) (fun a => (b.pending a).remaining) (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

lemma launch_decreases (u : Context p) (b : Book p) (τ : Time) (hr : ready u.t (root b u.seed u.out)) :
    workLeft u.t (launch u.t b τ) < workLeft u.t b := by
  have h := remaining_update b (u.t.worker b.issued) (.down b.issued τ)
  have hf : b.pending (u.t.worker b.issued) = .idle := phase_idle hr.2.1
  have hi := hr.1
  change b.issued < u.t.count at hi
  simp only [workLeft,launch,Phase.remaining, hf] at h ⊢
  omega

lemma pending_due (u : Context p) (b : Book p) (hv : Valid u.t b) (sched : Timetable p u.t u.T)
    (hh : ∀ i, 0 < p.h i) (hnext : b.issued < u.t.count)
    (hn : ¬ready u.t (root b u.seed u.out)) :
    ∃ i j, (b.pending i).job = some j ∧ u.t.finish j ≤ u.t.start b.issued := by
  have he (j : ℕ) (hj : j < u.t.count) : u.t.start j < u.t.finish j := by
    have h := sched.service j hj (fun _ => []) (0,0)
    have hle : u.t.start j ≤ u.t.start j + wire p (u.t.request j (fun _ => [])) := le_add_of_nonneg_right zero_le
    exact (hle.trans_lt (lt_add_of_pos_right _ (mul_pos (by norm_num) (hh _)))).trans_le
      ((le_add_of_nonneg_right zero_le).trans h)
  by_contra! h
  apply hn
  refine ⟨hnext, ?_, ?_⟩
  · change (b.pending (u.t.worker b.issued)).job = none
    cases hp : (b.pending (u.t.worker b.issued)).job with
    | none => rfl
    | some j =>
      obtain ⟨hj,hw,_⟩ := hv.2.2.1 _ j hp
      exact ((h _ j hp).not_ge (sched.exclusive j b.issued hj hnext hw)).elim
  · intro j hj hd
    have hlt : j < b.issued := by
      by_contra! hr
      exact (he _ hj).not_ge (hd.trans (sched.ordered _ _ hr hj))
    rcases hv.2.2.2 j hlt with hdone | hp
    · simp [root,hdone]
    · exact ((h _ j hp).not_ge hd).elim

lemma pending_threshold (u : Context p) (b : Book p) (c : u.Exec) (hc : Good u b c)
    (i : Fin p.n) (j : ℕ) (hj : (b.pending i).job = some j) :
    ∃ τ ≤ u.t.finish j, c.time ≤ τ ∧ (event u.O u.A c τ).isSome := by
  have hf := hc.forecast i
  have ht := hc.timely
  have ho := hc.oracle
  cases hi : b.pending i with
  | idle => simp [hi,Phase.job] at hj
  | down k τ =>
    simp [hi,Phase.job] at hj
    subst k
    have hp : c.oracle.communication.messages 0 i.succ = some (τ, frame (payload u.t u.out j)) := by
      rw [ho]; simp [machine,wires_down,hi,MultilevelWireState.Phase.downlink]
    refine ⟨τ, ?_, ht.2.1 _ _ _ _ hp, ?_⟩
    · simp only [hi,MultilevelWireState.Phase.within] at hf
      exact (le_add_of_nonneg_right zero_le |>.trans (le_add_of_nonneg_right zero_le)).trans hf
    · apply (DistributedExecution.event_ready _ _ _ _).mpr
      apply Or.inl
      exact (DistributedExecution.oracle_ready _ _ _).mpr (Or.inr
        ((DistributedExecution.communication_ready (Seed := Samples p) (Network p) _ _).mpr ⟨_,_,_,_,hp,le_rfl⟩))
  | work k τ =>
    simp [hi,Phase.job] at hj
    subst k
    have hp : (c.oracle.computation i.succ).pending = some (τ,u.t.decode (payload u.t u.out j)) := by
      rw [ho]; change MultilevelWireState.Phase.computing u.t u.out (b.pending i) = _
      rw [hi]; rfl
    refine ⟨τ, ?_, ht.1 _ _ _ hp, ?_⟩
    · simp only [hi,MultilevelWireState.Phase.within] at hf
      exact (le_add_of_nonneg_right zero_le).trans hf
    · apply (DistributedExecution.event_ready _ _ _ _).mpr
      apply Or.inl
      exact (DistributedExecution.oracle_ready _ _ _).mpr (Or.inl ⟨i.succ,
        (DistributedExecution.computation_ready (Network p) (evalPair u.g) i _ _).mpr ⟨_,_,hp,le_rfl⟩⟩)
  | up k τ =>
    simp [hi,Phase.job] at hj
    subst k
    have hp : c.oracle.communication.messages i.succ 0 = some (τ,frame (u.out j)) := by
      rw [ho]; simp [machine,wires_up,hi,MultilevelWireState.Phase.uplink]
    refine ⟨τ, by simpa only [hi,MultilevelWireState.Phase.within] using hf,ht.2.1 _ _ _ _ hp,?_⟩
    apply (DistributedExecution.event_ready _ _ _ _).mpr
    apply Or.inl
    exact (DistributedExecution.oracle_ready _ _ _).mpr (Or.inr
      ((DistributedExecution.communication_ready (Seed := Samples p) (Network p) _ _).mpr ⟨_,_,_,_,hp,le_rfl⟩))

end LongTails.Proofs.MultilevelDeadline
