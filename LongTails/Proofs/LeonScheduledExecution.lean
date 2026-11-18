import LongTails.Proofs.LeonReservations
import LongTails.Proofs.LeonActions
import LongTails.Proofs.LeonTermination

namespace LongTails.Proofs.LeonReadiness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations LeonTranscript

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : List (Frame p)} {out : Point p} {limit : Time}

lemma past_due (cert : Certified g seed limit rows) (pre mid tail : List (Frame p)) (b : Bool)
    (hr : rows = pre ++ mid ++ tail) :
    due limit (mid ++ tail) false ≤ due limit tail b := by
  induction mid generalizing pre with
  | nil =>
    cases tail with
    | nil => rfl
    | cons c rest =>
      cases b
      · rfl
      · exact (cert.ordered pre c rest (by simpa using hr)).1
  | cons c mid ih =>
    have hh := cert.ordered pre c (mid ++ tail) (by simpa [List.append_assoc] using hr)
    exact hh.1.trans (hh.2.trans (ih (pre ++ [c]) (by simpa [List.append_assoc] using hr)))

def pos (a : Cursor rows) (b : Bool) := 2 * a.past.length + b.toNat

lemma due_mono (cert : Certified g seed limit rows) (a b : Cursor rows) (v w : Bool)
    (h : pos a v ≤ pos b w) : due limit a.rest v ≤ due limit b.rest w := by
  have hl : a.past.length ≤ b.past.length := by cases v <;> cases w <;> simp [pos] at h <;> omega
  obtain ⟨mid, hm⟩ := before a b hl
  have hr := a.layout.symm.trans b.layout
  rw [← hm, List.append_assoc] at hr
  have he := List.append_cancel_left hr
  rw [he]
  cases mid with
  | nil =>
    simp only [List.append_nil] at hm
    cases v <;> cases w <;> simp only [List.nil_append]
    · rfl
    · exact past_due cert b.past [] b.rest true (by simpa using b.layout)
    · simp [pos, hm] at h
    · rfl
  | cons c mid =>
    have hn := cert.ordered a.past c (mid ++ b.rest) (by simpa [he] using a.layout)
    apply le_trans (b := c.finish)
    · cases v
      · exact hn.1
      · rfl
    · exact hn.2.trans (past_due cert (a.past ++ [c]) mid b.rest w
        (by simpa [List.append_assoc, ← hm] using b.layout))

lemma ready (cert : Certified g seed limit rows) (c : LeonClock.RunState g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (hmin : ∀ j, pos (cur i) (c.workers i).busy ≤ pos (cur j) (c.workers j).busy)
    (hn : (cur i).rest ≠ []) :
    (event (system p g P) (algorithm p limit) c (due limit (cur i).rest (c.workers i).busy)).isSome := by
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready]
  let T := due limit (cur i).rest (c.workers i).busy
  have hw (hr : runnable (c.workers i)) : ∃ j, c.wakeTime j ≤ T := ⟨i, (h.wake i hr).trans (h.time i)⟩
  cases hrest : (cur i).rest with
  | nil => exact False.elim (hn hrest)
  | cons a tail =>
    have hrow := (cur i).layout.trans (congrArg (List.append (cur i).past) hrest)
    have ht := h.trace i
    rw [hrest, List.map_cons] at ht
    cases ha : a.op i with
    | sample q vals =>
      rw [ha] at ht
      obtain ⟨_, hpr, _⟩ := LeonLocalTrace.sample ht
      cases hb : (c.workers i).busy with
      | false => exact Or.inr (by simpa only [T,hrest,hb] using hw (by simp [runnable,hpr,hb]))
      | true =>
        have hc := (h.compute i).2.2
        simp only [hb, ite_true] at hc
        obtain ⟨a',tail',q',vals',t,hr,_,hp,hfin⟩ := hc
        simp only [hrest,List.cons.injEq] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact Or.inl (Or.inl ⟨i, (LeonNetwork.compute_ready p g i _ _).mpr ⟨_, hp, hfin⟩⟩)
    | send j bits =>
      rw [ha] at ht
      obtain ⟨_,hpr,_⟩ := LeonLocalTrace.send ht
      exact Or.inr (by simpa only [T,hrest] using hw (by simp [runnable,hpr]))
    | receive j bits =>
      rw [ha] at ht
      obtain ⟨_,hpr,_⟩ := LeonLocalTrace.receive ht
      by_cases hin : (c.workers i).inbox j = []
      · have hlen : (cur i).past.length ≤ (cur j).past.length := by
          have hh := hmin j
          cases he : (c.workers i).busy <;> cases hf : (c.workers j).busy <;> simp [pos,he,hf] at hh <;> omega
        obtain ⟨more, hmore⟩ := before _ _ hlen
        obtain ⟨hdate, prior⟩ := cert.receive _ _ _ hrow i j bits ha
        obtain ⟨later, hl⟩ := prior
        have hs : posted (cur j).past j i = consumed (cur i).past j i ++
            (a.delivery,bits) :: (later ++ posted more j i) := by
          calc
            _ = posted ((cur i).past ++ more) j i := congrArg (fun l => posted l j i) hmore.symm
            _ = posted (cur i).past j i ++ posted more j i := List.flatMap_append
            _ = _ := by rw [← hl]; simp [List.append_assoc]
        have hlink := h.link j i
        rw [hin] at hlink
        obtain ⟨m,hm,hready,_⟩ := LeonLinkLedger.available hlink _ hs
        apply Or.inl (Or.inr ((LeonNetwork.mail_ready p _ _).mpr ⟨(j,i),m,hm,?_⟩))
        apply hready.trans (hdate.trans _)
        cases hb : (c.workers i).busy
        · simp [due]
        · simpa [due,hrest] using (cert.ordered _ _ _ hrow).1
      · exact Or.inr (by simpa only [T,hrest] using hw (by simpa [runnable,hpr] using hin))

end LongTails.Proofs.LeonReadiness

namespace LongTails.Proofs.LeonExecutionInvariant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations LeonReadiness LeonClock

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : List (Frame p)} {out : Point p} {limit : Time}

lemma minimum (c : RunState g P limit) (cur : Fin p.n → Cursor rows)
    (hn : ∃ j, (cur j).rest ≠ []) :
    ∃ i, (cur i).rest ≠ [] ∧ ∀ j, pos (cur i) (c.workers i).busy ≤ pos (cur j) (c.workers j).busy := by
  obtain ⟨j,hj⟩ := hn
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun k => pos (cur k) (c.workers k).busy)
    Finset.univ_nonempty
  refine ⟨i, ?_, fun k => hi k (Finset.mem_univ _)⟩
  intro he
  have hj' := congrArg List.length (cur j).layout
  have hi' := congrArg List.length (cur i).layout
  have hh := hi j (Finset.mem_univ _)
  have hn' := List.length_pos_iff.mpr hj
  simp only [List.length_append, he, List.length_nil, Nat.add_zero] at hj' hi'
  cases hbi : (c.workers i).busy <;> cases hbj : (c.workers j).busy <;> simp [pos,hbi,hbj] at hh <;> omega

lemma notified (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i,ev),o)) :
    ∃ a : Cursor rows, Consistent g P seed rows out
      (Function.update c.workers i (update p (c.workers i) ev)) o (Function.update cur i a) ∧
      c.time ≤ due limit a.rest (update p (c.workers i) ev).busy := by
  obtain ho | ⟨rfl,rfl,_⟩ := DistributedExecution.event_cases _ _ _ _ _ _ _ he
  · rcases DistributedExecution.oracle_answer_cases _ _ _ _ _ _ ho with
      ⟨val, os, rfl, hreply, rfl⟩ | ⟨⟨j,bits⟩, mail, rfl, hreply, rfl⟩
    · obtain ⟨a, hn, hd⟩ := LeonNotifications.computed cert h.toConsistent i c.time val os hreply
      exact ⟨a, hn, (h.time i).trans hd⟩
    · exact ⟨cur i, by simpa using LeonNotifications.received h.toConsistent j i bits c.time mail hreply,
        h.time i⟩
  · exact ⟨cur i, by simpa [update] using h.toConsistent, h.time i⟩

lemma event_valid (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i,ev),o)) :
    ∃ cur', Valid g P limit seed rows out (eventStep g P limit c i ev o) cur' := by
  obtain ⟨b, hm, ht⟩ := notified cert c cur h i ev o he
  let w := update p (c.workers i) ev
  obtain ⟨a,hnew,hdate⟩ := LeonActions.act cert hm i c.time (by simpa using ht)
  refine ⟨Function.update cur i a, ?_, ?_, ?_⟩
  · simpa only [Function.update_self, Function.update_idem,eventStep] using hnew
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [eventStep] using hdate
    · simpa [eventStep,Function.update_of_ne hj] using h.time j
  · intro j hr
    by_cases hj : j = i
    · subst j
      have hh : runnable (query p w).2 := by simpa [eventStep,w] using hr
      simpa [eventStep,w] using LeonActions.runnable_query w c.time limit hh
    · simpa [eventStep,Function.update_of_ne hj] using h.wake j (by
        simpa [eventStep,Function.update_of_ne hj] using hr)

lemma step_valid (cert : Certified g seed limit rows) (c d : RunState g P limit)
    (hd : c.deadline = limit) (ht : c.time ≤ c.deadline) (cur : Fin p.n → Cursor rows)
    (h : Valid g P limit seed rows out c cur) (hs : step (system p g P) (algorithm p limit) c = some d) :
    ∃ cur', Valid g P limit seed rows out d cur' := by
  let O := system p g P
  let A := algorithm p limit
  cases he : event O A c c.time with
  | some v =>
    rcases v with ⟨⟨i,ev⟩,o⟩
    have heq := Option.some.inj (hs.symm.trans (step_event g P limit c i ev o ht he))
    rw [heq]
    exact event_valid cert c cur h i ev o he
  | none =>
    change step O A c = some d at hs
    simp only [step, ite_eq_right (not_lt.mpr ht), he] at hs
    split_ifs at hs with ht'
    cases hs
    let ntime := nextTime (event O A c) c.time c.deadline
    have hn := DistributedExecution.nextTime_spec _ _ _ (LeonNetwork.next_exists p g P A c ht)
    refine ⟨cur, h.toConsistent, ?_, ?_⟩
    · intro j
      by_cases hall : ∃ i, (cur i).rest ≠ []
      · obtain ⟨i,hni,hmin⟩ := minimum c cur hall
        have hready := ready cert c cur h i hmin hni
        have hbefore : due limit (cur i).rest (c.workers i).busy ≤ limit := by
          cases hh : (cur i).rest with
          | nil => rfl
          | cons a rest =>
            have ha : a ∈ rows := by
              have heq := (cur i).layout.trans (congrArg (List.append (cur i).past) hh)
              exact (congrArg (fun xs => a ∈ xs) heq).mpr (by simp)
            have hb := cert.bounded a ha
            cases (c.workers i).busy
            · exact (cert.ordered _ _ _ ((cur i).layout.trans (congrArg (List.append _) hh))).1.trans hb
            · exact hb
        exact (hn.2 ⟨h.time i, hbefore.trans_eq hd.symm, Or.inr hready⟩).trans
          (due_mono cert _ _ _ _ (hmin j))
      · have hj : (cur j).rest = [] := by by_contra hne; exact hall ⟨j,hne⟩
        simpa [due,hj,hd] using hn.1.2.1
    · intro j hr; exact (h.wake j hr).trans hn.1.1

end LongTails.Proofs.LeonExecutionInvariant

namespace LongTails.Proofs.LeonScheduledExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations LeonReadiness LeonClock LeonExecutionInvariant

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : List (Frame p)} {out : Point p} {limit : Time}

lemma terminal_output (cert : Certified g seed limit rows) (c : RunState g P limit)
    (hd : c.deadline = limit) (ht : c.time ≤ c.deadline)
    (cur : Fin p.n → Cursor rows) (h : Valid g P limit seed rows out c cur)
    (hs : step (system p g P) (algorithm p limit) c = none) :
    (algorithm p limit).output (c.workers (algorithm p limit).root) = out := by
  let O := system p g P
  let A := algorithm p limit
  change step O A c = none at hs
  cases he : event O A c c.time with
  | some v =>
    rcases v with ⟨⟨i,e⟩,o⟩
    have hh := hs.symm.trans (step_event g P limit c i e o ht he)
    contradiction
  | none =>
    have ht' : c.time = c.deadline := by simpa [step,not_lt.mpr ht,he] using hs
    have hall (j) : (cur j).rest = [] := by
      by_contra hy
      obtain ⟨i,hni,hmin⟩ := minimum c cur ⟨j,hy⟩
      have hav := ready cert c cur h i hmin hni
      have hle : due limit (cur i).rest (c.workers i).busy ≤ limit := by
        cases hr : (cur i).rest with
        | nil => rfl
        | cons a r =>
          have hrow := (cur i).layout.trans (congrArg (List.append _) hr)
          have ha := cert.bounded a (show a ∈ rows by rw [hrow]; simp)
          cases (c.workers i).busy
          · exact (cert.ordered _ _ _ hrow).1.trans ha
          · exact ha
      have heq : due limit (cur i).rest (c.workers i).busy = c.time :=
        le_antisymm (hle.trans_eq (ht'.trans hd).symm) (h.time i)
      change (event O A c _).isSome at hav
      simp [heq,he] at hav
    have htr := h.trace A.root
    rw [hall,List.map_nil] at htr
    have hp := LeonLocalTrace.done htr
    change (match (c.workers A.root).program with | .finish x => x | _ => p.x0) = out
    rw [hp]

lemma execute (cert : Certified g seed limit rows) (ab : (algorithm p limit).Seed)
    (htr : ∀ i, LeonTranscript.Trace ((algorithm p limit).initial i ab).program
      (rows.map (fun c => c.op i)) out) :
    DistributedTemplate.execute (system p g P) (algorithm p limit) limit ab seed = out := by
  let A := algorithm p limit
  let O := system p g P
  let init := DistributedTemplate.initial O A limit (ab,seed)
  let start : Fin p.n → Cursor rows := fun _ => ⟨[],rows,rfl⟩
  have hinit : Valid g P limit seed rows out init start := by
    refine ⟨⟨htr,fun _ => ⟨rfl,rfl,rfl⟩,fun _ _ => LeonLinkLedger.empty⟩,fun _ => zero_le,
      fun _ _ => le_rfl⟩
  obtain ⟨k,hend⟩ := LeonTermination.finite g P limit ab seed limit le_rfl
  rw [DistributedExecution.execute_eq_terminal O A limit (ab,seed) k hend]
  have hrun (k : ℕ) (c : RunState g P limit) (hc : c.time ≤ c.deadline) (hd : c.deadline = limit)
      (cur : Fin p.n → Cursor rows) (h : Valid g P limit seed rows out c cur) :
      ∃ cur', Valid g P limit seed rows out (run O A k c) cur' := by
    induction k generalizing c cur with
    | zero => exact ⟨cur,h⟩
    | succ k ih =>
      cases hs : step O A c with
      | none => simpa [run,hs] using (show ∃ cs, Valid g P limit seed rows out c cs from ⟨cur,h⟩)
      | some d =>
        obtain ⟨cs,hcs⟩ := step_valid cert c d hd hc cur h hs
        simpa [run,hs] using ih d (DistributedExecution.step_time_le_deadline O A c d hc hs)
          ((DistributedExecution.step_deadline O A c d hs).trans hd) cs hcs
  obtain ⟨cs,hcs⟩ := hrun k init zero_le rfl start hinit
  exact terminal_output cert _ (DistributedExecution.run_deadline O A init k)
    (DistributedExecution.run_time_le_deadline O A init k zero_le) cs hcs hend

end LongTails.Proofs.LeonScheduledExecution
