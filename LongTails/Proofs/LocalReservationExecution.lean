import LongTails.Proofs.LocalReservationActions

namespace LongTails.Proofs.LocalReservationExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations (Frame Cursor due runnable posted consumed usedCount CompOK)
open LeonTranscript LeonClock LocalReservations

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : Fin p.n → List (Frame p)} {out : Point p} {limit : Time}

lemma due_before (cert : Certified g seed limit rows) (i : Fin p.n) (a b : Cursor (rows i))
    (busy : Bool) (send : Frame p) (after : List (Frame p)) (hb : b.rest = send :: after)
    (hpos : a.past.length ≤ b.past.length) : due limit a.rest busy ≤ send.finish := by
  obtain ⟨mid,hm⟩ := LeonReservations.before a b hpos
  have hl := a.layout.symm.trans b.layout
  rw [← hm,List.append_assoc] at hl
  have he := List.append_cancel_left hl
  rw [hb] at he
  rw [he]
  have hpre : rows i = a.past ++ mid ++ send :: after := by rw [List.append_assoc,← he]; exact a.layout
  generalize a.past = pre at hpre
  clear he hl hm
  induction mid generalizing pre busy with
  | nil =>
    have ord := (cert.ordered i pre send after (by simpa using hpre)).1
    cases busy <;> simp [due,ord]
  | cons c rest ih =>
    have ord := cert.ordered i pre c (rest ++ send :: after) (by simpa [List.append_assoc] using hpre)
    have hh := ih false (pre ++ [c]) (by simpa [List.append_assoc] using hpre)
    cases busy
    · exact ord.1.trans (ord.2.trans hh)
    · exact ord.2.trans hh

lemma ready (cert : Certified g seed limit rows) (c : LeonClock.RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (hmin : ∀ j, due limit (cur i).rest (c.workers i).busy ≤ due limit (cur j).rest (c.workers j).busy)
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
      · obtain ⟨hdate,beforeS,send,afterS,hsource,hearly,hprefix⟩ := cert.receive i _ _ _ hrow j bits ha
        let stop : Cursor (rows j) := ⟨beforeS ++ [send], afterS, by simpa [List.append_assoc] using hsource⟩
        have hlen : stop.past.length ≤ (cur j).past.length := by
          by_contra hn
          have hpre : (cur j).past.length ≤ beforeS.length := by
            simp only [stop,List.length_append,List.length_singleton] at hn
            omega
          let atSend : Cursor (rows j) := ⟨beforeS,send :: afterS,hsource⟩
          have hle := due_before cert j (cur j) atSend (c.workers j).busy send afterS rfl hpre
          have hh := hmin j
          have hre : a.start ≤ due limit (cur i).rest (c.workers i).busy := by
            cases (c.workers i).busy <;> simp [due,hrest,(cert.ordered i _ _ _ hrow).1]
          exact hearly.not_ge (hre.trans (hh.trans hle))
        obtain ⟨later,hl⟩ := hprefix.trans (posted_prefix (LeonReservations.before stop (cur j) hlen) j i)
        have hs : posted (cur j).past j i = consumed (cur i).past j i ++ (a.delivery,bits) :: later := by
          simpa [List.append_assoc] using hl.symm
        have hlink := h.link j i
        rw [hin] at hlink
        obtain ⟨m,hm,hready,_⟩ := LeonLinkLedger.available hlink _ hs
        apply Or.inl (Or.inr ((LeonNetwork.mail_ready p _ _).mpr ⟨(j,i),m,hm,?_⟩))
        apply hready.trans (hdate.trans _)
        cases hb : (c.workers i).busy
        · simp [due]
        · simpa [due,hrest] using (cert.ordered i _ _ _ hrow).1
      · exact Or.inr (by simpa only [T,hrest] using hw (by simpa [runnable,hpr] using hin))

lemma cap_le (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) (i : Fin p.n) :
    due limit (cur i).rest (c.workers i).busy ≤ limit := by
  cases hr : (cur i).rest with
  | nil => rfl
  | cons a rest =>
    have hrow := (cur i).layout.trans (congrArg (List.append _) hr)
    have hb := cert.bounded i a (show a ∈ rows i by rw [hrow]; simp)
    cases (c.workers i).busy
    · exact (cert.ordered i _ _ _ hrow).1.trans hb
    · exact hb

lemma minimum (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) (hn : ∃ j, (cur j).rest ≠ []) :
    ∃ i, (cur i).rest ≠ [] ∧ ∀ j, due limit (cur i).rest (c.workers i).busy ≤
      due limit (cur j).rest (c.workers j).busy := by
  classical
  let pending := Finset.univ.filter fun i => (cur i).rest ≠ []
  have hne : pending.Nonempty := by obtain ⟨j,hj⟩ := hn; exact ⟨j,by simp [pending,hj]⟩
  obtain ⟨i,hin,hmin⟩ := Finset.exists_min_image pending
    (fun j => due limit (cur j).rest (c.workers j).busy) hne
  refine ⟨i,(Finset.mem_filter.mp hin).2,fun j => ?_⟩
  by_cases hj : (cur j).rest = []
  · simpa [hj,due] using cap_le cert c cur i
  · exact hmin j (by simp [pending,hj])

lemma notified (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i,ev),o)) :
    ∃ a : Cursor (rows i), Consistent g P seed rows out
      (Function.update c.workers i (update p (c.workers i) ev)) o (Function.update cur i a) ∧
      c.time ≤ due limit a.rest (update p (c.workers i) ev).busy := by
  obtain ho | ⟨rfl,rfl,_⟩ := DistributedExecution.event_cases _ _ _ _ _ _ _ he
  · rcases DistributedExecution.oracle_answer_cases _ _ _ _ _ _ ho with
      ⟨val, os, rfl, hreply, rfl⟩ | ⟨⟨j,bits⟩, mail, rfl, hreply, rfl⟩
    · obtain ⟨a, hn, hd⟩ := LocalReservationActions.computed cert h.toConsistent i c.time val os hreply
      exact ⟨a, hn, (h.time i).trans hd⟩
    · exact ⟨cur i, by simpa using LocalReservationActions.received h.toConsistent j i bits c.time mail hreply,
        h.time i⟩
  · exact ⟨cur i, by simpa [update] using h.toConsistent, h.time i⟩

lemma event_valid (cert : Certified g seed limit rows) (c : RunState g P limit)
    (cur : (i : Fin p.n) → Cursor (rows i)) (h : Valid g P limit seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (algorithm p limit) c c.time = some ((i,ev),o)) :
    ∃ cur', Valid g P limit seed rows out (eventStep g P limit c i ev o) cur' := by
  obtain ⟨b, hm, ht⟩ := notified cert c cur h i ev o he
  let w := update p (c.workers i) ev
  obtain ⟨a,hnew,hdate⟩ := LocalReservationActions.act cert hm i c.time (by simpa using ht)
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
    (hd : c.deadline = limit) (ht : c.time ≤ c.deadline) (cur : (i : Fin p.n) → Cursor (rows i))
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
      · obtain ⟨i,hni,hmin⟩ := minimum cert c cur hall
        have hready := ready cert c cur h i hmin hni
        exact (hn.2 ⟨h.time i, (cap_le cert c cur i).trans_eq hd.symm, Or.inr hready⟩).trans (hmin j)
      · have hj : (cur j).rest = [] := by by_contra hne; exact hall ⟨j,hne⟩
        simpa [due,hj,hd] using hn.1.2.1
    · intro j hr; exact (h.wake j hr).trans hn.1.1

lemma terminal_output (cert : Certified g seed limit rows) (c : RunState g P limit)
    (hd : c.deadline = limit) (ht : c.time ≤ c.deadline)
    (cur : (i : Fin p.n) → Cursor (rows i)) (h : Valid g P limit seed rows out c cur)
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
      obtain ⟨i,hni,hmin⟩ := minimum cert c cur ⟨j,hy⟩
      have hav := ready cert c cur h i hmin hni
      have hle := cap_le cert c cur i
      have heq : due limit (cur i).rest (c.workers i).busy = c.time :=
        le_antisymm (hle.trans_eq (ht'.trans hd).symm) (h.time i)
      change (event O A c _).isSome at hav
      simp [heq,he] at hav
    have htr := h.trace A.root
    rw [hall,List.map_nil] at htr
    have hp := LeonLocalTrace.done htr
    change (match (c.workers A.root).program with | .finish x => x | _ => p.x0) = out
    rw [hp]

end LongTails.Proofs.LocalReservationExecution
