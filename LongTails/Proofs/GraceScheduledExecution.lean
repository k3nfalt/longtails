import LongTails.Proofs.GraceActions

namespace LongTails.Proofs.GraceScheduledExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open LeonProtocol (update query)
open LeonReservations (Frame Cursor due runnable before posted consumed)
open LeonReadiness (pos)
open GraceReservations
open GraceRouting (Routes)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} {A : Routes p S r}
  {g : Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : List (Frame p.base)} {out : Fin p.n → Point p} {limit horizon : Time}

lemma past_due (cert : Certified g seed horizon rows) (pre mid tail : List (Frame p.base)) (b : Bool)
    (hr : rows = pre ++ mid ++ tail) :
    due horizon (mid ++ tail) false ≤ due horizon tail b := by
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

lemma due_mono (cert : Certified g seed horizon rows) (a b : Cursor rows) (v w : Bool)
    (h : pos a v ≤ pos b w) : due horizon a.rest v ≤ due horizon b.rest w := by
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

lemma ready (cert : Certified g seed horizon rows) (c : GraceExecution.RunState A g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid A g P limit horizon seed rows out c cur) (i : Fin p.n)
    (hmin : ∀ j, pos (cur i) (c.workers i).busy ≤ pos (cur j) (c.workers j).busy)
    (hn : (cur i).rest ≠ []) :
    (event (system p g P) (GraceSgd.algorithm A limit) c (due horizon (cur i).rest (c.workers i).busy)).isSome := by
  rw [DistributedExecution.event_ready, DistributedExecution.oracle_ready]
  let T := due horizon (cur i).rest (c.workers i).busy
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
        exact Or.inl (Or.inl ⟨i, (LeonNetwork.compute_ready p.base (fun _ => g) i _ _).mpr ⟨_, hp, hfin⟩⟩)
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
        apply Or.inl (Or.inr ((LeonNetwork.mail_ready p.base _ _).mpr ⟨(j,i),m,hm,?_⟩))
        apply hready.trans (hdate.trans _)
        cases hb : (c.workers i).busy
        · simp [due]
        · simpa [due,hrest] using (cert.ordered _ _ _ hrow).1
      · exact Or.inr (by simpa only [T,hrest] using hw (by simpa [runnable,hpr] using hin))

lemma notified (cert : Certified g seed horizon rows) (c : GraceExecution.RunState A g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid A g P limit horizon seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (GraceSgd.algorithm A limit) c c.time = some ((i,ev),o)) :
    ∃ a : Cursor rows, Consistent g P seed rows out
      (Function.update c.workers i (update p.base (c.workers i) ev)) o (Function.update cur i a) ∧
      c.time ≤ due horizon a.rest (update p.base (c.workers i) ev).busy := by
  obtain ho | ⟨rfl,rfl,_⟩ := DistributedExecution.event_cases _ _ _ _ _ _ _ he
  · rcases DistributedExecution.oracle_answer_cases _ _ _ _ _ _ ho with
      ⟨val, os, rfl, hreply, rfl⟩ | ⟨⟨j,bits⟩, mail, rfl, hreply, rfl⟩
    · obtain ⟨a, hn, hd⟩ := GraceActions.computed cert h.toConsistent i c.time val os hreply
      exact ⟨a, hn, (h.time i).trans hd⟩
    · exact ⟨cur i, by simpa using GraceActions.received h.toConsistent j i bits c.time mail hreply,
        h.time i⟩
  · exact ⟨cur i, by simpa [update] using h.toConsistent, h.time i⟩

lemma event_valid (cert : Certified g seed horizon rows) (c : GraceExecution.RunState A g P limit)
    (cur : Fin p.n → Cursor rows) (h : Valid A g P limit horizon seed rows out c cur) (i : Fin p.n)
    (ev : Event (ComputeReply p) (CommReply p)) (o : OracleState (system p g P))
    (he : event (system p g P) (GraceSgd.algorithm A limit) c c.time = some ((i,ev),o)) :
    ∃ cur', Valid A g P limit horizon seed rows out (GraceExecution.eventState A g P limit c i ev o) cur' := by
  obtain ⟨b, hm, ht⟩ := notified cert c cur h i ev o he
  let w := update p.base (c.workers i) ev
  obtain ⟨a,hnew,hdate⟩ := GraceActions.act cert hm i c.time (by simpa using ht)
  refine ⟨Function.update cur i a, ?_, ?_, ?_⟩
  · simpa only [Function.update_self, Function.update_idem,GraceExecution.eventState] using hnew
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [GraceExecution.eventState] using hdate
    · simpa [GraceExecution.eventState,Function.update_of_ne hj] using h.time j
  · intro j hr
    by_cases hj : j = i
    · subst j
      have hh : runnable (query p.base w).2 := by simpa [GraceExecution.eventState,w] using hr
      simpa [GraceExecution.eventState,w] using LeonActions.runnable_query w c.time limit hh
    · simpa [GraceExecution.eventState,Function.update_of_ne hj] using h.wake j (by
        simpa [GraceExecution.eventState,Function.update_of_ne hj] using hr)

lemma least_cursor (c : GraceExecution.RunState A g P limit) (cur : Fin p.n → Cursor rows)
    (hn : ∃ j, (cur j).rest ≠ []) :
    ∃ i, (cur i).rest ≠ [] ∧ ∀ j, pos (cur i) (c.workers i).busy ≤ pos (cur j) (c.workers j).busy :=
  LeonExecutionInvariant.minimum (GraceExecution.referenceState A g P limit c) cur hn

lemma due_le (cert : Certified g seed horizon rows) (a : Cursor rows) (b : Bool) :
    due horizon a.rest b ≤ horizon := by
  cases hr : a.rest with
  | nil => rfl
  | cons c tail =>
    have hx := a.layout.trans (congrArg (List.append a.past) hr)
    have hfin := cert.bounded c (by rw [hx]; simp)
    cases b
    · exact (cert.ordered _ _ _ hx).1.trans hfin
    · exact hfin

lemma step_valid (cert : Certified g seed horizon rows) (c d : GraceExecution.RunState A g P limit)
    (hd : c.deadline ≤ horizon) (ht : c.time ≤ c.deadline) (cur : Fin p.n → Cursor rows)
    (h : Valid A g P limit horizon seed rows out c cur)
    (hs : step (system p g P) (GraceSgd.algorithm A limit) c = some d) :
    ∃ cur', Valid A g P limit horizon seed rows out d cur' := by
  let O := system p g P
  let alg := GraceSgd.algorithm A limit
  cases he : event O alg c c.time with
  | some val =>
    rcases val with ⟨⟨i,ev⟩,o⟩
    have heq := Option.some.inj (hs.symm.trans (GraceExecution.step_event A g P limit c i ev o ht he))
    rw [heq]
    exact event_valid cert c cur h i ev o he
  | none =>
    change step O alg c = some d at hs
    simp only [step, ite_eq_right (not_lt.mpr ht), he] at hs
    split_ifs at hs
    cases hs
    have hx := GraceExecution.next_exists A g P limit c ht
    have hn := DistributedExecution.nextTime_spec _ _ _ hx
    refine ⟨cur,h.toConsistent,?_,?_⟩
    · intro j
      by_cases someWork : ∃ i, (cur i).rest ≠ []
      · obtain ⟨i,hni,hm⟩ := least_cursor c cur someWork
        exact (DistributedExecution.nextTime_le_ready _ _ _ _ hx (h.time i) (ready cert c cur h i hm hni)).trans
          (due_mono cert _ _ _ _ (hm j))
      · have hj : (cur j).rest = [] := by by_contra hne; exact someWork ⟨j,hne⟩
        simpa [due,hj] using hn.1.2.1.trans hd
    · intro j hr; exact (h.wake j hr).trans hn.1.1

lemma enlarge (cert : Certified g seed limit rows) (hh : limit ≤ horizon) :
    Certified g seed horizon rows := by
  refine ⟨?_, fun c hc => (cert.bounded c hc).trans hh, cert.sample, cert.send, cert.receive⟩
  intro pre c rest he
  obtain ⟨hs, hf⟩ := cert.ordered pre c rest he
  refine ⟨hs, hf.trans ?_⟩
  cases rest with
  | nil => exact hh
  | cons => rfl

lemma run_valid (cert : Certified g seed horizon rows) (j : (GraceSgd.algorithm A limit).Seed)
    (htr : ∀ i, LeonTranscript.Trace ((GraceSgd.algorithm A limit).initial i j).program
      (rows.map fun c => c.op i) (out i)) (T : Time) (hT : T ≤ horizon) (k : ℕ) :
    ∃ cur, Valid A g P limit horizon seed rows out (run (system p g P) (GraceSgd.algorithm A limit)
      k (initial (system p g P) (GraceSgd.algorithm A limit) T (j,seed))) cur := by
  let O := system p g P
  let alg := GraceSgd.algorithm A limit
  have advance (k : ℕ) (c : GraceExecution.RunState A g P limit) (ht : c.time ≤ c.deadline)
      (hd : c.deadline ≤ horizon) (cur : Fin p.n → Cursor rows)
      (hv : Valid A g P limit horizon seed rows out c cur) :
      ∃ next, Valid A g P limit horizon seed rows out (run O alg k c) next := by
    induction k generalizing c cur with
    | zero => exact ⟨cur,hv⟩
    | succ k ih =>
      cases hs : step O alg c with
      | none => exact (by simpa [run,hs] using (show ∃ n, Valid A g P limit horizon seed rows out c n from ⟨cur,hv⟩))
      | some d =>
        obtain ⟨next, hn⟩ := step_valid cert c d hd ht cur hv hs
        simpa only [run,hs] using ih d (DistributedExecution.step_time_le_deadline O alg c d ht hs)
          ((DistributedExecution.step_deadline O alg c d hs).le.trans hd) next hn
  let cur : Fin p.n → Cursor rows := fun _ => ⟨[],rows,rfl⟩
  exact advance k _ zero_le hT cur ⟨⟨htr, fun _ => ⟨rfl,rfl,rfl⟩, fun _ _ => LeonLinkLedger.empty⟩,
    fun _ => zero_le, fun _ _ => le_rfl⟩

lemma finished (cert : Certified g seed limit rows) (c : GraceExecution.RunState A g P limit)
    (hd : c.deadline = limit) (ht : c.time ≤ c.deadline) (cur : Fin p.n → Cursor rows)
    (hv : Valid A g P limit limit seed rows out c cur)
    (hs : step (system p g P) (GraceSgd.algorithm A limit) c = none) : ∀ i, (cur i).rest = [] := by
  let O := system p g P
  let alg := GraceSgd.algorithm A limit
  change step O alg c = none at hs
  have he : event O alg c c.time = none := by
    cases hh : event O alg c c.time with
    | none => rfl
    | some v =>
      rcases v with ⟨⟨i,ev⟩,o⟩
      have hx := hs.symm.trans (GraceExecution.step_event A g P limit c i ev o ht hh)
      contradiction
  have hnow : c.time = c.deadline := by simpa [step,not_lt.mpr ht,he] using hs
  intro j
  by_contra hn
  obtain ⟨i,hni,hm⟩ := least_cursor c cur ⟨j,hn⟩
  have had := ready cert c cur hv i hm hni
  have ht' : due limit (cur i).rest (c.workers i).busy = c.time :=
    le_antisymm ((due_le cert _ _).trans_eq (hnow.trans hd).symm) (hv.time i)
  change (event O alg c _).isSome at had
  simp [ht',he] at had

lemma execute (cert : Certified g seed limit rows) (j : (GraceSgd.algorithm A limit).Seed)
    (htr : ∀ i, LeonTranscript.Trace ((GraceSgd.algorithm A limit).initial i j).program
      (rows.map fun c => c.op i) (out i)) :
    DistributedTemplate.execute (system p g P) (GraceSgd.algorithm A limit) limit j seed = out r := by
  let O := system p g P
  let alg := GraceSgd.algorithm A limit
  let init := initial O alg limit (j,seed)
  obtain ⟨k,hk⟩ := GraceExecution.finite A g P limit j seed limit le_rfl
  rw [DistributedExecution.execute_eq_terminal O alg limit (j,seed) k hk]
  obtain ⟨cur,hv⟩ := run_valid cert j htr limit le_rfl k (P := P)
  have hall := finished cert _ (DistributedExecution.run_deadline O alg init k)
    (DistributedExecution.run_time_le_deadline O alg init k zero_le) cur hv hk
  have h := hv.trace r
  rw [hall, List.map_nil] at h
  have hfin := LeonLocalTrace.done h
  change (match ((run O alg k init).workers r).program with | .finish x => x | _ => p.x₀) = out r
  rw [hfin]

end LongTails.Proofs.GraceScheduledExecution
