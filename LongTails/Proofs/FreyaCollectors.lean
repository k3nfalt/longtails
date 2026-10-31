import LongTails.Template
import LongTails.Algorithms.FreyaCollectors
import LongTails.Setups.FreyaPageIterations
import LongTails.Proofs.FreyaMoments
import LongTails.Proofs.FreyaEquilibrium

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Proofs.FreyaCollectors

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaRandomness
open LongTails.Algorithms.FreyaCollectors LongTails.Algorithms.FreyaInputs
open LongTails.Setups.FreyaIndependence

section Trajectory

open LongTails.Algorithms.FreyaPage

theorem run_length (q : Raw) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    (run q O seed ω k).2.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [run, ih]

noncomputable def historyAt (q : Raw) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) k :=
  ⟨(run q O seed ω k).2, run_length q O seed ω k⟩

theorem cast_seed {Query Reply : Type*} (O : Oracle Query Reply 1) (ω : (k : ℕ) → O.Seed k)
    {i j : ℕ} (h : i = j) : cast (congrArg O.Seed h) (ω i) = ω j := by
  cases h
  rfl

theorem replyAt_eq_answerAt (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ)
    (x : Fin 1 × Option (Request q.d q.m q.n)) :
    replyAt q O seed ω k x = answerAt O k (historyAt q O seed ω k) x (ω k) := by
  unfold replyAt answerAt historyAt
  rw [cast_seed O ω (run_length q O seed ω k).symm]

theorem trace_succ (q : Raw) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    trace q O seed ω (k + 1) =
      update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) :=
  rfl

theorem historyAt_succ (q : Raw) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
    (historyAt q O seed ω (k + 1)).val = (historyAt q O seed ω k).val ++
      [(query q (trace q O seed ω k), replyAt q O seed ω k (query q (trace q O seed ω k)))] :=
  rfl

theorem measurable_historyAt_append {Query Reply Ω : Type*} [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Ω] {k : ℕ}
    (history : Ω → HistoryAt Query Reply k) (entry : Ω → (Fin 1 × Query) × Reply)
    (hh : Measurable history) (he : Measurable entry) :
    Measurable (fun z => (⟨(history z).val ++ [entry z], by simp [(history z).property]⟩ :
      HistoryAt Query Reply (k + 1))) := by
  apply Measurable.of_comap_le
  rw [show (historyAtMeasurableSpace (k + 1) : MeasurableSpace (HistoryAt Query Reply (k + 1))) =
    MeasurableSpace.comap (historyCoordinates (k + 1)) inferInstance from rfl,
    MeasurableSpace.comap_comp]
  refine Measurable.comap_le (measurable_pi_iff.mpr fun i => ?_)
  by_cases hi : i.val < k
  · have hcoord : Measurable (fun z => historyCoordinates k (history z) ⟨i.val, hi⟩) :=
      (measurable_pi_apply _).comp ((comap_measurable (historyCoordinates k)).comp hh)
    convert hcoord using 1
    funext z
    simp only [Function.comp_apply, historyCoordinates, List.get_eq_getElem, Fin.val_cast]
    exact List.getElem_append_left (by simpa [(history z).property] using hi)
  · have hik : i.val = k := by omega
    convert he using 1
    funext z
    simp only [Function.comp_apply, historyCoordinates, List.get_eq_getElem, Fin.val_cast]
    rw [List.getElem_append_right (by simp [(history z).property, hik])]
    simp [(history z).property, hik]

theorem measurable_trajectory (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) [MeasurableSpace (State q)]
    (hanswer : ∀ k, Measurable (fun z : (HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) k ×
      (Fin 1 × Option (Request q.d q.m q.n))) × O.Seed k => answerAt O k z.1.1 z.1.2 z.2))
    (hinitial : Measurable (initial q))
    (hupdate : Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2))
    (hquery : Measurable (query q)) (k : ℕ) :
    Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => trace q O z.1 z.2 k) ∧
      Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => historyAt q O z.1 z.2 k) := by
  induction k with
  | zero =>
    refine ⟨hinitial.comp measurable_fst, ?_⟩
    convert (measurable_const : Measurable (fun _ : Seed q.K × ((k : ℕ) → O.Seed k) =>
      (⟨[], rfl⟩ : HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) 0))) using 1
    funext z
    rfl
  | succ k ih =>
    have hq := hquery.comp ih.1
    have hr : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
        replyAt q O z.1 z.2 k (query q (trace q O z.1 z.2 k))) := by
      convert (hanswer k).comp ((ih.2.prodMk hq).prodMk
        ((measurable_pi_apply k).comp measurable_snd)) using 1
      funext z
      exact replyAt_eq_answerAt q O z.1 z.2 k _
    refine ⟨hupdate.comp (ih.1.prodMk hr), ?_⟩
    convert measurable_historyAt_append _ _ ih.2 (hq.prodMk hr) using 1
    funext z
    rfl

theorem measurable_replyAt (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) [MeasurableSpace (State q)]
    (hanswer : ∀ k, Measurable (fun z : (HistoryAt (Option (Request q.d q.m q.n)) (Reply q.d q.n) k ×
      (Fin 1 × Option (Request q.d q.m q.n))) × O.Seed k => answerAt O k z.1.1 z.1.2 z.2))
    (hinitial : Measurable (initial q))
    (hupdate : Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2))
    (hquery : Measurable (query q)) (k : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {w : Ω → Seed q.K × ((k : ℕ) → O.Seed k)} (hw : Measurable w)
    {x : Ω → Fin 1 × Option (Request q.d q.m q.n)} (hx : Measurable x) :
    Measurable (fun z => replyAt q O (w z).1 (w z).2 k (x z)) := by
  convert (hanswer k).comp ((((measurable_trajectory q O hanswer hinitial hupdate hquery k).2.comp
    hw).prodMk hx).prodMk ((measurable_pi_apply k).comp (measurable_snd.comp hw))) using 1
  funext z
  exact replyAt_eq_answerAt q O (w z).1 (w z).2 k _

theorem replyAt_seed (q : Raw) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hobl : HistoryOblivious O) (seed seed' : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ)
    (x : Fin 1 × Option (Request q.d q.m q.n)) :
    replyAt q O seed ω k x = replyAt q O seed' ω k x :=
  hobl _ _ x ω (by rw [run_length, run_length])

theorem replyAt_prefix (q : Raw) (b : Bool)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hobl : HistoryOblivious O) (seed seed' : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ)
    (x : Fin 1 × Option (Request q.d q.m q.n)) :
    replyAt { q with «prefix» := b } O seed ω k x = replyAt q O seed' ω k x :=
  hobl _ _ x ω (by rw [run_length, run_length])

end Trajectory

noncomputable def fullQuery {d m n : ℕ} (s : FullState d m n) : Option (Request d m n) :=
  if s.remaining.isEmpty then none else pendingRequest s.clock s.pending

noncomputable def differenceQuery {d m n : ℕ} (s : DifferenceState d m n) :
    Option (Request d m n) :=
  if s.target ≤ s.count then none else pendingRequest s.clock s.pending

noncomputable def fullTrace {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) : ℕ → FullState d m n
  | 0 => fullInitial n labels x start rows
  | a + 1 => let s := fullTrace n labels x start rows answer a
             fullUpdate s (answer a (fullQuery s))

noncomputable def differenceTrace {d m : ℕ} (n S : ℕ)
    (x y : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) : ℕ → DifferenceState d m n
  | 0 => differenceInitial n S x y start rows
  | a + 1 => let s := differenceTrace n S x y start rows answer a
             differenceUpdate s (answer a (differenceQuery s))

def servicePath {d m n : ℕ} (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Reply d n) : Prop :=
  ∀ a, answer a none = none ∧ ∀ r, legalRequest τ r → ∃ i j c,
    r.pending i = some j ∧ answer a (some r) = some (i, j.id, c, jobValue f j) ∧
      r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i'

theorem servicePath_replyAt {q : Raw} {f : Fin q.m → Space q.d → ℝ} {τ : Fin q.n → ℝ≥0∞}
    {O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1} (seed : Seed q.K)
    {ω : (k : ℕ) → O.Seed k}
    (h : ∀ history : List ((Fin 1 × Option (Request q.d q.m q.n)) × Reply q.d q.n),
      O.answer history (0, none) (ω history.length) = none ∧
      ∀ r, legalRequest τ r → ∃ i j c, r.pending i = some j ∧
        O.answer history (0, some r) (ω history.length) = some (i, j.id, c, jobValue f j) ∧
        r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i') :
    servicePath f τ (fun a r => LongTails.Algorithms.FreyaPage.replyAt q O seed ω a (0, r)) :=
  fun a => h (LongTails.Algorithms.FreyaPage.run q O seed ω a).2

noncomputable def contribution {d m : ℕ} (f : Fin m → Space d → ℝ)
    (labels : List (Fin m)) (x : Space d) (a : ℕ) : Space d :=
  (labels[a]?).elim 0 (fun i => gradient (f i) x)

noncomputable def uncovered {d m n : ℕ} (labels : List (Fin m))
    (remaining : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) : List ℕ := by
  classical
  exact ((List.finRange n).filter fun i => decide (i ≤ j)).foldl (fun rem i =>
    (pending i).elim rem fun job =>
      (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem
        (fun a => rem.erase a)) remaining

noncomputable def dispatchContext {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
    List ℕ × (Fin n → Option (Job d m)) × Option (Fin n) × ℝ≥0 := by
  classical
  exact if h : a < n then
    (List.range labels.length,
      (fun i => if i.val < a then (fullInitial n labels x start rows).pending i else none),
      (if labels.isEmpty then none else some ⟨a, h⟩), start)
  else
    let s := fullTrace n labels x start rows answer (a - n)
    let reply := answer (a - n) (fullQuery s)
    let t := fullUpdate s reply
    match reply with
    | none => (t.remaining, s.pending, none, t.clock)
    | some (i, _, _, _) =>
      (t.remaining, Function.update s.pending i none,
        (if t.remaining.isEmpty then none else some i), t.clock)

noncomputable def assignmentRemaining {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) : Finset ℕ := by
  classical
  exact (dispatchContext n labels x start rows answer a).1.toFinset

noncomputable def assignmentChoice {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) : ℕ :=
  (chooseRemaining (rows a) (dispatchContext n labels x start rows answer a).1).getD 0

noncomputable def FullFresh {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} (n : ℕ) (labels : List (Fin m)) (x : Space d) (start : ℝ≥0)
    (rows : Ω → ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Ω → Reply d n) : Prop :=
  ∃ H : ℕ → MeasurableSpace Ω, Monotone H ∧
    FreshAssignments P H
      (fun a ω => assignmentRemaining n labels x start (rows ω) (fun k r => answer k r ω) a)
      (fun a ω => assignmentChoice n labels x start (rows ω) (fun k r => answer k r ω) a) ∧
    (∀ a, Measurable[H a] (fun ω =>
      let c := dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a
      (c.1.toFinset, c.2.1, c.2.2.1, c.2.2.2))) ∧
    (∀ a, Measurable[H (a + 1)] (fun ω =>
      assignmentChoice n labels x start (rows ω) (fun k r => answer k r ω) a))

noncomputable def couponWaiting {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) (j : Fin n) (u : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + n * labels.length)).filter fun a =>
    let c := dispatchContext n labels x start rows answer a
    (∃ i, c.2.2.1 = some i ∧ i ≤ j) ∧ (uncovered labels c.1 c.2.1 j).length = u).card

noncomputable def couponWork {d m : ℕ} (n : ℕ) (labels : List (Fin m))
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (answer : ℕ → Option (Request d m n) → Reply d n) (j : Fin n) : ℕ :=
  ∑ u : Fin labels.length, (couponWaiting n labels x start rows answer j (u.val + 1) + 1)

noncomputable def multisetTimeBound {n : ℕ} (τ : Fin n → ℝ≥0∞) (q : ℕ) : ℝ≥0∞ :=
  12 * (⨅ j : Fin n,
    ((q : ℝ≥0∞) + ENNReal.ofReal ((min q n : ℕ) * Real.log (min q n)) + (j.val + 1 : ℕ)) /
      ∑ i ∈ Finset.Iic j, (τ i)⁻¹)

theorem full_invariant {d m : ℕ} (n : ℕ) (hn : 0 < n)
    (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) (a : ℕ) :
    let s := fullTrace n labels x start rows answer a
    s.remaining.Nodup ∧ (∀ b ∈ s.remaining, b < labels.length) ∧ start ≤ s.clock ∧
      s.sum + (s.remaining.map (contribution f labels x)).sum =
        (labels.map fun i => gradient (f i) x).sum ∧
      (s.remaining ≠ [] → legalRequest τ ⟨s.clock, s.pending⟩) ∧
      (∀ i job, s.pending i = some job → job.kind = Sum.inl x ∧ job.id < s.nextID) ∧
      (∀ i i' job job', s.pending i = some job → s.pending i' = some job' →
        job.id = job'.id → i = i') := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have hdispatch (kind : JobKind d) (c : ℝ≥0) (id : ℕ)
        (b : Option (Fin m)) (job : Job d m) (h : dispatch kind c id b = some job) :
        job.kind = kind ∧ job.started = c ∧ job.id = id := by
      delta dispatch at h
      obtain ⟨i, hi, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      exact ⟨rfl, rfl, rfl⟩
    have hselect (rem : List ℕ) (hne : rem ≠ []) (hbound : ∀ b ∈ rem, b < labels.length)
        (row : ChoiceRow) : ∃ i, selectedLabel labels rem row = some i := by
      have hlen : rem.length ≠ 0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
      let j : Fin rem.length := ⟨(row (rem.length-1)).val, by
        have hj := (row (rem.length-1)).isLt
        omega⟩
      have hb : rem.get j < labels.length := hbound _ (List.get_mem _ _)
      refine ⟨labels[rem.get j], ?_⟩
      delta selectedLabel chooseRemaining
      rw [dite_eq_right hlen]
      dsimp only
      exact List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
    have hinit : ((List.range labels.length).map (contribution f labels x)).sum =
        (labels.map fun i => gradient (f i) x).sum := by
      congr 1
      apply List.ext_getElem (by simp)
      intro b hb hb'
      have hbl : b < labels.length := by simpa only [List.length_map, List.length_range] using hb
      simp only [List.getElem_map, List.getElem_range]
      delta contribution
      rw [List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩]
      rfl
    let I (s : FullState d m n) : Prop :=
      s.original = labels ∧ s.point = x ∧ s.remaining.Nodup ∧
      (∀ b ∈ s.remaining, b < labels.length) ∧ start ≤ s.clock ∧
      s.sum + (s.remaining.map (contribution f labels x)).sum =
        (labels.map fun i => gradient (f i) x).sum ∧
      (s.remaining ≠ [] → legalRequest τ ⟨s.clock, s.pending⟩) ∧
      (∀ i job, s.pending i = some job → job.kind = Sum.inl x ∧ job.id < s.nextID) ∧
      (∀ i i' job job', s.pending i = some job → s.pending i' = some job' →
        job.id = job'.id → i = i')
    have hinv : ∀ a, I (fullTrace n labels x start rows answer a) := by
      intro a
      induction a with
      | zero =>
        change I (fullInitial n labels x start rows)
        refine ⟨rfl, rfl, List.nodup_range, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
        · intro b hb
          exact List.mem_range.mp hb
        · change 0 + ((List.range labels.length).map (contribution f labels x)).sum = _
          simpa only [zero_add] using hinit
        · intro hne
          constructor
          · let i : Fin n := ⟨0, hn⟩
            obtain ⟨b, hb⟩ := hselect (List.range labels.length) hne
              (fun b hb => List.mem_range.mp hb) (rows i.val)
            refine ⟨i, ⟨b, Sum.inl x, start, i.val⟩, ?_⟩
            change dispatch (Sum.inl x) start (0+i.val)
              (selectedLabel labels (List.range labels.length) (rows (0+i.val))) = _
            simp only [zero_add, hb]
            rfl
          · intro i job hj
            have h := hdispatch (Sum.inl x) start i.val _ job (by delta fullInitial at hj; simpa only [zero_add] using hj)
            refine ⟨h.2.1.le, ?_⟩
            delta deadline
            rw [h.2.1]
            exact le_add_of_nonneg_right zero_le
        · intro i job hj
          have h := hdispatch (Sum.inl x) start i.val _ job (by delta fullInitial at hj; simpa only [zero_add] using hj)
          exact ⟨h.1, by change job.id < 0+n; rw [zero_add, h.2.2]; exact i.isLt⟩
        · intro i i' job job' hj hj' hid
          have h := hdispatch (Sum.inl x) start i.val _ job (by delta fullInitial at hj; simpa only [zero_add] using hj)
          have h' := hdispatch (Sum.inl x) start i'.val _ job' (by delta fullInitial at hj'; simpa only [zero_add] using hj')
          apply Fin.ext
          exact h.2.2.symm.trans (hid.trans h'.2.2)
      | succ a ih =>
        let s := fullTrace n labels x start rows answer a
        change I (fullUpdate s (answer a (fullQuery s)))
        by_cases hempty : s.remaining = []
        · have hstop : fullUpdate s (answer a (fullQuery s)) = s := by
            delta fullUpdate
            rw [hempty]
            dsimp only [List.isEmpty]
            rw [ite_eq_left rfl]
          rw [hstop]
          exact ih
        · change I s at ih
          obtain ⟨horig, hpoint, hnodup, hbound, hstart, hsum, hlegal, hjobs, huniq⟩ := ih
          have hisEmpty : s.remaining.isEmpty = false := by
            cases h : s.remaining with
            | nil => exact False.elim (hempty h)
            | cons b bs => rfl
          let r : Request d m n := ⟨s.clock, s.pending⟩
          have hr : legalRequest τ r := hlegal hempty
          have hquery : fullQuery s = some r := by
            delta fullQuery
            simp only [hisEmpty, Bool.false_eq_true, ite_false]
            delta pendingRequest
            have hex : ∃ i, s.pending i ≠ none := by
              obtain ⟨i, job, hj⟩ := hr.1
              change s.pending i = some job at hj
              exact ⟨i, by rw [hj]; simp⟩
            rw [ite_eq_left hex]
          obtain ⟨i, job, c, hj, hreply, hc, hdeadline⟩ := (hservice a).2 r hr
          change s.pending i = some job at hj
          change s.clock ≤ c at hc
          have hkind := (hjobs i job hj).1
          have hvalue : jobValue f job = gradient (f job.component) x := by
            delta jobValue
            rw [hkind]
          let found := s.remaining.find? fun b => decide (s.original[b]? = some job.component)
          let rem := found.elim s.remaining (fun b => s.remaining.erase b)
          let total := if found.isSome then s.sum + jobValue f job else s.sum
          have hrem : rem.Nodup ∧ (∀ b ∈ rem, b < labels.length) ∧
              total + (rem.map (contribution f labels x)).sum =
                (labels.map fun i => gradient (f i) x).sum := by
            cases hfound : found with
            | none => simpa only [rem, total, hfound, Option.elim_none, Option.isSome_none, Bool.false_eq_true, ite_false]
                using And.intro hnodup (And.intro hbound hsum)
            | some b =>
              have hb : b ∈ s.remaining := List.mem_of_find?_eq_some hfound
              have hlabel : labels[b]? = some job.component := by
                have h := List.find?_some hfound
                simpa only [horig, decide_eq_true_eq] using h
              have hcontrib : contribution f labels x b = jobValue f job := by
                delta contribution
                rw [hlabel]
                exact hvalue.symm
              dsimp only [rem, total]
              simp only [hfound, Option.elim_some, Option.isSome_some, ite_true]
              refine ⟨hnodup.erase b, fun k hk => hbound k (List.mem_of_mem_erase hk), ?_⟩
              rw [add_assoc, ← hcontrib, List.sum_map_erase (contribution f labels x) hb]
              exact hsum
          let next := dispatch (Sum.inl s.point) c s.nextID
            (selectedLabel s.original rem (s.rows s.nextID))
          let t : FullState d m n :=
            { s with
              remaining := rem
              sum := total
              pending := Function.update s.pending i next
              clock := c
              nextID := s.nextID+1 }
          have hstep : fullUpdate s (answer a (fullQuery s)) = t := by
            rw [hquery, hreply]
            delta fullUpdate
            rw [hisEmpty, ite_eq_right Bool.false_ne_true]
            dsimp only
            rw [hj]
            dsimp only
            rw [ite_eq_left (And.intro rfl hc)]
          rw [hstep]
          have hnprops (new : Job d m) (hnew : next = some new) :
              new.kind = Sum.inl x ∧ new.started = c ∧ new.id = s.nextID := by
            have h := hdispatch (Sum.inl s.point) c s.nextID _ new hnew
            simpa only [hpoint] using h
          refine ⟨horig, hpoint, hrem.1, hrem.2.1, hstart.trans hc, hrem.2.2, ?_, ?_, ?_⟩
          · intro hne
            have hex : ∃ new, next = some new := by
              obtain ⟨b, hb⟩ := hselect rem hne hrem.2.1 (s.rows s.nextID)
              refine ⟨⟨b, Sum.inl s.point, c, s.nextID⟩, ?_⟩
              change dispatch (Sum.inl s.point) c s.nextID
                (selectedLabel s.original rem (s.rows s.nextID)) = _
              rw [horig, hb]
              rfl
            constructor
            · obtain ⟨new, hnew⟩ := hex
              exact ⟨i, new, (Function.update_self _ _ _).trans hnew⟩
            · intro k old hold
              change Function.update s.pending i next k = some old at hold
              by_cases hk : k = i
              · subst k
                rw [Function.update_self] at hold
                have h := hnprops old hold
                refine ⟨h.2.1.le, ?_⟩
                change (c : ℝ≥0∞) ≤ deadline τ old i
                delta deadline
                rw [h.2.1]
                exact le_add_of_nonneg_right zero_le
              · rw [Function.update_of_ne hk] at hold
                exact ⟨((hr.2 k old hold).1).trans hc, hdeadline k old hold⟩
          · intro k old hold
            change Function.update s.pending i next k = some old at hold
            by_cases hk : k = i
            · subst k
              rw [Function.update_self] at hold
              have h := hnprops old hold
              exact ⟨h.1, by change old.id < s.nextID+1; rw [h.2.2]; omega⟩
            · rw [Function.update_of_ne hk] at hold
              have h := hjobs k old hold
              exact ⟨h.1, by change old.id < s.nextID+1; omega⟩
          · intro k l old old' hold hold' hid
            change Function.update s.pending i next k = some old at hold
            change Function.update s.pending i next l = some old' at hold'
            by_cases hk : k = i
            · subst k
              rw [Function.update_self] at hold
              by_cases hl : l = i
              · exact hl.symm
              · rw [Function.update_of_ne hl] at hold'
                have hnew := (hnprops old hold).2.2
                have holdid := (hjobs l old' hold').2
                omega
            · rw [Function.update_of_ne hk] at hold
              by_cases hl : l = i
              · subst l
                rw [Function.update_self] at hold'
                have hnew := (hnprops old' hold').2.2
                have holdid := (hjobs k old hold).2
                omega
              · rw [Function.update_of_ne hl] at hold'
                exact huniq k l old old' hold hold' hid
    exact (hinv a).2.2


theorem full_event_bound {d m : ℕ} (n : ℕ) (hn : 0 < n)
    (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) :
    (fullTrace n labels x start rows answer (n * labels.length)).remaining = [] ∧
      ∀ a, n * labels.length ≤ a → fullTrace n labels x start rows answer a =
        fullTrace n labels x start rows answer (n * labels.length) := by
  open scoped BigOperators ENNReal NNReal in
    classical
    let tr := fullTrace n labels x start rows answer
    let good (s : FullState d m n) : Finset (Fin n) := Finset.univ.filter fun i =>
      ∃ job, s.pending i = some job ∧ ∃ b ∈ s.remaining, labels[b]? = some job.component
    let V (s : FullState d m n) : ℕ :=
      if s.remaining = [] then 0 else n * (s.remaining.length + 1) - (good s).card
    have hcard (s : FullState d m n) : (good s).card ≤ n := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
    have hselect (rem : List ℕ) (hne : rem ≠ [])
        (hbound : ∀ b ∈ rem, b < labels.length) (row : ChoiceRow) :
        ∃ b, b ∈ rem ∧ ∃ hb : b < labels.length,
          selectedLabel labels rem row = some labels[b] := by
      have hlen : rem.length ≠ 0 := by
        intro hz
        exact hne (List.length_eq_zero_iff.mp hz)
      let j : Fin rem.length := ⟨(row (rem.length-1)).val, by
        have hj := (row (rem.length-1)).isLt
        omega⟩
      have hb := hbound _ (List.get_mem rem j)
      refine ⟨rem.get j, List.get_mem rem j, hb, ?_⟩
      delta selectedLabel chooseRemaining
      rw [dite_eq_right hlen]
      dsimp only
      exact List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
    have hmeta : ∀ a, (tr a).original = labels := by
      intro a
      induction a with
      | zero => rfl
      | succ a ih =>
        change (fullUpdate (tr a) (answer a (fullQuery (tr a)))).original = labels
        delta fullUpdate
        by_cases he : (tr a).remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact ih
        · rw [ite_eq_right he]
          cases hr : answer a (fullQuery (tr a)) with
          | none => exact ih
          | some reply =>
            obtain ⟨i, id, c, value⟩ := reply
            dsimp only
            cases hp : (tr a).pending i with
            | none => exact ih
            | some job =>
              dsimp only
              split <;> exact ih
    have halt (s : FullState d m n) (hs : s.remaining = []) (reply : Reply d n) :
        fullUpdate s reply = s := by
      delta fullUpdate
      rw [hs]
      dsimp only [List.isEmpty]
      rw [ite_eq_left rfl]
    have hinit : V (tr 0) ≤ n * labels.length := by
      by_cases hempty : labels = []
      · subst labels
        exact Nat.zero_le _
      · have hne : (List.range labels.length) ≠ [] := by
          intro h
          have := congrArg List.length h
          simp only [List.length_range, List.length_nil] at this
          exact hempty (List.length_eq_zero_iff.mp this)
        have hg : good (tr 0) = Finset.univ := by
          apply Finset.ext
          intro i
          simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          obtain ⟨b, hb, hbl, hlabel⟩ := hselect (List.range labels.length) hne
            (fun k hk => List.mem_range.mp hk) (rows i.val)
          refine ⟨⟨labels[b], Sum.inl x, start, i.val⟩, ?_, b, hb, ?_⟩
          · change dispatch (Sum.inl x) start (0+i.val)
              (selectedLabel labels (List.range labels.length) (rows (0+i.val))) = _
            simp only [zero_add, hlabel]
            rfl
          · exact List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩
        change (if (List.range labels.length) = [] then 0 else
          n * ((List.range labels.length).length+1) - (good (tr 0)).card) ≤ _
        rw [ite_eq_right hne, hg, Finset.card_fin, List.length_range, Nat.mul_add, Nat.mul_one]
        omega
    have hpositive (s : FullState d m n) (hne : s.remaining ≠ []) : 0 < V s := by
      have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
      have hc := hcard s
      have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
      dsimp only [V]
      rw [ite_eq_right hne, Nat.mul_add, Nat.mul_one]
      omega
    have hdecrease : ∀ a, (tr a).remaining ≠ [] → V (tr (a+1)) + 1 ≤ V (tr a) := by
      intro a hne
      let s := tr a
      have horig := hmeta a
      change s.original = labels at horig
      have hinv := full_invariant n hn labels x start rows f τ answer hservice a
      change s.remaining.Nodup ∧ (∀ b ∈ s.remaining, b < labels.length) ∧ _ at hinv
      have hbound := hinv.2.1
      let r : Request d m n := ⟨s.clock, s.pending⟩
      have hr : legalRequest τ r := hinv.2.2.2.2.1 hne
      have hisEmpty : s.remaining.isEmpty = false := by
        cases h : s.remaining with
        | nil => exact False.elim (hne h)
        | cons b bs => rfl
      have hquery : fullQuery s = some r := by
        delta fullQuery
        simp only [hisEmpty, Bool.false_eq_true, ite_false]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i, job, hj⟩ := hr.1
          change s.pending i = some job at hj
          exact ⟨i, by rw [hj]; simp⟩
        rw [ite_eq_left hex]
      obtain ⟨i, job, c, hj, hreply, hc, _⟩ := (hservice a).2 r hr
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      let found := s.remaining.find? fun b => decide (s.original[b]? = some job.component)
      let rem := found.elim s.remaining (fun b => s.remaining.erase b)
      let next := dispatch (Sum.inl s.point) c s.nextID
        (selectedLabel s.original rem (s.rows s.nextID))
      let t : FullState d m n :=
        { s with
          remaining := rem
          sum := if found.isSome then s.sum + jobValue f job else s.sum
          pending := Function.update s.pending i next
          clock := c
          nextID := s.nextID+1 }
      have hstep : tr (a+1) = t := by
        change fullUpdate s (answer a (fullQuery s)) = t
        rw [hquery, hreply]
        delta fullUpdate
        rw [hisEmpty, ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
      rw [hstep]
      by_cases ht : rem = []
      · have hzero : V t = 0 := by
          dsimp only [V]
          exact ite_eq_left ht
        rw [hzero]
        exact hpositive s hne
      · have hrembound : ∀ b ∈ rem, b < labels.length := by
          cases hf : found with
          | none => simpa only [rem, hf, Option.elim_none] using hbound
          | some b =>
            intro k hk
            exact hbound k (List.mem_of_mem_erase (by simpa only [rem, hf, Option.elim_some] using hk))
        have hgood : i ∈ good t := by
          obtain ⟨b, hb, hbl, hlabel⟩ := hselect rem ht hrembound (s.rows s.nextID)
          simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨labels[b], Sum.inl s.point, c, s.nextID⟩, ?_, b, hb, ?_⟩
          · change Function.update s.pending i next i = _
            rw [Function.update_self]
            change dispatch (Sum.inl s.point) c s.nextID
              (selectedLabel s.original rem (s.rows s.nextID)) = _
            rw [horig, hlabel]
            rfl
          · exact List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩
        have hlow : 1 ≤ (good t).card := Finset.card_pos.mpr ⟨i, hgood⟩
        have hcs := hcard s
        have hct := hcard t
        change (if rem = [] then 0 else n*(rem.length+1)-(good t).card)+1 ≤ _
        rw [ite_eq_right ht]
        change n*(rem.length+1)-(good t).card+1 ≤
          if s.remaining = [] then 0 else n*(s.remaining.length+1)-(good s).card
        rw [ite_eq_right hne]
        cases hf : found with
        | some b =>
          have hb : b ∈ s.remaining := List.mem_of_find?_eq_some hf
          have hlen : rem.length+1 = s.remaining.length := by
            dsimp only [rem]
            rw [hf]
            change (s.remaining.erase b).length+1=s.remaining.length
            have hl := List.length_erase_of_mem hb
            have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            omega
          have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hmul : n ≤ n*s.remaining.length := Nat.le_mul_of_pos_right _ hp
          rw [hlen, Nat.mul_add, Nat.mul_one]
          have calcBound (n a b c : ℕ) (hn : 0<n) (hb : b≤n) (hc : 1≤c)
              (hc' : c≤n) (ha : n≤a) : a-c+1≤a+n-b := by omega
          exact calcBound n (n*s.remaining.length) (good s).card (good t).card hn hcs hlow hct hmul
        | none =>
          have hrem : rem = s.remaining := by simp only [rem, hf, Option.elim_none]
          have hbad : i ∉ good s := by
            intro hi
            obtain ⟨old, hold, b, hb, hlabel⟩ := (Finset.mem_filter.mp hi).2
            have heq : old = job := Option.some.inj (hold.symm.trans hj)
            subst old
            have hfind := List.find?_eq_none.mp hf b hb
            simp only [horig, hlabel, decide_true, not_true_eq_false] at hfind
          have hset : good t = insert i (good s) := by
            apply Finset.ext
            intro k
            by_cases hk : k = i
            · subst k
              exact iff_of_true hgood (Finset.mem_insert_self _ _)
            · simp only [Finset.mem_insert, hk, false_or]
              change (k ∈ Finset.univ.filter fun k =>
                ∃ old, Function.update s.pending i next k = some old ∧
                  ∃ b ∈ rem, labels[b]? = some old.component) ↔ _
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [Function.update_of_ne hk, hrem]
              simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          have hcount : (good t).card = (good s).card+1 := by
            rw [hset, Finset.card_insert_of_notMem hbad]
          rw [hrem, hcount, Nat.mul_add, Nat.mul_one]
          have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
          have calcBound (n a b : ℕ) (hn : 0<n) (hb : b≤n) (ha : n≤a) :
              a+n-(b+1)+1≤a+n-b := by omega
          exact calcBound n (n*s.remaining.length) (good s).card hn hcs hmul
    have hbound : ∀ a, V (tr a) ≤ n*labels.length-a := by
      intro a
      induction a with
      | zero => simpa only [Nat.sub_zero] using hinit
      | succ a ih =>
        by_cases he : (tr a).remaining = []
        · have hstep : tr (a+1) = tr a := halt (tr a) he _
          rw [hstep]
          have hz : V (tr a) = 0 := ite_eq_left he
          rw [hz]
          exact Nat.zero_le _
        · have hd := hdecrease a he
          have calcBound (current next total a : ℕ) (hi : current≤total-a) (hd : next+1≤current) :
              next≤total-(a+1) := by omega
          exact calcBound _ _ _ _ ih hd
    have hterminal : (tr (n*labels.length)).remaining = [] := by
      by_contra hne
      have hp := hpositive _ hne
      have hb := hbound (n*labels.length)
      rw [Nat.sub_self] at hb
      exact (Nat.not_lt_of_ge hb) hp
    refine ⟨hterminal, ?_⟩
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => rfl
    | succ a ha ih =>
      change fullUpdate (tr a) (answer a (fullQuery (tr a))) = tr (n*labels.length)
      change tr a = tr (n*labels.length) at ih
      rw [ih]
      exact halt _ hterminal _


theorem difference_event_bound {d m : ℕ} (hm : 0 < m) (n S : ℕ) (hn : 0 < n)
    (x y : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) :
    (∀ a, a ≤ S → (differenceTrace n S x y start rows answer a).count = a) ∧
      ∀ a, S ≤ a → differenceTrace n S x y start rows answer a =
        differenceTrace n S x y start rows answer S := by
  open scoped ENNReal NNReal in
    classical
    have hlabel (row : ChoiceRow) : ∃ i : Fin m, labelAt row m = some i := by
      delta labelAt
      simp only [hm, dite_true]
      exact ⟨_, rfl⟩
    let tr := differenceTrace n S x y start rows answer
    have htc : ∀ a, a ≤ S → (tr a).target = S ∧ (tr a).count = a := by
      by_cases hS : S = 0
      · intro a ha
        have ha0 : a = 0 := by omega
        subst a
        exact ⟨rfl, rfl⟩
      · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
        have hinv : ∀ a, a ≤ S →
            (tr a).target = S ∧ (tr a).count = a ∧
              ∀ i, ∃ job, (tr a).pending i = some job ∧ job.started ≤ (tr a).clock ∧
                ((tr a).clock : ℝ≥0∞) ≤ deadline τ job i := by
          intro a
          induction a with
          | zero =>
            intro _
            refine ⟨rfl, rfl, ?_⟩
            intro i
            obtain ⟨b, hb⟩ := hlabel (rows i.val)
            let job : Job d m := ⟨b, Sum.inr (x,y), start, i.val⟩
            refine ⟨job, ?_, le_rfl, ?_⟩
            · change (if S = 0 then none else dispatch (Sum.inr (x,y)) start (0+i.val)
                (labelAt (rows (0+i.val)) m)) = some job
              rw [ite_eq_right hS]
              simp only [zero_add, hb]
              rfl
            · change (start : ℝ≥0∞) ≤ (start : ℝ≥0∞) + (2 : ℕ) * τ i
              exact le_add_of_nonneg_right zero_le
          | succ a ih =>
            intro ha
            have haS : a < S := by omega
            obtain ⟨htarget, hcount, hpending⟩ := ih (by omega)
            let s := tr a
            let r : Request d m n := ⟨s.clock, s.pending⟩
            change s.target = S at htarget
            change s.count = a at hcount
            have hlegal : legalRequest τ r := by
              constructor
              · let i : Fin n := ⟨0, hn⟩
                obtain ⟨job, hj, _, _⟩ := hpending i
                exact ⟨i, job, hj⟩
              · intro i job hj
                obtain ⟨job', hj', hstart, htime⟩ := hpending i
                have heq : job = job' := Option.some.inj (hj.symm.trans hj')
                subst job'
                exact ⟨hstart, htime⟩
            have hactive : ¬s.target ≤ s.count := by
              rw [htarget, hcount]
              omega
            have hquery : differenceQuery s = some r := by
              delta differenceQuery
              rw [ite_eq_right hactive]
              delta pendingRequest
              have hex : ∃ i, s.pending i ≠ none := by
                obtain ⟨i, job, hj⟩ := hlegal.1
                change s.pending i = some job at hj
                exact ⟨i, by rw [hj]; simp⟩
              rw [ite_eq_left hex]
            obtain ⟨i, job, c, hj, hreply, hc, hdeadline⟩ := (hservice a).2 r hlegal
            change s.pending i = some job at hj
            change s.clock ≤ c at hc
            obtain ⟨b, hb⟩ := hlabel (s.rows s.nextID)
            let next : Job d m := ⟨b, Sum.inr (s.x,s.y), c, s.nextID⟩
            let t : DifferenceState d m n :=
              { s with
                count := s.count+1
                sum := s.sum+jobValue f job
                pending := Function.update s.pending i (some next)
                clock := c
                nextID := s.nextID+1 }
            have hnext : tr (a+1) = t := by
              change differenceUpdate s (answer a (differenceQuery s)) = t
              rw [hquery, hreply]
              delta differenceUpdate
              rw [ite_eq_right hactive]
              dsimp only
              rw [hj]
              dsimp only
              rw [ite_eq_left (And.intro rfl hc)]
              delta dispatch
              rw [hb]
              rfl
            rw [hnext]
            refine ⟨htarget, ?_, ?_⟩
            · change s.count + 1 = a + 1
              rw [hcount]
            · intro k
              by_cases hk : k = i
              · subst k
                refine ⟨next, ?_, le_rfl, ?_⟩
                · exact Function.update_self _ _ _
                · change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞) + (2 : ℕ) * τ i
                  exact le_add_of_nonneg_right zero_le
              · obtain ⟨old, hold, hstarted, _⟩ := hpending k
                refine ⟨old, ?_, hstarted.trans hc, hdeadline k old hold⟩
                change Function.update s.pending i (some next) k = some old
                rw [Function.update_of_ne hk]
                exact hold
        intro a ha
        exact ⟨(hinv a ha).1, (hinv a ha).2.1⟩
    refine ⟨fun a ha => (htc a ha).2, ?_⟩
    have halt (s : DifferenceState d m n) (hs : s.target ≤ s.count) (reply : Reply d n) :
        differenceUpdate s reply = s := by
      delta differenceUpdate
      exact ite_eq_left hs
    have hterminal : (tr S).target ≤ (tr S).count := by
      rw [(htc S le_rfl).1, (htc S le_rfl).2]
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => rfl
    | succ a ha ih =>
      change differenceUpdate (tr a) (answer a (differenceQuery (tr a))) = tr S
      change tr a = tr S at ih
      rw [ih]
      exact halt (tr S) hterminal _


theorem finite_completion {d m n : ℕ} (f : Fin m → Space d → ℝ)
    (τ : Fin n → ℝ≥0∞) (O : Oracle (Option (Request d m n)) (Reply d n) 1)
    (hservice : PrimitiveService f τ O) : LiveService τ O := by
  filter_upwards [hservice.2] with ω hω
  intro history r hr
  obtain ⟨i, j, c, hj, hanswer, hc, _⟩ := (hω history).2 r hr
  exact ⟨i, j, c, jobValue f j, hj, hanswer, hc⟩


theorem coupon_progress {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} (n : ℕ) (hn : 0 < n) (labels : List (Fin m)) (hq : 0 < labels.length)
    (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
    (hrows : Measurable rows)
    (hanswer : ∀ a, Measurable (fun z : Option (Request d m n) × Ω => answer a z.1 z.2))
    (hservice : ∀ᵐ ω ∂(P : Measure Ω), servicePath f τ (fun a r => answer a r ω))
    (hfresh : FullFresh P n labels x start rows answer) (j : Fin n)
    (u : ℕ) (hu : 0 < u) :
    (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
      ∂(P : Measure Ω)) ≤ 1 + (min (j.val + 1) labels.length : ℕ) / (u : ℝ≥0∞) := by
  have _hrows := hrows
  have _hanswer := hanswer
  set_option maxHeartbeats 1600000 in
  open scoped BigOperators ENNReal NNReal in
    have freyaDevelopmentEraseMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (b : β) (l : List α) :
        ((l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)).map φ = (l.map φ).erase b := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        by_cases ha : φ a = b
        · simp [ha]
        · cases hf : l.find? (fun a => decide (φ a = b)) with
          | none =>
            have hnot : b ∉ l.map φ := by
              intro hb
              obtain ⟨v,hv,heq⟩ := List.mem_map.mp hb
              have h := List.find?_eq_none.mp hf v hv
              simp only [heq,decide_true,not_true_eq_false] at h
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_none,
              List.map_cons]
            rw [List.erase_of_not_mem (by simpa only [List.mem_cons,not_or] using And.intro (Ne.symm ha) hnot)]
          | some v =>
            have hv : φ v = b := by
              have h := List.find?_some hf
              simpa only [decide_eq_true_eq] using h
            have hva : v ≠ a := by intro h; subst v; exact ha hv
            have hi := ih
            rw [hf] at hi
            simp only [Option.elim_some] at hi
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_some,
              List.map_cons]
            rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using Ne.symm hva), List.map_cons,hi,List.erase_cons_tail (by simpa only [beq_iff_eq] using ha)]
    have freyaDevelopmentEraseFoldCount {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) l).count b = l.count b - jobs.count b := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        by_cases hab : a = b
        · subst a
          simp only [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne (Ne.symm hab)]
          simp only [List.count_cons,hab,beq_iff_eq,ite_false]
          omega
    have freyaDevelopmentEraseFoldLength {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) :
        (jobs.foldl (fun rem a => rem.erase a) l).length ≤ l.length ∧
          l.length ≤ (jobs.foldl (fun rem a => rem.erase a) l).length + jobs.length := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        obtain ⟨h₁,h₂⟩ := ih (l.erase a)
        have hlen : (l.erase a).length ≤ l.length := List.length_erase_le
        have hlen' : l.length ≤ (l.erase a).length + 1 := by
          by_cases ha : a ∈ l
          · rw [List.length_erase_of_mem ha]
            omega
          · rw [List.erase_of_not_mem ha]
            omega
        simpa only [List.foldl_cons,List.length_cons] using And.intro (h₁.trans hlen) (by omega)
    have freyaDevelopmentEraseFoldMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (jobs : List β) (l : List α) :
        (jobs.foldl (fun rem b => (rem.find? fun a => decide (φ a = b)).elim rem
          (fun a => rem.erase a)) l).map φ =
          jobs.foldl (fun rem b => rem.erase b) (l.map φ) := by
      induction jobs generalizing l with
      | nil => rfl
      | cons b jobs ih =>
        simp only [List.foldl_cons]
        rw [ih,freyaDevelopmentEraseMap]
    have freyaDevelopmentFilterMapFold {ι α β : Type}
        (f : List α → β → List α) (p : ι → Option β) (workers : List ι) (l : List α) :
        workers.foldl (fun rem i => (p i).elim rem (f rem)) l =
          (workers.filterMap p).foldl f l := by
      induction workers generalizing l with
      | nil => rfl
      | cons i workers ih =>
        simp (config := { iota := false }) only [List.foldl_cons,List.filterMap_cons]
        cases hp : p i with
        | none => exact ih l
        | some b => exact ih (f l b)
    have freyaDevelopmentEraseFoldPerm {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs jobs' l l' : List α) (hj : jobs.Perm jobs') (hl : l.Perm l') :
        (jobs.foldl (fun rem a => rem.erase a) l).Perm
          (jobs'.foldl (fun rem a => rem.erase a) l') := by
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentEraseFoldCount,freyaDevelopmentEraseFoldCount,
        hl.count_eq b,hj.count_eq b]
    have freyaDevelopmentUncoveredCounts {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (b : Option (Fin m)) :
        ((uncovered labels rem pending j).map (fun a => labels[a]?)).count b =
          (rem.map (fun a => labels[a]?)).count b -
            ((((List.finRange n).filter fun i => decide (i ≤ j)).filterMap
              (fun i => (pending i).map fun job => some job.component)).count b) := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let φ := fun a : ℕ => labels[a]?
      let p := fun i => (pending i).map fun job => some job.component
      let eraseOne := fun (l : List ℕ) (b : Option (Fin m)) =>
        (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)
      have hf : (fun (l : List ℕ) i => (pending i).elim l fun job =>
          (l.find? fun a => decide (labels[a]? = some job.component)).elim l
            (fun a => l.erase a)) = (fun l i => (p i).elim l (eraseOne l)) := by
        funext l i
        dsimp only [p]
        cases hp : pending i with
        | none => rfl
        | some job => rfl
      have heq : uncovered labels rem pending j = (workers.filterMap p).foldl eraseOne rem := by
        delta uncovered
        rw [hf]
        exact freyaDevelopmentFilterMapFold eraseOne p workers rem
      rw [heq]
      change ((workers.filterMap p).foldl
        (fun l b => (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)) rem
          |>.map φ |>.count b) = _
      rw [freyaDevelopmentEraseFoldMap]
      exact freyaDevelopmentEraseFoldCount (workers.filterMap p) (rem.map φ) b
    have freyaDevelopmentContextNodup {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
        (dispatchContext n labels x start rows answer a).1.Nodup := by
      classical
      have hup (s : FullState d m n) (reply : Reply d n) (hs : s.remaining.Nodup) :
          (fullUpdate s reply).remaining.Nodup := by
        delta fullUpdate
        by_cases he : s.remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact hs
        · rw [ite_eq_right he]
          cases reply with
          | none => exact hs
          | some reply =>
            obtain ⟨i,id,c,value⟩ := reply
            dsimp only
            cases hp : s.pending i with
            | none => exact hs
            | some job =>
              dsimp only
              split
              · dsimp only
                cases hf : s.remaining.find? (fun b => decide (s.original[b]? = some job.component)) with
                | none => exact hs
                | some b => exact hs.erase b
              · exact hs
      have htrace : ∀ k, (fullTrace n labels x start rows answer k).remaining.Nodup := by
        intro k
        induction k with
        | zero => exact List.nodup_range
        | succ k ih => exact hup _ _ ih
      delta dispatchContext
      by_cases ha : a < n
      · rw [dite_eq_left ha]
        exact List.nodup_range
      · rw [dite_eq_right ha]
        dsimp only
        have h := hup (fullTrace n labels x start rows answer (a-n))
          (answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n)))) (htrace (a-n))
        cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
        | none => simpa only [hr] using h
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          simpa only [hr] using h
    have freyaDevelopmentUncoveredLengthPerm {d m n : ℕ} (labels : List (Fin m))
        (rem rem' : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (hrem : rem.Perm rem') :
        (uncovered labels rem pending j).length = (uncovered labels rem' pending j).length := by
      classical
      have hp : ((uncovered labels rem pending j).map (fun a => labels[a]?)).Perm
          ((uncovered labels rem' pending j).map (fun a => labels[a]?)) := by
        apply List.perm_iff_count.mpr
        intro b
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,
          (hrem.map (fun a => labels[a]?)).count_eq b]
      simpa only [List.length_map] using hp.length_eq
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaDevelopmentPendingCodesMeas {d m n : ℕ} :
        Measurable (fun pending : Fin n → Option (Job d m) =>
          fun i => (pending i).elim 0 (fun job => job.component.val+1)) := by
      have hj : Measurable (fun job : Job d m => job.component) := measurable_fst.comp (comap_measurable _)
      have hv : Measurable (fun job : Job d m => job.component.val+1) :=
        (measurable_of_countable (fun i : Fin m => i.val+1)).comp hj
      exact Measurable.of_eval fun i => (freyaDevelopmentOptionElimMeas 0 _ hv).comp (measurable_pi_apply i)
    have freyaDevelopmentEraseFoldDemand {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) (l.erase b)).Perm
          ((jobs.foldl (fun rem a => rem.erase a) l).erase b) := by
      apply List.perm_iff_count.mpr
      intro a
      rw [freyaDevelopmentEraseFoldCount]
      by_cases ha : a = b
      · subst a
        rw [List.count_erase_self,List.count_erase_self,freyaDevelopmentEraseFoldCount]
        omega
      · rw [List.count_erase_of_ne ha,List.count_erase_of_ne ha,freyaDevelopmentEraseFoldCount]
    have freyaDevelopmentOneHit (U : ℕ → ℕ) (hmono : Antitone U) (N u : ℕ) :
        ((Finset.range N).filter fun a => U a = u ∧ U (a+1) < u).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have hA := (Finset.mem_filter.mp ha).2
      have hB := (Finset.mem_filter.mp hb).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hab | hba
      · have h : U b ≤ U (a+1) := hmono (Nat.succ_le_of_lt hab)
        omega
      · have h : U a ≤ U (b+1) := hmono (Nat.succ_le_of_lt hba)
        omega
    have freyaDevelopmentFreshSubset {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (H : ℕ → MeasurableSpace Ω) (a : ℕ) (hH : H a ≤ ‹MeasurableSpace Ω›)
        (R U : Ω → Finset ℕ) (C : Ω → ℕ)
        (hR : Measurable[H a] R) (hU : Measurable[H a] U) (hC : Measurable C)
        (q : ℕ) (hsub : ∀ ω, U ω ⊆ R ω) (hbound : ∀ ω, R ω ⊆ Finset.range q)
        (huniform : ∀ E, MeasurableSet[H a] E → ∀ j : ℕ,
          (∫⁻ ω in E, if (R ω).Nonempty ∧ C ω = j then (1 : ℝ≥0∞) else 0 ∂(P : Measure Ω)) =
            ∫⁻ ω in E, if j ∈ R ω then ((R ω).card : ℝ≥0∞)⁻¹ else 0 ∂(P : Measure Ω))
        (E : Set Ω) (hE : MeasurableSet[H a] E) :
        (∫⁻ ω in E, if C ω ∈ U ω then (1 : ℝ≥0∞) else 0 ∂(P : Measure Ω)) =
          ∫⁻ ω in E, ((U ω).card : ℝ≥0∞)/((R ω).card : ℝ≥0∞) ∂(P : Measure Ω) := by
      classical
      let A := fun j ω => if j ∈ U ω then
        (if (R ω).Nonempty ∧ C ω = j then (1 : ℝ≥0∞) else 0) else 0
      let B := fun j ω => if j ∈ U ω then ((R ω).card : ℝ≥0∞)⁻¹ else 0
      have hUset (j : ℕ) : MeasurableSet[H a] {ω | j ∈ U ω} :=
        hU (Set.to_countable {s : Finset ℕ | j ∈ s}).measurableSet
      have hRset : MeasurableSet[H a] {ω | (R ω).Nonempty} :=
        hR (Set.to_countable {s : Finset ℕ | s.Nonempty}).measurableSet
      have hA (j : ℕ) : Measurable (A j) :=
        (measurable_const.ite ((hH _ hRset).inter (hC (measurableSet_singleton j))) measurable_const).ite
          (hH _ (hUset j)) measurable_const
      have hB (j : ℕ) : Measurable (B j) :=
        ((measurable_of_countable (fun s : Finset ℕ => (s.card : ℝ≥0∞)⁻¹)).comp (hR.mono hH le_rfl)).ite
          (hH _ (hUset j)) measurable_const
      have hAB (j : ℕ) : (∫⁻ ω in E, A j ω ∂(P : Measure Ω)) =
          ∫⁻ ω in E, B j ω ∂(P : Measure Ω) := by
        have h := huniform ({ω | j ∈ U ω} ∩ E) ((hUset j).inter hE) j
        rw [← Measure.restrict_restrict (hH _ (hUset j)),
          ← lintegral_indicator (hH _ (hUset j)),← lintegral_indicator (hH _ (hUset j))] at h
        simp only [Set.indicator_apply,Set.mem_ofPred_eq] at h
        change (∫⁻ ω in E, A j ω ∂(P : Measure Ω)) = _ at h
        refine h.trans (lintegral_congr fun ω => ?_)
        by_cases hj : j ∈ U ω
        · have hr := hsub ω hj
          simp only [ite_eq_left hr,B,ite_eq_left hj]
        · simp only [B,ite_eq_right hj]
      have hsumA (ω : Ω) : (∑ j ∈ Finset.range q, A j ω) =
          if C ω ∈ U ω then (1 : ℝ≥0∞) else 0 := by
        by_cases hc : C ω ∈ U ω
        · rw [ite_eq_left hc]
          have hcq := hbound ω (hsub ω hc)
          rw [Finset.sum_eq_single (C ω)]
          · dsimp only [A]
            rw [ite_eq_left hc,ite_eq_left (And.intro ⟨C ω,hsub ω hc⟩ rfl)]
          · intro b _ hb
            dsimp only [A]
            by_cases hbU : b ∈ U ω
            · rw [ite_eq_left hbU,ite_eq_right (fun h => hb h.2.symm)]
            · rw [ite_eq_right hbU]
          · exact fun h => (h hcq).elim
        · rw [ite_eq_right hc]
          apply Finset.sum_eq_zero
          intro j _
          dsimp only [A]
          by_cases hj : j ∈ U ω
          · rw [ite_eq_left hj]
            have hnot : ¬ ((R ω).Nonempty ∧ C ω = j) := by
              rintro ⟨_,hcj⟩
              exact hc (hcj.symm ▸ hj)
            rw [ite_eq_right hnot]
          · rw [ite_eq_right hj]
      have hsumB (ω : Ω) : (∑ j ∈ Finset.range q, B j ω) =
          ((U ω).card : ℝ≥0∞)/((R ω).card : ℝ≥0∞) := by
        dsimp only [B]
        rw [← Finset.sum_filter]
        have heq : (Finset.range q).filter (fun j => j ∈ U ω) = U ω := by
          ext j
          simp only [Finset.mem_filter]
          exact ⟨And.right,fun hj => ⟨hbound ω (hsub ω hj),hj⟩⟩
        rw [heq,Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
      rw [← lintegral_congr hsumA,← lintegral_congr hsumB,
        lintegral_finsetSum _ (fun j _ => hA j),lintegral_finsetSum _ (fun j _ => hB j)]
      exact Finset.sum_congr rfl fun j _ => hAB j
    have freyaDevelopmentFiniteOccupation {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (N : ℕ) (E Hit : ℕ → Set Ω)
        (hE : ∀ a, MeasurableSet (E a)) (hHit : ∀ a, MeasurableSet (Hit a))
        (c : ℝ≥0∞) (hc : c ≠ 0) (hctop : c ≠ ⊤)
        (hprob : ∀ a ∈ Finset.range N, c*(P : Measure Ω) (E a) ≤ (P : Measure Ω) (Hit a))
        (hone : ∀ᵐ ω ∂(P : Measure Ω), (@Finset.filter ℕ (fun a => ω ∈ Hit a) (Classical.decPred _) (Finset.range N)).card ≤ 1) :
        (∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ E a) (Classical.decPred _) (Finset.range N)).card : ℝ≥0∞) ∂(P : Measure Ω)) ≤ c⁻¹ := by
      classical
      have hcount (F : ℕ → Set Ω) (hF : ∀ a, MeasurableSet (F a)) :
          (∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ F a) (Classical.decPred _) (Finset.range N)).card : ℝ≥0∞) ∂(P : Measure Ω)) =
            ∑ a ∈ Finset.range N, (P : Measure Ω) (F a) := by
        simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
        have hi (a : ℕ) : Measurable (fun ω => if ω ∈ F a then (1 : ℝ≥0∞) else 0) :=
          measurable_const.ite (hF a) measurable_const
        rw [lintegral_finsetSum (Finset.range N)
          (f := fun a ω => if ω ∈ F a then (1 : ℝ≥0∞) else 0) (fun a _ => hi a)]
        apply Finset.sum_congr rfl
        intro a _
        have heq : (fun ω => if ω ∈ F a then (1 : ℝ≥0∞) else 0) =
            (F a).indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          simp only [Set.indicator_apply]
        rw [heq,lintegral_indicator (hF a)]
        simp
      have hsum : (∑ a ∈ Finset.range N, (P : Measure Ω) (Hit a)) ≤ 1 := by
        rw [← hcount Hit hHit]
        have hm : (∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ Hit a) (Classical.decPred _) (Finset.range N)).card : ℝ≥0∞) ∂(P : Measure Ω)) ≤
            ∫⁻ _ω, (1 : ℝ≥0∞) ∂(P : Measure Ω) :=
          lintegral_mono_ae (hone.mono fun ω h => by exact_mod_cast h)
        simpa using hm
      have hmul : c*(∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ E a) (Classical.decPred _) (Finset.range N)).card : ℝ≥0∞)
          ∂(P : Measure Ω)) ≤ 1 := by
        rw [hcount E hE,Finset.mul_sum]
        exact (Finset.sum_le_sum hprob).trans hsum
      have hscaled : c⁻¹*(c*(∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ E a) (Classical.decPred _) (Finset.range N)).card : ℝ≥0∞)
          ∂(P : Measure Ω))) ≤ c⁻¹*1 := by gcongr
      rwa [← mul_assoc,ENNReal.inv_mul_cancel hc hctop,one_mul,mul_one] at hscaled
    have freyaDevelopmentContextSublist {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
        (dispatchContext n labels x start rows answer a).1.Sublist (List.range labels.length) := by
      classical
      have hup (s : FullState d m n) (reply : Reply d n) (hs : s.remaining.Sublist (List.range labels.length)) :
          (fullUpdate s reply).remaining.Sublist (List.range labels.length) := by
        delta fullUpdate
        by_cases he : s.remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact hs
        · rw [ite_eq_right he]
          cases reply with
          | none => exact hs
          | some reply =>
            obtain ⟨i,id,c,value⟩ := reply
            dsimp only
            cases hp : s.pending i with
            | none => exact hs
            | some job =>
              dsimp only
              split
              · dsimp only
                cases hf : s.remaining.find? (fun b => decide (s.original[b]? = some job.component)) with
                | none => exact hs
                | some b => exact List.erase_sublist.trans hs
              · exact hs
      have htrace : ∀ k, (fullTrace n labels x start rows answer k).remaining.Sublist (List.range labels.length) := by
        intro k
        induction k with
        | zero => exact List.Sublist.refl _
        | succ k ih => exact hup _ _ ih
      delta dispatchContext
      by_cases ha : a < n
      · rw [dite_eq_left ha]
      · rw [dite_eq_right ha]
        dsimp only
        have h := hup (fullTrace n labels x start rows answer (a-n))
          (answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n)))) (htrace (a-n))
        cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
        | none => simpa only [hr] using h
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          simpa only [hr] using h
    have freyaDevelopmentRatioLowerBound {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) (E : Set Ω) (hE : MeasurableSet E)
        (U R : Ω → ℕ) (u k : ℕ)
        (hU : ∀ ω ∈ E, U ω = u) (hR : ∀ ω ∈ E, R ω ≤ u+k) :
        ((u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞))*(P : Measure Ω) E ≤
          ∫⁻ ω in E, (U ω : ℝ≥0∞)/(R ω : ℝ≥0∞) ∂(P : Measure Ω) := by
      calc
        _ = ∫⁻ _ω in E, ((u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞)) ∂(P : Measure Ω) := by simp
        _ ≤ _ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hE] with ω hω
          rw [hU ω hω]
          have hden : (R ω : ℝ≥0∞) ≤ ((u+k : ℕ) : ℝ≥0∞) := by exact_mod_cast hR ω hω
          gcongr
    have freyaDevelopmentWaitingConstant (u k : ℕ) (hu : 0 < u) :
        (u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞) ≠ 0 ∧
          (u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞) ≠ ⊤ ∧
          ((u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞))⁻¹ = 1+(k : ℝ≥0∞)/(u : ℝ≥0∞) := by
      have hu0 : (u : ℝ≥0∞) ≠ 0 := by exact_mod_cast hu.ne'
      have huk0 : ((u+k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show u+k ≠ 0 by omega)
      refine ⟨?_,?_,?_⟩
      · exact ENNReal.div_ne_zero.mpr ⟨hu0,by simp⟩
      · exact ENNReal.div_ne_top (by simp) huk0
      · rw [ENNReal.inv_div,Nat.cast_add,ENNReal.add_div,
          ENNReal.div_self hu0 (by simp)] <;> simp_all
    have freyaDevelopmentFreshOccupation {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) (H : ℕ → MeasurableSpace Ω)
        (R U : ℕ → Ω → Finset ℕ) (C : ℕ → Ω → ℕ)
        (hfresh : FreshAssignments P H R C)
        (hUmeas : ∀ a, Measurable[H a] (U a)) (E : ℕ → Set Ω)
        (hE : ∀ a, MeasurableSet[H a] (E a)) (N q u k : ℕ) (hu : 0 < u)
        (hsub : ∀ a ω, U a ω ⊆ R a ω)
        (hbound : ∀ a ω, R a ω ⊆ Finset.range q)
        (hcard : ∀ a ω, ω ∈ E a → (U a ω).card = u)
        (hsize : ∀ a ω, ω ∈ E a → (R a ω).card ≤ u+k)
        (hone : ∀ᵐ ω ∂(P : Measure Ω),
          (@Finset.filter ℕ (fun a => ω ∈ E a ∧ C a ω ∈ U a ω)
            (Classical.decPred _) (Finset.range N)).card ≤ 1) :
        (∫⁻ ω, ((@Finset.filter ℕ (fun a => ω ∈ E a) (Classical.decPred _)
          (Finset.range N)).card : ℝ≥0∞) ∂(P : Measure Ω)) ≤ 1+(k : ℝ≥0∞)/(u : ℝ≥0∞) := by
      classical
      let Hit := fun a => E a ∩ {ω | C a ω ∈ U a ω}
      have hEglobal (a : ℕ) : MeasurableSet (E a) := (hfresh a).1 _ (hE a)
      have hmember (a : ℕ) : MeasurableSet {ω | C a ω ∈ U a ω} :=
        (((hfresh a).2.2.1).prodMk ((hUmeas a).mono (hfresh a).1 le_rfl))
          (Set.to_countable {z : ℕ × Finset ℕ | z.1 ∈ z.2}).measurableSet
      have hHit (a : ℕ) : MeasurableSet (Hit a) := (hEglobal a).inter (hmember a)
      have hprob (a : ℕ) : ((u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞))*(P : Measure Ω) (E a) ≤
          (P : Measure Ω) (Hit a) := by
        have hid := freyaDevelopmentFreshSubset P H a (hfresh a).1 (R a) (U a) (C a)
          (hfresh a).2.1 (hUmeas a) (hfresh a).2.2.1 q (hsub a) (hbound a)
          (hfresh a).2.2.2 (E a) (hE a)
        have hlo := freyaDevelopmentRatioLowerBound P (E a) (hEglobal a)
          (fun ω => (U a ω).card) (fun ω => (R a ω).card) u k (hcard a) (hsize a)
        rw [← hid] at hlo
        have heq : (fun ω => if C a ω ∈ U a ω then (1 : ℝ≥0∞) else 0) =
            {ω | C a ω ∈ U a ω}.indicator (fun _ => (1 : ℝ≥0∞)) := by
          funext ω
          simp only [Set.indicator_apply,Set.mem_ofPred_eq]
        rw [heq,lintegral_indicator (hmember a)] at hlo
        simpa only [lintegral_const,Measure.restrict_apply (hmember a),
          Measure.restrict_apply_univ,one_mul,Set.inter_comm,Hit] using hlo
      obtain ⟨hc,hctop,hcinv⟩ := freyaDevelopmentWaitingConstant u k hu
      have h := freyaDevelopmentFiniteOccupation P N E Hit hEglobal hHit
        ((u : ℝ≥0∞)/((u+k : ℕ) : ℝ≥0∞)) hc hctop (fun a _ => hprob a) hone
      rwa [hcinv] at h
    have freyaDevelopmentUncoveredCode {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        uncovered labels rem pending j =
          ((List.finRange n).filter fun i => decide (i ≤ j)).foldl (fun l i =>
            if (pending i).elim 0 (fun job => job.component.val+1) = 0 then l else
              (l.find? fun a => decide ((labels[a]?).elim 0 (fun v => v.val+1) =
                (pending i).elim 0 (fun job => job.component.val+1))).elim l (fun a => l.erase a)) rem := by
      classical
      delta uncovered
      apply congrArg (fun step => ((List.finRange n).filter fun i => decide (i ≤ j)).foldl step rem)
      funext l i
      cases hp : pending i with
      | none => simp only [Option.elim_none,ite_true]
      | some job =>
        simp only [Option.elim_some]
        rw [ite_eq_right (Nat.succ_ne_zero _)]
        have hpred : (fun a : ℕ => decide (labels[a]? = some job.component)) =
            (fun a => decide ((labels[a]?).elim 0 (fun v => v.val+1) = job.component.val+1)) := by
          funext a
          congr 1
          cases hl : labels[a]? with
          | none => simp
          | some v => simp only [Option.some.injEq,Option.elim_some,Fin.ext_iff,Nat.add_right_cancel_iff]
        rw [hpred]
        congr 3
    have freyaDevelopmentUncoveredSublist {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        (uncovered labels rem pending j).Sublist rem := by
      classical
      have h (workers : List (Fin n)) (l : List ℕ) :
          (workers.foldl (fun rem i => (pending i).elim rem fun job =>
            (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem
              (fun a => rem.erase a)) l).Sublist l := by
        induction workers generalizing l with
        | nil => exact List.Sublist.refl _
        | cons i workers ih =>
          rw [List.foldl_cons]
          cases hp : pending i with
          | none => exact ih l
          | some job =>
            simp only [Option.elim_some]
            cases hf : l.find? (fun a => decide (labels[a]? = some job.component)) with
            | none => exact ih l
            | some a => exact (ih (l.erase a)).trans List.erase_sublist
      exact h _ _
    have freyaDevelopmentCanonicalUncoveredMeas {Ω : Type} [MeasurableSpace Ω]
        {d m n : ℕ} (labels : List (Fin m)) (j : Fin n)
        (R : Ω → Finset ℕ) (pending : Ω → Fin n → Option (Job d m))
        (hR : Measurable R) (hpending : Measurable pending) :
        Measurable (fun ω => (uncovered labels (R ω).toList (pending ω) j).toFinset) := by
      classical
      let F := fun z : Finset ℕ × (Fin n → ℕ) =>
        (((List.finRange n).filter fun i => decide (i ≤ j)).foldl (fun l i =>
          if z.2 i = 0 then l else
            (l.find? fun a => decide ((labels[a]?).elim 0 (fun v => v.val+1) = z.2 i)).elim l
              (fun a => l.erase a)) z.1.toList).toFinset
      have hm := (measurable_of_countable F).comp
        (hR.prodMk (freyaDevelopmentPendingCodesMeas.comp hpending))
      have heq : (fun ω => (uncovered labels (R ω).toList (pending ω) j).toFinset) =
          (fun ω => F (R ω,fun i => (pending ω i).elim 0 (fun job => job.component.val+1))) := by
        funext ω
        rw [freyaDevelopmentUncoveredCode]
      rw [heq]
      exact hm
    have freyaDevelopmentCanonicalUncoveredCard {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (hrem : rem.Nodup) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        (uncovered labels rem.toFinset.toList pending j).toFinset.card =
          (uncovered labels rem pending j).length := by
      classical
      have hp : rem.toFinset.toList.Perm rem := by
        apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hrem).mpr
        intro a
        simp only [Finset.mem_toList,List.mem_toFinset]
      have hn := (freyaDevelopmentUncoveredSublist labels rem.toFinset.toList pending j).nodup
        (Finset.nodup_toList _)
      rw [List.toFinset_card_of_nodup hn]
      exact freyaDevelopmentUncoveredLengthPerm labels _ _ pending j hp
    have freyaDevelopmentUncoveredLengthBound {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        rem.length ≤ (uncovered labels rem pending j).length + (j.val+1) := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let jobs := workers.filterMap fun i => (pending i).map fun job => some job.component
      let vals := rem.map fun a => labels[a]?
      have hp : ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          (jobs.foldl (fun l b => l.erase b) vals) := by
        apply List.perm_iff_count.mpr
        intro b
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentEraseFoldCount]
      have hlen := (freyaDevelopmentEraseFoldLength jobs vals).2
      rw [← hp.length_eq] at hlen
      simp only [List.length_map] at hlen
      have hjobs : jobs.length ≤ workers.length := List.length_filterMap_le _ _
      have hworkers : workers.length = j.val+1 := by
        have hn : workers.Nodup := (List.nodup_finRange n).filter _
        rw [← List.toFinset_card_of_nodup hn]
        have hset : workers.toFinset = Finset.Iic j := by
          ext i
          simp only [List.mem_toFinset,workers,List.mem_filter,List.mem_finRange,
            true_and,decide_eq_true_eq,Finset.mem_Iic]
        rw [hset,Fin.card_Iic]
      have hvals : vals.length = rem.length := List.length_map _
      omega
    have freyaDevelopmentCouponFromDynamics {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n) (u : ℕ) (hu : 0 < u)
        (hdyn : ∀ᵐ ω ∂(P : Measure Ω),
          let ctx := fun a => dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a
          let V := fun a => (uncovered labels (ctx a).1 (ctx a).2.1 j).length
          Antitone V ∧ ∀ a, (∃ i, (ctx a).2.2.1 = some i ∧ i ≤ j) →
            assignmentChoice n labels x start (rows ω) (fun k r => answer k r ω) a ∈
              (uncovered labels (ctx a).1.toFinset.toList (ctx a).2.1 j).toFinset →
            V (a+1) < V a) :
        (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
          ∂(P : Measure Ω)) ≤ 1+(min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞) := by
      classical
      obtain ⟨H,_,hF,hcontext,_⟩ := hfresh
      let ctx := fun a ω => dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a
      let R := fun a ω => (ctx a ω).1.toFinset
      let C := fun a ω => assignmentChoice n labels x start (rows ω) (fun k r => answer k r ω) a
      let U := fun a ω => (uncovered labels (R a ω).toList (ctx a ω).2.1 j).toFinset
      let V := fun a ω => (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length
      let E := fun a => {ω | (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ∧ (U a ω).card = u}
      change FreshAssignments P H R C at hF
      have hUm (a : ℕ) : Measurable[H a] (U a) :=
        @freyaDevelopmentCanonicalUncoveredMeas Ω (H a) d m n labels j (R a) (fun ω => (ctx a ω).2.1)
          (hcontext a).fst (hcontext a).snd.fst
      have hcard (a : ℕ) (ω : Ω) : (U a ω).card = V a ω :=
        freyaDevelopmentCanonicalUncoveredCard labels (ctx a ω).1
          (freyaDevelopmentContextNodup n labels x start (rows ω) (fun k r => answer k r ω) a)
          (ctx a ω).2.1 j
      have hEm (a : ℕ) : MeasurableSet[H a] (E a) := by
        have hflag := (freyaDevelopmentOptionElimMeas false (fun i : Fin n => decide (i ≤ j))
          (measurable_of_countable _)).comp (hcontext a).snd.snd.fst
        have hs : MeasurableSet[H a] {ω | (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j)} := by
          have heq : {ω | (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j)} =
              {ω | ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true} := by
            ext ω
            change (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ↔ _
            cases hc : (ctx a ω).2.2.1 <;> simp [hc]
          rw [heq]
          exact hflag (measurableSet_singleton true)
        exact hs.inter (((measurable_of_countable Finset.card).comp (hUm a)) (measurableSet_singleton u))
      have hsub (a : ℕ) (ω : Ω) : U a ω ⊆ R a ω := by
        intro b hb
        have h := (freyaDevelopmentUncoveredSublist labels (R a ω).toList (ctx a ω).2.1 j).subset
          (List.mem_toFinset.mp hb)
        exact Finset.mem_toList.mp h
      have hbound (a : ℕ) (ω : Ω) : R a ω ⊆ Finset.range labels.length := by
        intro b hb
        exact Finset.mem_range.mpr (List.mem_range.mp ((freyaDevelopmentContextSublist n labels x start (rows ω)
          (fun k r => answer k r ω) a).subset (List.mem_toFinset.mp hb)))
      have hsize (a : ℕ) (ω : Ω) (hω : ω ∈ E a) :
          (R a ω).card ≤ u+min (j.val+1) labels.length := by
        have hlen := freyaDevelopmentUncoveredLengthBound labels (ctx a ω).1 (ctx a ω).2.1 j
        have hq := (freyaDevelopmentContextSublist n labels x start (rows ω)
          (fun k r => answer k r ω) a).length_le
        have hRcard : (R a ω).card = (ctx a ω).1.length :=
          List.toFinset_card_of_nodup (freyaDevelopmentContextNodup n labels x start (rows ω)
            (fun k r => answer k r ω) a)
        have hvalue : V a ω = u := (hcard a ω).symm.trans hω.2
        change (ctx a ω).1.length ≤ V a ω+(j.val+1) at hlen
        simp only [List.length_range] at hq
        change (ctx a ω).1.length ≤ labels.length at hq
        rw [hRcard]
        omega
      have hone : ∀ᵐ ω ∂(P : Measure Ω),
          (@Finset.filter ℕ (fun a => ω ∈ E a ∧ C a ω ∈ U a ω)
            (Classical.decPred _) (Finset.range (n+n*labels.length))).card ≤ 1 := by
        filter_upwards [hdyn] with ω hω
        change Antitone (fun a => V a ω) ∧ _ at hω
        refine (Finset.card_le_card ?_).trans (freyaDevelopmentOneHit (fun a => V a ω) hω.1 (n+n*labels.length) u)
        intro a ha
        have hh : a ∈ Finset.range (n+n*labels.length) ∧ ω ∈ E a ∧ C a ω ∈ U a ω := by
          simpa only [Finset.mem_filter] using ha
        obtain ⟨haN,haE,haU⟩ := hh
        refine Finset.mem_filter.mpr ⟨haN,?_,?_⟩
        · exact (hcard a ω).symm.trans haE.2
        · exact (hω.2 a haE.1 haU).trans_eq ((hcard a ω).symm.trans haE.2)
      have h := freyaDevelopmentFreshOccupation P H R U C hF hUm E hEm
        (n+n*labels.length) labels.length u (min (j.val+1) labels.length) hu hsub hbound
        (fun _ _ hω => hω.2) hsize hone
      refine (le_of_eq (lintegral_congr fun ω => ?_)).trans h
      congr 1
      delta couponWaiting
      congr 1
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter,E,Set.mem_ofPred_eq,hcard]
      rfl
    have freyaDevelopmentFilterMapCount {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (b : α) :
        (workers.filterMap p).count b = ∑ i ∈ workers.toFinset, if p i = some b then 1 else 0 := by
      induction workers with
      | nil => simp
      | cons i workers ih =>
        obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
        have hind := ih hn
        rw [List.toFinset_cons,Finset.sum_insert (by simpa only [List.mem_toFinset] using hi),
          List.filterMap_cons]
        cases hp : p i with
        | none =>
          dsimp only
          rw [ite_eq_right (Ne.symm (Option.some_ne_none b)),Nat.zero_add]
          exact hind
        | some a =>
          dsimp only
          rw [List.count_cons,hind]
          simp only [beq_iff_eq,Option.some.injEq,Nat.add_comm]
    have freyaDevelopmentFilterMapRemovePerm {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (i : ι) (hi : i ∈ workers) (b : α) (hb : p i = some b) :
        (workers.filterMap p).Perm (b :: workers.filterMap (Function.update p i none)) := by
      classical
      apply List.perm_iff_count.mpr
      intro c
      rw [List.count_cons,freyaDevelopmentFilterMapCount workers hn,
        freyaDevelopmentFilterMapCount workers hn]
      have hiS : i ∈ workers.toFinset := List.mem_toFinset.mpr hi
      have hold := Finset.sum_erase_add workers.toFinset (fun k => if p k = some c then 1 else 0) hiS
      have hnew := Finset.sum_erase_add workers.toFinset
        (fun k => if Function.update p i none k = some c then (1 : ℕ) else 0) hiS
      have heq : (∑ k ∈ workers.toFinset.erase i,
          if Function.update p i none k = some c then (1 : ℕ) else 0) =
          ∑ k ∈ workers.toFinset.erase i, if p k = some c then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
      rw [Function.update_self,ite_eq_right (Ne.symm (Option.some_ne_none c)),Nat.add_zero,heq] at hnew
      rw [← hold,← hnew,hb]
      simp only [Option.some.injEq,beq_iff_eq]
    have freyaDevelopmentFilterMapReplacePerm {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (i : ι) (hi : i ∈ workers) (hb : p i = none) (b : α) :
        (workers.filterMap (Function.update p i (some b))).Perm (b :: workers.filterMap p) := by
      have h := freyaDevelopmentFilterMapRemovePerm workers hn (Function.update p i (some b)) i hi b
        (Function.update_self _ _ _)
      have heq : Function.update (Function.update p i (some b)) i none = p := by
        rw [Function.update_idem]
        funext k
        by_cases hk : k = i
        · subst k
          rw [Function.update_self,hb]
        · rw [Function.update_of_ne hk]
      rw [heq] at h
      exact h
    have freyaDevelopmentUncoveredLabelsPerm {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          ((((List.finRange n).filter (fun i => decide (i ≤ j))).filterMap
            (fun i => (pending i).map fun job => some job.component)).foldl
              (fun l b => l.erase b) (rem.map fun a => labels[a]?)) := by
      classical
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentEraseFoldCount]
    have freyaDevelopmentPrefixCompletion {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : i ≤ j) (job : Job d m) (hi : pending i = some job) :
        (uncovered labels
          ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
          (Function.update pending i none) j).length = (uncovered labels rem pending j).length := by
      classical
      let workers := (List.finRange n).filter fun k => decide (k ≤ j)
      let p := fun k => (pending k).map fun job => some job.component
      let p' := fun k => (Function.update pending i none k).map fun job => some job.component
      let vals := rem.map fun a => labels[a]?
      let b := some job.component
      have hn : workers.Nodup := (List.nodup_finRange n).filter _
      have hiw : i ∈ workers := by simp only [workers,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]; exact hij
      have hp : p i = some b := by dsimp only [p]; rw [hi]; rfl
      have hp' : p' = Function.update p i none := by
        funext k
        by_cases hk : k = i
        · subst k
          dsimp only [p']
          rw [Function.update_self,Function.update_self]
          rfl
        · dsimp only [p',p]
          rw [Function.update_of_ne hk,Function.update_of_ne hk]
      have hperm := freyaDevelopmentFilterMapRemovePerm workers hn p i hiw b hp
      rw [← hp'] at hperm
      have hfold := freyaDevelopmentEraseFoldPerm (workers.filterMap p) (b :: workers.filterMap p') vals vals
        hperm (List.Perm.refl _)
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels
        ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
        (Function.update pending i none) j
      have hmap := freyaDevelopmentEraseMap (fun a : ℕ => labels[a]?) b rem
      change (List.map (fun a => labels[a]?) _).Perm
        (List.foldl (fun l b => l.erase b) (List.map (fun a => labels[a]?) _) (workers.filterMap p')) at hnew
      rw [hmap] at hnew
      have hall := hold.trans hfold
      change ((uncovered labels rem pending j).map (fun a => labels[a]?)).Perm
        (List.foldl (fun l b => l.erase b) (vals.erase b) (workers.filterMap p')) at hall
      have hlen := (hnew.trans hall.symm).length_eq
      simpa only [List.length_map] using hlen
    have freyaDevelopmentPrefixAssignment {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : i ≤ j) (hi : pending i = none) (job : Job d m) :
        (uncovered labels rem (Function.update pending i (some job)) j).length ≤
          (uncovered labels rem pending j).length ∧
        (some job.component ∈ (uncovered labels rem pending j).map (fun a => labels[a]?) →
          (uncovered labels rem (Function.update pending i (some job)) j).length+1 =
            (uncovered labels rem pending j).length) := by
      classical
      let workers := (List.finRange n).filter fun k => decide (k ≤ j)
      let p := fun k => (pending k).map fun job => some job.component
      let p' := fun k => (Function.update pending i (some job) k).map fun job => some job.component
      let vals := rem.map fun a => labels[a]?
      let b := some job.component
      have hn : workers.Nodup := (List.nodup_finRange n).filter _
      have hiw : i ∈ workers := by simp only [workers,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]; exact hij
      have hp : p i = none := by dsimp only [p]; rw [hi]; rfl
      have hp' : p' = Function.update p i (some b) := by
        funext k
        by_cases hk : k = i
        · subst k
          dsimp only [p']
          rw [Function.update_self,Function.update_self]
          rfl
        · dsimp only [p',p]
          rw [Function.update_of_ne hk,Function.update_of_ne hk]
      have hperm := freyaDevelopmentFilterMapReplacePerm workers hn p i hiw hp b
      rw [← hp'] at hperm
      have hfold := freyaDevelopmentEraseFoldPerm (workers.filterMap p') (b :: workers.filterMap p) vals vals
        hperm (List.Perm.refl _)
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels rem (Function.update pending i (some job)) j
      have hafter := hnew.trans hfold
      change ((uncovered labels rem (Function.update pending i (some job)) j).map fun a => labels[a]?).Perm
        (List.foldl (fun l b => l.erase b) (vals.erase b) (workers.filterMap p)) at hafter
      have hres := (hafter.trans (freyaDevelopmentEraseFoldDemand (workers.filterMap p) vals b)).trans
        (hold.erase b).symm
      have hlen := hres.length_eq
      simp only [List.length_map] at hlen
      refine ⟨?_,?_⟩
      · rw [hlen]
        exact List.length_erase_le.trans_eq (List.length_map _)
      · intro hb
        rw [hlen,List.length_erase_of_mem hb,List.length_map]
        have hpos := List.length_pos_of_mem hb
        simp only [List.length_map] at hpos
        omega
    have freyaDevelopmentUncoveredSamePrefix {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending pending' : Fin n → Option (Job d m)) (j : Fin n)
        (hp : ∀ i, i ≤ j → (pending i).map (fun job => job.component) =
          (pending' i).map (fun job => job.component)) :
        ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          ((uncovered labels rem pending' j).map fun a => labels[a]?) := by
      classical
      have hf (workers : List (Fin n))
          (hw : ∀ i ∈ workers, (pending i).map (fun job => some job.component) =
            (pending' i).map (fun job => some job.component)) :
          workers.filterMap (fun i => (pending i).map fun job => some job.component) =
            workers.filterMap (fun i => (pending' i).map fun job => some job.component) := by
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          have hhead := hw i List.mem_cons_self
          have htail := ih (fun k hk => hw k (List.mem_cons_of_mem _ hk))
          rw [List.filterMap_cons,List.filterMap_cons,hhead,htail]
      have hworkers := hf ((List.finRange n).filter fun i => decide (i ≤ j)) (by
        intro i hi
        have h := hp i (of_decide_eq_true (List.mem_filter.mp hi).2)
        have hh := congrArg (Option.map some) h
        simpa only [Option.map_map,Function.comp_def] using hh)
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,hworkers]
    have freyaDevelopmentOutsideCompletion {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : ¬ i ≤ j) (job : Job d m) :
        (uncovered labels
          ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
          (Function.update pending i none) j).length ≤ (uncovered labels rem pending j).length := by
      classical
      let rem' := (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a)
      have hsame := freyaDevelopmentUncoveredSamePrefix labels rem' (Function.update pending i none) pending j (by
        intro k hk
        have hki : k ≠ i := by intro h; subst k; exact hij hk
        rw [Function.update_of_ne hki])
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels rem' pending j
      have hmap := freyaDevelopmentEraseMap (fun a : ℕ => labels[a]?) (some job.component) rem
      change (List.map (fun a => labels[a]?) rem') = _ at hmap
      rw [hmap] at hnew
      have hafter := (hnew.trans (freyaDevelopmentEraseFoldDemand _ _ _)).trans
        (hold.erase (some job.component)).symm
      have hlen := (hsame.trans hafter).length_eq
      simp only [List.length_map] at hlen
      rw [hlen]
      exact List.length_erase_le.trans_eq (List.length_map _)
    have freyaDevelopmentFullMetadata {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (a : ℕ) :
        let s := fullTrace n labels x start rows answer a
        s.original = labels ∧ s.rows = rows ∧ (s.remaining ≠ [] → s.nextID = n+a) := by
      classical
      let tr := fullTrace n labels x start rows answer
      have hstatic : ∀ k, (tr k).original = labels ∧ (tr k).rows = rows := by
        intro k
        induction k with
        | zero => exact ⟨rfl,rfl⟩
        | succ k ih =>
          change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).original = labels ∧
            (fullUpdate (tr k) (answer k (fullQuery (tr k)))).rows = rows
          delta fullUpdate
          by_cases he : (tr k).remaining.isEmpty = true
          · rw [ite_eq_left he]
            exact ih
          · rw [ite_eq_right he]
            cases hr : answer k (fullQuery (tr k)) with
            | none => exact ih
            | some reply =>
              obtain ⟨i,id,c,value⟩ := reply
              dsimp only
              cases hp : (tr k).pending i with
              | none => exact ih
              | some job =>
                dsimp only
                split <;> exact ih
      have halt (s : FullState d m n) (he : s.remaining = []) (reply : Reply d n) :
          fullUpdate s reply = s := by
        delta fullUpdate
        rw [he]
        dsimp only [List.isEmpty]
        rw [ite_eq_left rfl]
      have hnext : ∀ k, (tr k).remaining ≠ [] → (tr k).nextID = n+k := by
        intro k
        induction k with
        | zero => intro _; change 0+n=n+0; omega
        | succ k ih =>
          intro hne
          have hprev : (tr k).remaining ≠ [] := by
            intro he
            have hh := halt (tr k) he (answer k (fullQuery (tr k)))
            change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).remaining ≠ [] at hne
            rw [hh] at hne
            exact hne he
          have hinv := full_invariant n hn labels x start rows f τ answer hservice k
          let r : Request d m n := ⟨(tr k).clock,(tr k).pending⟩
          have hlegal : legalRequest τ r := hinv.2.2.2.2.1 hprev
          have he : (tr k).remaining.isEmpty = false := by
            cases hh : (tr k).remaining with
            | nil => exact (hprev hh).elim
            | cons b bs => rfl
          have hquery : fullQuery (tr k) = some r := by
            delta fullQuery
            rw [he,ite_eq_right Bool.false_ne_true]
            delta pendingRequest
            have hx : ∃ i, (tr k).pending i ≠ none := by
              obtain ⟨i,job,hj⟩ := hlegal.1
              exact ⟨i,by change (tr k).pending i = some job at hj; rw [hj]; exact Option.some_ne_none job⟩
            rw [ite_eq_left hx]
          obtain ⟨i,job,c,hj,hr,hc,_⟩ := (hservice k).2 r hlegal
          change (tr k).pending i = some job at hj
          change (tr k).clock ≤ c at hc
          change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).nextID = n+(k+1)
          rw [hquery,hr]
          delta fullUpdate
          rw [he,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hj]
          dsimp only
          rw [ite_eq_left (And.intro rfl hc)]
          change (tr k).nextID+1=n+(k+1)
          rw [ih hprev]
          omega
      exact ⟨(hstatic a).1,(hstatic a).2,hnext a⟩
    have freyaDevelopmentActiveDispatch {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (hne : (fullTrace n labels x start rows answer k).remaining ≠ []) :
        let s := fullTrace n labels x start rows answer k
        ∃ i job c, s.pending i = some job ∧
          let rem := (s.remaining.find? fun a => decide (labels[a]? = some job.component)).elim
            s.remaining (fun a => s.remaining.erase a)
          let next := dispatch (Sum.inl s.point) c (n+k) (selectedLabel labels rem (rows (n+k)))
          dispatchContext n labels x start rows answer (n+k) =
            (rem,Function.update s.pending i none,(if rem.isEmpty then none else some i),c) ∧
          (fullTrace n labels x start rows answer (k+1)).remaining = rem ∧
          (fullTrace n labels x start rows answer (k+1)).pending = Function.update s.pending i next := by
      classical
      let s := fullTrace n labels x start rows answer k
      have hmeta := freyaDevelopmentFullMetadata n hn labels x start rows f τ answer hservice k
      change s.original = labels ∧ s.rows = rows ∧ (s.remaining ≠ [] → s.nextID = n+k) at hmeta
      have hinv := full_invariant n hn labels x start rows f τ answer hservice k
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := hinv.2.2.2.2.1 hne
      have he : s.remaining.isEmpty = false := by
        cases hh : s.remaining with
        | nil => exact (hne hh).elim
        | cons a as => rfl
      have hquery : fullQuery s = some r := by
        delta fullQuery
        rw [he,ite_eq_right Bool.false_ne_true]
        delta pendingRequest
        have hx : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          exact ⟨i,by change s.pending i = some job at hj; rw [hj]; exact Option.some_ne_none job⟩
        rw [ite_eq_left hx]
      obtain ⟨i,job,c,hj,hr,hc,_⟩ := (hservice k).2 r hlegal
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      refine ⟨i,job,c,hj,?_⟩
      let found := s.remaining.find? fun a => decide (labels[a]? = some job.component)
      let rem := found.elim s.remaining (fun a => s.remaining.erase a)
      let next := dispatch (Sum.inl s.point) c (n+k) (selectedLabel labels rem (rows (n+k)))
      let t : FullState d m n := {s with
        remaining := rem
        sum := if found.isSome then s.sum+jobValue f job else s.sum
        pending := Function.update s.pending i next
        clock := c
        nextID := s.nextID+1}
      have hup : fullUpdate s (answer k (fullQuery s)) = t := by
        rw [hquery,hr]
        delta fullUpdate
        rw [he,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
        dsimp only [t,next,rem,found]
        rw [hmeta.1,hmeta.2.1,hmeta.2.2 hne]
      have htrace : fullTrace n labels x start rows answer (k+1) = t := hup
      refine ⟨?_,?_,?_⟩
      · delta dispatchContext
        rw [dite_eq_right (show ¬n+k<n by omega)]
        dsimp only
        rw [show n+k-n=k by omega]
        change (let reply := answer k (fullQuery s)
          let v := fullUpdate s reply
          _) = _
        rw [hup,hquery,hr]
      · rw [htrace]
      · rw [htrace]
    have freyaDevelopmentUncoveredEmpty {d m n : ℕ} (labels : List (Fin m))
        (pending : Fin n → Option (Job d m)) (j : Fin n) :
        uncovered labels [] pending j = [] := by
      exact List.sublist_nil.mp (freyaDevelopmentUncoveredSublist labels [] pending j)
    have freyaDevelopmentUncoveredPerm {d m n : ℕ} (labels : List (Fin m))
        (rem rem' : List ℕ) (hp : rem.Perm rem')
        (pending : Fin n → Option (Job d m)) (j : Fin n) :
        ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          ((uncovered labels rem' pending j).map fun a => labels[a]?) := by
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,
        (hp.map (fun a => labels[a]?)).count_eq]
    have freyaDevelopmentChosenLabel {m : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (hb : ∀ a ∈ rem, a < labels.length) (hne : rem ≠ []) (row : ChoiceRow) :
        ∃ a b, chooseRemaining row rem = some a ∧ a ∈ rem ∧ labels[a]? = some b ∧
          selectedLabel labels rem row = some b := by
      have hlen : rem.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
      let index := row (rem.length-1)
      have hi : index.val < rem.length := by have hh := index.isLt; omega
      let a := rem.get ⟨index.val,hi⟩
      have ha : a ∈ rem := List.get_mem _ _
      have ha' := hb a ha
      refine ⟨a,labels[a],?_,ha,?_,?_⟩
      · delta chooseRemaining
        rw [dite_eq_right hlen]
      · exact List.getElem?_eq_getElem ha'
      · delta selectedLabel
        have hc : chooseRemaining row rem = some a := by
          delta chooseRemaining
          rw [dite_eq_right hlen]
        rw [hc]
        exact List.getElem?_eq_getElem ha'
    have freyaDevelopmentDispatchDecrease {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (hb : ∀ a ∈ rem, a < labels.length) (hr : rem.Nodup)
        (pending : Fin n → Option (Job d m)) (j i : Fin n) (hi : pending i = none)
        (kind : JobKind d) (clock : ℝ≥0) (id : ℕ) (row : ChoiceRow) :
        let next := dispatch kind clock id (selectedLabel labels rem row)
        (uncovered labels rem (Function.update pending i next) j).length ≤
          (uncovered labels rem pending j).length ∧
        (i ≤ j → (chooseRemaining row rem).getD 0 ∈
          (uncovered labels rem.toFinset.toList pending j).toFinset →
          (uncovered labels rem (Function.update pending i next) j).length <
            (uncovered labels rem pending j).length) := by
      classical
      dsimp only
      by_cases he : rem = []
      · subst rem
        rw [freyaDevelopmentUncoveredEmpty,freyaDevelopmentUncoveredEmpty]
        refine ⟨le_rfl,?_⟩
        intro _ hh
        simp only [List.toFinset_nil,Finset.toList_empty,freyaDevelopmentUncoveredEmpty,
          List.toFinset_nil,Finset.notMem_empty] at hh
      obtain ⟨a,b,hc,ha,hb',hs⟩ := freyaDevelopmentChosenLabel labels rem hb he row
      rw [hs]
      dsimp only [dispatch,Option.map_some]
      by_cases hij : i ≤ j
      · have hdec := freyaDevelopmentPrefixAssignment labels rem pending j i hij hi ⟨b,kind,clock,id⟩
        refine ⟨hdec.1,?_⟩
        intro _ hhit
        rw [hc] at hhit
        have hmem : a ∈ uncovered labels rem.toFinset.toList pending j := List.mem_toFinset.mp hhit
        have hval : some b ∈ (uncovered labels rem.toFinset.toList pending j).map (fun a => labels[a]?) :=
          List.mem_map.mpr ⟨a,hmem,hb'⟩
        have hp := freyaDevelopmentUncoveredPerm labels rem.toFinset.toList rem
          (List.toFinset_toList hr) pending j
        have hstrict := hdec.2 (hp.mem_iff.mp hval)
        omega
      · have hp := freyaDevelopmentUncoveredSamePrefix labels rem
          (Function.update pending i (some ⟨b,kind,clock,id⟩)) pending j (by
            intro k hk
            rw [Function.update_of_ne (show k ≠ i by intro h; subst k; exact hij hk)])
        have hlen := hp.length_eq
        simp only [List.length_map] at hlen
        exact ⟨hlen.le,fun h => (hij h).elim⟩
    have freyaDevelopmentEmptyTraceContext {d m : ℕ} (n : ℕ)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (he : (fullTrace n labels x start rows answer k).remaining = []) :
        (dispatchContext n labels x start rows answer (n+k)).1 = [] ∧
        (fullTrace n labels x start rows answer (k+1)).remaining = [] := by
      let s := fullTrace n labels x start rows answer k
      have hquery : fullQuery s = none := by
        delta fullQuery
        change s.remaining = [] at he
        rw [he]
        rfl
      have hup : fullUpdate s (answer k (fullQuery s)) = s := by
        delta fullUpdate
        change s.remaining = [] at he
        rw [he]
        rfl
      refine ⟨?_,?_⟩
      · delta dispatchContext
        rw [dite_eq_right (show ¬ n+k<n by omega)]
        dsimp only
        rw [show n+k-n=k by omega]
        change (let reply := answer k (fullQuery s)
          let t := fullUpdate s reply
          (_ : List ℕ)) = []
        rw [hup,hquery,(hservice k).1]
        exact he
      · change (fullUpdate s (answer k (fullQuery s))).remaining = []
        rw [hup]
        exact he
    have freyaDevelopmentCompletionDecrease {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (k : ℕ) :
        let s := fullTrace n labels x start rows answer k
        let c := dispatchContext n labels x start rows answer (n+k)
        (uncovered labels c.1 c.2.1 j).length ≤ (uncovered labels s.remaining s.pending j).length := by
      dsimp only
      by_cases he : (fullTrace n labels x start rows answer k).remaining = []
      · rw [(freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he).1,
          freyaDevelopmentUncoveredEmpty]
        exact Nat.zero_le _
      obtain ⟨i,job,c,hj,hctx,_,_⟩ := freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k he
      rw [hctx]
      dsimp only
      by_cases hij : i ≤ j
      · exact (freyaDevelopmentPrefixCompletion labels _ _ j i hij job hj).le
      · exact freyaDevelopmentOutsideCompletion labels _ _ j i hij job
    have freyaDevelopmentLaterDynamics {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (k : ℕ) :
        let ctx := fun a => dispatchContext n labels x start rows answer a
        let V := fun a => (uncovered labels (ctx a).1 (ctx a).2.1 j).length
        V (n+k+1) ≤ V (n+k) ∧
          ((∃ i, (ctx (n+k)).2.2.1 = some i ∧ i ≤ j) →
            assignmentChoice n labels x start rows answer (n+k) ∈
              (uncovered labels (ctx (n+k)).1.toFinset.toList (ctx (n+k)).2.1 j).toFinset →
            V (n+k+1) < V (n+k)) := by
      classical
      dsimp only
      rw [show n+k+1=n+(k+1) by omega]
      by_cases he : (fullTrace n labels x start rows answer k).remaining = []
      · have h0 := freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he
        have h1 := freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice (k+1) h0.2
        rw [h0.1,h1.1,freyaDevelopmentUncoveredEmpty,freyaDevelopmentUncoveredEmpty]
        refine ⟨le_rfl,?_⟩
        intro _ hh
        simp only [List.toFinset_nil,Finset.toList_empty,freyaDevelopmentUncoveredEmpty,
          List.toFinset_nil,Finset.notMem_empty] at hh
      obtain ⟨i,job,c,hj,hctx,hrem,hpending⟩ :=
        freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k he
      let s := fullTrace n labels x start rows answer k
      let rem := (s.remaining.find? fun a => decide (labels[a]? = some job.component)).elim
        s.remaining (fun a => s.remaining.erase a)
      let p := Function.update s.pending i none
      have hr : rem.Nodup := by
        have h := freyaDevelopmentContextNodup n labels x start rows answer (n+k)
        rw [hctx] at h
        exact h
      have hb : ∀ a ∈ rem, a < labels.length := by
        have h := freyaDevelopmentContextSublist n labels x start rows answer (n+k)
        rw [hctx] at h
        exact fun a ha => List.mem_range.mp (h.subset ha)
      have hdec := freyaDevelopmentDispatchDecrease labels rem hb hr p j i
        (Function.update_self i none s.pending) (Sum.inl s.point) c (n+k) (rows (n+k))
      simp only [p,Function.update_idem] at hdec
      have hcomp := freyaDevelopmentCompletionDecrease n hn labels x start rows f τ answer hservice j (k+1)
      dsimp only at hcomp
      rw [hrem,hpending] at hcomp
      rw [hctx]
      dsimp only
      refine ⟨hcomp.trans hdec.1,?_⟩
      intro hflag hhit
      have hij : i ≤ j := by
        change (∃ i', (if rem.isEmpty then none else some i) = some i' ∧ i' ≤ j) at hflag
        by_cases hh : rem.isEmpty = true
        · rw [ite_eq_left hh] at hflag
          obtain ⟨i',hi',_⟩ := hflag
          cases hi'
        · rw [ite_eq_right hh] at hflag
          obtain ⟨i',hi',hij'⟩ := hflag
          exact (Option.some.inj hi') ▸ hij'
      have hchoice : assignmentChoice n labels x start rows answer (n+k) =
          (chooseRemaining (rows (n+k)) rem).getD 0 := by
        delta assignmentChoice
        rw [hctx]
      rw [hchoice] at hhit
      exact hcomp.trans_lt (hdec.2 hij hhit)
    have freyaDevelopmentInitialPending {α : Type} {n : ℕ} (p : Fin n → Option α)
        (a : ℕ) (ha : a < n) :
        Function.update (fun i : Fin n => if i.val < a then p i else none) ⟨a,ha⟩ (p ⟨a,ha⟩) =
          (fun i => if i.val < a+1 then p i else none) := by
      classical
      funext i
      by_cases hi : i = ⟨a,ha⟩
      · subst i
        rw [Function.update_self,ite_eq_left (show a<a+1 by omega)]
      · rw [Function.update_of_ne hi]
        have hval : i.val ≠ a := by intro h; exact hi (Fin.ext h)
        by_cases hlt : i.val < a
        · rw [ite_eq_left hlt,ite_eq_left (show i.val<a+1 by omega)]
        · rw [ite_eq_right hlt,ite_eq_right (show ¬i.val<a+1 by omega)]
    have freyaDevelopmentInitialDynamics {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (hq : 0 < labels.length)
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (a : ℕ) (ha : a < n) :
        let ctx := fun k => dispatchContext n labels x start rows answer k
        let V := fun k => (uncovered labels (ctx k).1 (ctx k).2.1 j).length
        V (a+1) ≤ V a ∧
          ((∃ i, (ctx a).2.2.1 = some i ∧ i ≤ j) →
            assignmentChoice n labels x start rows answer a ∈
              (uncovered labels (ctx a).1.toFinset.toList (ctx a).2.1 j).toFinset →
            V (a+1) < V a) := by
      classical
      dsimp only
      let s := fullInitial n labels x start rows
      let p := fun i : Fin n => if i.val < a then s.pending i else none
      let p' := fun i : Fin n => if i.val < a+1 then s.pending i else none
      let i : Fin n := ⟨a,ha⟩
      have hi : p i = none := by dsimp only [p,i]; rw [ite_eq_right (Nat.lt_irrefl a)]
      have he : labels.isEmpty = false := by
        cases hh : labels with
        | nil => simp only [hh,List.length_nil] at hq; omega
        | cons b bs => rfl
      have hctx : dispatchContext n labels x start rows answer a = (List.range labels.length,p,some i,start) := by
        delta dispatchContext
        rw [dite_eq_left ha,he,ite_eq_right Bool.false_ne_true]
      have hp : Function.update p i (dispatch (Sum.inl x) start a
          (selectedLabel labels (List.range labels.length) (rows a))) = p' := by
        have h := freyaDevelopmentInitialPending s.pending a ha
        change Function.update p i (s.pending i) = p' at h
        have hjob : s.pending i = dispatch (Sum.inl x) start a
            (selectedLabel labels (List.range labels.length) (rows a)) := by
          dsimp only [s,fullInitial,i]
          simp only [Nat.zero_add]
        rw [hjob] at h
        exact h
      have hdec := freyaDevelopmentDispatchDecrease labels (List.range labels.length)
        (fun b hb => List.mem_range.mp hb) List.nodup_range p j i hi (Sum.inl x) start a (rows a)
      dsimp only at hdec
      rw [hp] at hdec
      have hnext : (uncovered labels (dispatchContext n labels x start rows answer (a+1)).1
          (dispatchContext n labels x start rows answer (a+1)).2.1 j).length ≤
          (uncovered labels (List.range labels.length) p' j).length := by
        by_cases hlt : a+1<n
        · have hc : dispatchContext n labels x start rows answer (a+1) =
              (List.range labels.length,p',some ⟨a+1,hlt⟩,start) := by
            delta dispatchContext
            rw [dite_eq_left hlt,he,ite_eq_right Bool.false_ne_true]
          rw [hc]
        · have han : a+1=n := by omega
          have hpall : p' = s.pending := by
            funext b
            dsimp only [p']
            rw [ite_eq_left (show b.val<a+1 by rw [han]; exact b.isLt)]
          rw [hpall,han]
          have h := freyaDevelopmentCompletionDecrease n hn labels x start rows f τ answer hservice j 0
          rw [Nat.add_zero] at h
          exact h
      rw [hctx]
      dsimp only
      refine ⟨hnext.trans hdec.1,?_⟩
      intro hflag hhit
      obtain ⟨i',hi',hij'⟩ := hflag
      have hij : i ≤ j := (Option.some.inj hi') ▸ hij'
      have hchoice : assignmentChoice n labels x start rows answer a =
          (chooseRemaining (rows a) (List.range labels.length)).getD 0 := by
        delta assignmentChoice
        rw [hctx]
      rw [hchoice] at hhit
      exact hnext.trans_lt (hdec.2 hij hhit)
    have freyaDevelopmentCouponActual {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (hq : 0 < labels.length)
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hservice : ∀ᵐ ω ∂(P : Measure Ω), servicePath f τ (fun a r => answer a r ω))
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n) (u : ℕ) (hu : 0 < u) :
        (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
          ∂(P : Measure Ω)) ≤ 1+(min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞) := by
      apply freyaDevelopmentCouponFromDynamics P n labels x start rows answer hfresh j u hu
      filter_upwards [hservice] with ω hs
      dsimp only
      have hstep (a : ℕ) := by
        by_cases ha : a < n
        · exact freyaDevelopmentInitialDynamics n hn labels hq x start (rows ω) f τ
            (fun k r => answer k r ω) hs j a ha
        · have h := freyaDevelopmentLaterDynamics n hn labels x start (rows ω) f τ
            (fun k r => answer k r ω) hs j (a-n)
          rw [show n+(a-n)=a by omega] at h
          exact h
      exact ⟨antitone_nat_of_succ_le (fun a => (hstep a).1),fun a => (hstep a).2⟩
    exact freyaDevelopmentCouponActual P n hn labels hq x start rows f τ answer hservice hfresh j u hu


theorem capacity_bound {d m : ℕ} (n : ℕ) (hn : 0 < n)
    (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) (j : Fin n) :
    (((fullTrace n labels x start rows answer (n * labels.length)).clock - start : ℝ≥0) : ℝ≥0∞) ≤
      ((couponWork n labels x start rows answer j + (j.val + 1) : ℕ) : ℝ≥0∞) /
        (∑ i ∈ Finset.Iic j, (τ i)⁻¹) + τ j := by
  set_option maxHeartbeats 1600000 in
  open scoped BigOperators ENNReal NNReal in
    have freyaDevelopmentEraseMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (b : β) (l : List α) :
        ((l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)).map φ = (l.map φ).erase b := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        by_cases ha : φ a = b
        · simp [ha]
        · cases hf : l.find? (fun a => decide (φ a = b)) with
          | none =>
            have hnot : b ∉ l.map φ := by
              intro hb
              obtain ⟨v,hv,heq⟩ := List.mem_map.mp hb
              have h := List.find?_eq_none.mp hf v hv
              simp only [heq,decide_true,not_true_eq_false] at h
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_none,
              List.map_cons]
            rw [List.erase_of_not_mem (by simpa only [List.mem_cons,not_or] using And.intro (Ne.symm ha) hnot)]
          | some v =>
            have hv : φ v = b := by
              have h := List.find?_some hf
              simpa only [decide_eq_true_eq] using h
            have hva : v ≠ a := by intro h; subst v; exact ha hv
            have hi := ih
            rw [hf] at hi
            simp only [Option.elim_some] at hi
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_some,
              List.map_cons]
            rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using Ne.symm hva), List.map_cons,hi,List.erase_cons_tail (by simpa only [beq_iff_eq] using ha)]
    have freyaDevelopmentEraseFoldCount {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) l).count b = l.count b - jobs.count b := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        by_cases hab : a = b
        · subst a
          simp only [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne (Ne.symm hab)]
          simp only [List.count_cons,hab,beq_iff_eq,ite_false]
          omega
    have freyaDevelopmentEraseFoldLength {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) :
        (jobs.foldl (fun rem a => rem.erase a) l).length ≤ l.length ∧
          l.length ≤ (jobs.foldl (fun rem a => rem.erase a) l).length + jobs.length := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        obtain ⟨h₁,h₂⟩ := ih (l.erase a)
        have hlen : (l.erase a).length ≤ l.length := List.length_erase_le
        have hlen' : l.length ≤ (l.erase a).length + 1 := by
          by_cases ha : a ∈ l
          · rw [List.length_erase_of_mem ha]
            omega
          · rw [List.erase_of_not_mem ha]
            omega
        simpa only [List.foldl_cons,List.length_cons] using And.intro (h₁.trans hlen) (by omega)
    have freyaDevelopmentEraseFoldMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (jobs : List β) (l : List α) :
        (jobs.foldl (fun rem b => (rem.find? fun a => decide (φ a = b)).elim rem
          (fun a => rem.erase a)) l).map φ =
          jobs.foldl (fun rem b => rem.erase b) (l.map φ) := by
      induction jobs generalizing l with
      | nil => rfl
      | cons b jobs ih =>
        simp only [List.foldl_cons]
        rw [ih,freyaDevelopmentEraseMap]
    have freyaDevelopmentFilterMapFold {ι α β : Type}
        (f : List α → β → List α) (p : ι → Option β) (workers : List ι) (l : List α) :
        workers.foldl (fun rem i => (p i).elim rem (f rem)) l =
          (workers.filterMap p).foldl f l := by
      induction workers generalizing l with
      | nil => rfl
      | cons i workers ih =>
        simp (config := { iota := false }) only [List.foldl_cons,List.filterMap_cons]
        cases hp : p i with
        | none => exact ih l
        | some b => exact ih (f l b)
    have freyaDevelopmentEraseFoldPerm {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs jobs' l l' : List α) (hj : jobs.Perm jobs') (hl : l.Perm l') :
        (jobs.foldl (fun rem a => rem.erase a) l).Perm
          (jobs'.foldl (fun rem a => rem.erase a) l') := by
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentEraseFoldCount,freyaDevelopmentEraseFoldCount,
        hl.count_eq b,hj.count_eq b]
    have freyaDevelopmentUncoveredCounts {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (b : Option (Fin m)) :
        ((uncovered labels rem pending j).map (fun a => labels[a]?)).count b =
          (rem.map (fun a => labels[a]?)).count b -
            ((((List.finRange n).filter fun i => decide (i ≤ j)).filterMap
              (fun i => (pending i).map fun job => some job.component)).count b) := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let φ := fun a : ℕ => labels[a]?
      let p := fun i => (pending i).map fun job => some job.component
      let eraseOne := fun (l : List ℕ) (b : Option (Fin m)) =>
        (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)
      have hf : (fun (l : List ℕ) i => (pending i).elim l fun job =>
          (l.find? fun a => decide (labels[a]? = some job.component)).elim l
            (fun a => l.erase a)) = (fun l i => (p i).elim l (eraseOne l)) := by
        funext l i
        dsimp only [p]
        cases hp : pending i with
        | none => rfl
        | some job => rfl
      have heq : uncovered labels rem pending j = (workers.filterMap p).foldl eraseOne rem := by
        delta uncovered
        rw [hf]
        exact freyaDevelopmentFilterMapFold eraseOne p workers rem
      rw [heq]
      change ((workers.filterMap p).foldl
        (fun l b => (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)) rem
          |>.map φ |>.count b) = _
      rw [freyaDevelopmentEraseFoldMap]
      exact freyaDevelopmentEraseFoldCount (workers.filterMap p) (rem.map φ) b
    have freyaDevelopmentEraseFoldDemand {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) (l.erase b)).Perm
          ((jobs.foldl (fun rem a => rem.erase a) l).erase b) := by
      apply List.perm_iff_count.mpr
      intro a
      rw [freyaDevelopmentEraseFoldCount]
      by_cases ha : a = b
      · subst a
        rw [List.count_erase_self,List.count_erase_self,freyaDevelopmentEraseFoldCount]
        omega
      · rw [List.count_erase_of_ne ha,List.count_erase_of_ne ha,freyaDevelopmentEraseFoldCount]
    have freyaDevelopmentContextSublist {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
        (dispatchContext n labels x start rows answer a).1.Sublist (List.range labels.length) := by
      classical
      have hup (s : FullState d m n) (reply : Reply d n) (hs : s.remaining.Sublist (List.range labels.length)) :
          (fullUpdate s reply).remaining.Sublist (List.range labels.length) := by
        delta fullUpdate
        by_cases he : s.remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact hs
        · rw [ite_eq_right he]
          cases reply with
          | none => exact hs
          | some reply =>
            obtain ⟨i,id,c,value⟩ := reply
            dsimp only
            cases hp : s.pending i with
            | none => exact hs
            | some job =>
              dsimp only
              split
              · dsimp only
                cases hf : s.remaining.find? (fun b => decide (s.original[b]? = some job.component)) with
                | none => exact hs
                | some b => exact List.erase_sublist.trans hs
              · exact hs
      have htrace : ∀ k, (fullTrace n labels x start rows answer k).remaining.Sublist (List.range labels.length) := by
        intro k
        induction k with
        | zero => exact List.Sublist.refl _
        | succ k ih => exact hup _ _ ih
      delta dispatchContext
      by_cases ha : a < n
      · rw [dite_eq_left ha]
      · rw [dite_eq_right ha]
        dsimp only
        have h := hup (fullTrace n labels x start rows answer (a-n))
          (answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n)))) (htrace (a-n))
        cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
        | none => simpa only [hr] using h
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          simpa only [hr] using h
    have freyaDevelopmentUncoveredSublist {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        (uncovered labels rem pending j).Sublist rem := by
      classical
      have h (workers : List (Fin n)) (l : List ℕ) :
          (workers.foldl (fun rem i => (pending i).elim rem fun job =>
            (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem
              (fun a => rem.erase a)) l).Sublist l := by
        induction workers generalizing l with
        | nil => exact List.Sublist.refl _
        | cons i workers ih =>
          rw [List.foldl_cons]
          cases hp : pending i with
          | none => exact ih l
          | some job =>
            simp only [Option.elim_some]
            cases hf : l.find? (fun a => decide (labels[a]? = some job.component)) with
            | none => exact ih l
            | some a => exact (ih (l.erase a)).trans List.erase_sublist
      exact h _ _
    have freyaDevelopmentFilterMapCount {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (b : α) :
        (workers.filterMap p).count b = ∑ i ∈ workers.toFinset, if p i = some b then 1 else 0 := by
      induction workers with
      | nil => simp
      | cons i workers ih =>
        obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
        have hind := ih hn
        rw [List.toFinset_cons,Finset.sum_insert (by simpa only [List.mem_toFinset] using hi),
          List.filterMap_cons]
        cases hp : p i with
        | none =>
          dsimp only
          rw [ite_eq_right (Ne.symm (Option.some_ne_none b)),Nat.zero_add]
          exact hind
        | some a =>
          dsimp only
          rw [List.count_cons,hind]
          simp only [beq_iff_eq,Option.some.injEq,Nat.add_comm]
    have freyaDevelopmentFilterMapRemovePerm {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (i : ι) (hi : i ∈ workers) (b : α) (hb : p i = some b) :
        (workers.filterMap p).Perm (b :: workers.filterMap (Function.update p i none)) := by
      classical
      apply List.perm_iff_count.mpr
      intro c
      rw [List.count_cons,freyaDevelopmentFilterMapCount workers hn,
        freyaDevelopmentFilterMapCount workers hn]
      have hiS : i ∈ workers.toFinset := List.mem_toFinset.mpr hi
      have hold := Finset.sum_erase_add workers.toFinset (fun k => if p k = some c then 1 else 0) hiS
      have hnew := Finset.sum_erase_add workers.toFinset
        (fun k => if Function.update p i none k = some c then (1 : ℕ) else 0) hiS
      have heq : (∑ k ∈ workers.toFinset.erase i,
          if Function.update p i none k = some c then (1 : ℕ) else 0) =
          ∑ k ∈ workers.toFinset.erase i, if p k = some c then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
      rw [Function.update_self,ite_eq_right (Ne.symm (Option.some_ne_none c)),Nat.add_zero,heq] at hnew
      rw [← hold,← hnew,hb]
      simp only [Option.some.injEq,beq_iff_eq]
    have freyaDevelopmentFilterMapReplacePerm {ι α : Type} [DecidableEq ι] [DecidableEq α]
        [BEq α] [LawfulBEq α] (workers : List ι) (hn : workers.Nodup)
        (p : ι → Option α) (i : ι) (hi : i ∈ workers) (hb : p i = none) (b : α) :
        (workers.filterMap (Function.update p i (some b))).Perm (b :: workers.filterMap p) := by
      have h := freyaDevelopmentFilterMapRemovePerm workers hn (Function.update p i (some b)) i hi b
        (Function.update_self _ _ _)
      have heq : Function.update (Function.update p i (some b)) i none = p := by
        rw [Function.update_idem]
        funext k
        by_cases hk : k = i
        · subst k
          rw [Function.update_self,hb]
        · rw [Function.update_of_ne hk]
      rw [heq] at h
      exact h
    have freyaDevelopmentUncoveredLabelsPerm {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) :
        ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          ((((List.finRange n).filter (fun i => decide (i ≤ j))).filterMap
            (fun i => (pending i).map fun job => some job.component)).foldl
              (fun l b => l.erase b) (rem.map fun a => labels[a]?)) := by
      classical
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentEraseFoldCount]
    have freyaDevelopmentPrefixCompletion {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : i ≤ j) (job : Job d m) (hi : pending i = some job) :
        (uncovered labels
          ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
          (Function.update pending i none) j).length = (uncovered labels rem pending j).length := by
      classical
      let workers := (List.finRange n).filter fun k => decide (k ≤ j)
      let p := fun k => (pending k).map fun job => some job.component
      let p' := fun k => (Function.update pending i none k).map fun job => some job.component
      let vals := rem.map fun a => labels[a]?
      let b := some job.component
      have hn : workers.Nodup := (List.nodup_finRange n).filter _
      have hiw : i ∈ workers := by simp only [workers,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]; exact hij
      have hp : p i = some b := by dsimp only [p]; rw [hi]; rfl
      have hp' : p' = Function.update p i none := by
        funext k
        by_cases hk : k = i
        · subst k
          dsimp only [p']
          rw [Function.update_self,Function.update_self]
          rfl
        · dsimp only [p',p]
          rw [Function.update_of_ne hk,Function.update_of_ne hk]
      have hperm := freyaDevelopmentFilterMapRemovePerm workers hn p i hiw b hp
      rw [← hp'] at hperm
      have hfold := freyaDevelopmentEraseFoldPerm (workers.filterMap p) (b :: workers.filterMap p') vals vals
        hperm (List.Perm.refl _)
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels
        ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
        (Function.update pending i none) j
      have hmap := freyaDevelopmentEraseMap (fun a : ℕ => labels[a]?) b rem
      change (List.map (fun a => labels[a]?) _).Perm
        (List.foldl (fun l b => l.erase b) (List.map (fun a => labels[a]?) _) (workers.filterMap p')) at hnew
      rw [hmap] at hnew
      have hall := hold.trans hfold
      change ((uncovered labels rem pending j).map (fun a => labels[a]?)).Perm
        (List.foldl (fun l b => l.erase b) (vals.erase b) (workers.filterMap p')) at hall
      have hlen := (hnew.trans hall.symm).length_eq
      simpa only [List.length_map] using hlen
    have freyaDevelopmentPrefixAssignment {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : i ≤ j) (hi : pending i = none) (job : Job d m) :
        (uncovered labels rem (Function.update pending i (some job)) j).length ≤
          (uncovered labels rem pending j).length ∧
        (some job.component ∈ (uncovered labels rem pending j).map (fun a => labels[a]?) →
          (uncovered labels rem (Function.update pending i (some job)) j).length+1 =
            (uncovered labels rem pending j).length) := by
      classical
      let workers := (List.finRange n).filter fun k => decide (k ≤ j)
      let p := fun k => (pending k).map fun job => some job.component
      let p' := fun k => (Function.update pending i (some job) k).map fun job => some job.component
      let vals := rem.map fun a => labels[a]?
      let b := some job.component
      have hn : workers.Nodup := (List.nodup_finRange n).filter _
      have hiw : i ∈ workers := by simp only [workers,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]; exact hij
      have hp : p i = none := by dsimp only [p]; rw [hi]; rfl
      have hp' : p' = Function.update p i (some b) := by
        funext k
        by_cases hk : k = i
        · subst k
          dsimp only [p']
          rw [Function.update_self,Function.update_self]
          rfl
        · dsimp only [p',p]
          rw [Function.update_of_ne hk,Function.update_of_ne hk]
      have hperm := freyaDevelopmentFilterMapReplacePerm workers hn p i hiw hp b
      rw [← hp'] at hperm
      have hfold := freyaDevelopmentEraseFoldPerm (workers.filterMap p') (b :: workers.filterMap p) vals vals
        hperm (List.Perm.refl _)
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels rem (Function.update pending i (some job)) j
      have hafter := hnew.trans hfold
      change ((uncovered labels rem (Function.update pending i (some job)) j).map fun a => labels[a]?).Perm
        (List.foldl (fun l b => l.erase b) (vals.erase b) (workers.filterMap p)) at hafter
      have hres := (hafter.trans (freyaDevelopmentEraseFoldDemand (workers.filterMap p) vals b)).trans
        (hold.erase b).symm
      have hlen := hres.length_eq
      simp only [List.length_map] at hlen
      refine ⟨?_,?_⟩
      · rw [hlen]
        exact List.length_erase_le.trans_eq (List.length_map _)
      · intro hb
        rw [hlen,List.length_erase_of_mem hb,List.length_map]
        have hpos := List.length_pos_of_mem hb
        simp only [List.length_map] at hpos
        omega
    have freyaDevelopmentUncoveredSamePrefix {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending pending' : Fin n → Option (Job d m)) (j : Fin n)
        (hp : ∀ i, i ≤ j → (pending i).map (fun job => job.component) =
          (pending' i).map (fun job => job.component)) :
        ((uncovered labels rem pending j).map fun a => labels[a]?).Perm
          ((uncovered labels rem pending' j).map fun a => labels[a]?) := by
      classical
      have hf (workers : List (Fin n))
          (hw : ∀ i ∈ workers, (pending i).map (fun job => some job.component) =
            (pending' i).map (fun job => some job.component)) :
          workers.filterMap (fun i => (pending i).map fun job => some job.component) =
            workers.filterMap (fun i => (pending' i).map fun job => some job.component) := by
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          have hhead := hw i List.mem_cons_self
          have htail := ih (fun k hk => hw k (List.mem_cons_of_mem _ hk))
          rw [List.filterMap_cons,List.filterMap_cons,hhead,htail]
      have hworkers := hf ((List.finRange n).filter fun i => decide (i ≤ j)) (by
        intro i hi
        have h := hp i (of_decide_eq_true (List.mem_filter.mp hi).2)
        have hh := congrArg (Option.map some) h
        simpa only [Option.map_map,Function.comp_def] using hh)
      apply List.perm_iff_count.mpr
      intro b
      rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,hworkers]
    have freyaDevelopmentOutsideCompletion {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hij : ¬ i ≤ j) (job : Job d m) :
        (uncovered labels
          ((rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a))
          (Function.update pending i none) j).length ≤ (uncovered labels rem pending j).length := by
      classical
      let rem' := (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a)
      have hsame := freyaDevelopmentUncoveredSamePrefix labels rem' (Function.update pending i none) pending j (by
        intro k hk
        have hki : k ≠ i := by intro h; subst k; exact hij hk
        rw [Function.update_of_ne hki])
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels rem' pending j
      have hmap := freyaDevelopmentEraseMap (fun a : ℕ => labels[a]?) (some job.component) rem
      change (List.map (fun a => labels[a]?) rem') = _ at hmap
      rw [hmap] at hnew
      have hafter := (hnew.trans (freyaDevelopmentEraseFoldDemand _ _ _)).trans
        (hold.erase (some job.component)).symm
      have hlen := (hsame.trans hafter).length_eq
      simp only [List.length_map] at hlen
      rw [hlen]
      exact List.length_erase_le.trans_eq (List.length_map _)
    have freyaDevelopmentFullMetadata {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (a : ℕ) :
        let s := fullTrace n labels x start rows answer a
        s.original = labels ∧ s.rows = rows ∧ (s.remaining ≠ [] → s.nextID = n+a) := by
      classical
      let tr := fullTrace n labels x start rows answer
      have hstatic : ∀ k, (tr k).original = labels ∧ (tr k).rows = rows := by
        intro k
        induction k with
        | zero => exact ⟨rfl,rfl⟩
        | succ k ih =>
          change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).original = labels ∧
            (fullUpdate (tr k) (answer k (fullQuery (tr k)))).rows = rows
          delta fullUpdate
          by_cases he : (tr k).remaining.isEmpty = true
          · rw [ite_eq_left he]
            exact ih
          · rw [ite_eq_right he]
            cases hr : answer k (fullQuery (tr k)) with
            | none => exact ih
            | some reply =>
              obtain ⟨i,id,c,value⟩ := reply
              dsimp only
              cases hp : (tr k).pending i with
              | none => exact ih
              | some job =>
                dsimp only
                split <;> exact ih
      have halt (s : FullState d m n) (he : s.remaining = []) (reply : Reply d n) :
          fullUpdate s reply = s := by
        delta fullUpdate
        rw [he]
        dsimp only [List.isEmpty]
        rw [ite_eq_left rfl]
      have hnext : ∀ k, (tr k).remaining ≠ [] → (tr k).nextID = n+k := by
        intro k
        induction k with
        | zero => intro _; change 0+n=n+0; omega
        | succ k ih =>
          intro hne
          have hprev : (tr k).remaining ≠ [] := by
            intro he
            have hh := halt (tr k) he (answer k (fullQuery (tr k)))
            change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).remaining ≠ [] at hne
            rw [hh] at hne
            exact hne he
          have hinv := full_invariant n hn labels x start rows f τ answer hservice k
          let r : Request d m n := ⟨(tr k).clock,(tr k).pending⟩
          have hlegal : legalRequest τ r := hinv.2.2.2.2.1 hprev
          have he : (tr k).remaining.isEmpty = false := by
            cases hh : (tr k).remaining with
            | nil => exact (hprev hh).elim
            | cons b bs => rfl
          have hquery : fullQuery (tr k) = some r := by
            delta fullQuery
            rw [he,ite_eq_right Bool.false_ne_true]
            delta pendingRequest
            have hx : ∃ i, (tr k).pending i ≠ none := by
              obtain ⟨i,job,hj⟩ := hlegal.1
              exact ⟨i,by change (tr k).pending i = some job at hj; rw [hj]; exact Option.some_ne_none job⟩
            rw [ite_eq_left hx]
          obtain ⟨i,job,c,hj,hr,hc,_⟩ := (hservice k).2 r hlegal
          change (tr k).pending i = some job at hj
          change (tr k).clock ≤ c at hc
          change (fullUpdate (tr k) (answer k (fullQuery (tr k)))).nextID = n+(k+1)
          rw [hquery,hr]
          delta fullUpdate
          rw [he,ite_eq_right Bool.false_ne_true]
          dsimp only
          rw [hj]
          dsimp only
          rw [ite_eq_left (And.intro rfl hc)]
          change (tr k).nextID+1=n+(k+1)
          rw [ih hprev]
          omega
      exact ⟨(hstatic a).1,(hstatic a).2,hnext a⟩
    have freyaDevelopmentActiveDispatch {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (hne : (fullTrace n labels x start rows answer k).remaining ≠ []) :
        let s := fullTrace n labels x start rows answer k
        ∃ i job c, s.pending i = some job ∧
          let rem := (s.remaining.find? fun a => decide (labels[a]? = some job.component)).elim
            s.remaining (fun a => s.remaining.erase a)
          let next := dispatch (Sum.inl s.point) c (n+k) (selectedLabel labels rem (rows (n+k)))
          dispatchContext n labels x start rows answer (n+k) =
            (rem,Function.update s.pending i none,(if rem.isEmpty then none else some i),c) ∧
          (fullTrace n labels x start rows answer (k+1)).remaining = rem ∧
          (fullTrace n labels x start rows answer (k+1)).pending = Function.update s.pending i next := by
      classical
      let s := fullTrace n labels x start rows answer k
      have hmeta := freyaDevelopmentFullMetadata n hn labels x start rows f τ answer hservice k
      change s.original = labels ∧ s.rows = rows ∧ (s.remaining ≠ [] → s.nextID = n+k) at hmeta
      have hinv := full_invariant n hn labels x start rows f τ answer hservice k
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := hinv.2.2.2.2.1 hne
      have he : s.remaining.isEmpty = false := by
        cases hh : s.remaining with
        | nil => exact (hne hh).elim
        | cons a as => rfl
      have hquery : fullQuery s = some r := by
        delta fullQuery
        rw [he,ite_eq_right Bool.false_ne_true]
        delta pendingRequest
        have hx : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          exact ⟨i,by change s.pending i = some job at hj; rw [hj]; exact Option.some_ne_none job⟩
        rw [ite_eq_left hx]
      obtain ⟨i,job,c,hj,hr,hc,_⟩ := (hservice k).2 r hlegal
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      refine ⟨i,job,c,hj,?_⟩
      let found := s.remaining.find? fun a => decide (labels[a]? = some job.component)
      let rem := found.elim s.remaining (fun a => s.remaining.erase a)
      let next := dispatch (Sum.inl s.point) c (n+k) (selectedLabel labels rem (rows (n+k)))
      let t : FullState d m n := {s with
        remaining := rem
        sum := if found.isSome then s.sum+jobValue f job else s.sum
        pending := Function.update s.pending i next
        clock := c
        nextID := s.nextID+1}
      have hup : fullUpdate s (answer k (fullQuery s)) = t := by
        rw [hquery,hr]
        delta fullUpdate
        rw [he,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
        dsimp only [t,next,rem,found]
        rw [hmeta.1,hmeta.2.1,hmeta.2.2 hne]
      have htrace : fullTrace n labels x start rows answer (k+1) = t := hup
      refine ⟨?_,?_,?_⟩
      · delta dispatchContext
        rw [dite_eq_right (show ¬n+k<n by omega)]
        dsimp only
        rw [show n+k-n=k by omega]
        change (let reply := answer k (fullQuery s)
          let v := fullUpdate s reply
          _) = _
        rw [hup,hquery,hr]
      · rw [htrace]
      · rw [htrace]
    have freyaDevelopmentUncoveredEmpty {d m n : ℕ} (labels : List (Fin m))
        (pending : Fin n → Option (Job d m)) (j : Fin n) :
        uncovered labels [] pending j = [] := by
      exact List.sublist_nil.mp (freyaDevelopmentUncoveredSublist labels [] pending j)
    have freyaDevelopmentChosenLabel {m : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (hb : ∀ a ∈ rem, a < labels.length) (hne : rem ≠ []) (row : ChoiceRow) :
        ∃ a b, chooseRemaining row rem = some a ∧ a ∈ rem ∧ labels[a]? = some b ∧
          selectedLabel labels rem row = some b := by
      have hlen : rem.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
      let index := row (rem.length-1)
      have hi : index.val < rem.length := by have hh := index.isLt; omega
      let a := rem.get ⟨index.val,hi⟩
      have ha : a ∈ rem := List.get_mem _ _
      have ha' := hb a ha
      refine ⟨a,labels[a],?_,ha,?_,?_⟩
      · delta chooseRemaining
        rw [dite_eq_right hlen]
      · exact List.getElem?_eq_getElem ha'
      · delta selectedLabel
        have hc : chooseRemaining row rem = some a := by
          delta chooseRemaining
          rw [dite_eq_right hlen]
        rw [hc]
        exact List.getElem?_eq_getElem ha'
    have freyaDevelopmentEmptyTraceContext {d m : ℕ} (n : ℕ)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (he : (fullTrace n labels x start rows answer k).remaining = []) :
        (dispatchContext n labels x start rows answer (n+k)).1 = [] ∧
        (fullTrace n labels x start rows answer (k+1)).remaining = [] := by
      let s := fullTrace n labels x start rows answer k
      have hquery : fullQuery s = none := by
        delta fullQuery
        change s.remaining = [] at he
        rw [he]
        rfl
      have hup : fullUpdate s (answer k (fullQuery s)) = s := by
        delta fullUpdate
        change s.remaining = [] at he
        rw [he]
        rfl
      refine ⟨?_,?_⟩
      · delta dispatchContext
        rw [dite_eq_right (show ¬ n+k<n by omega)]
        dsimp only
        rw [show n+k-n=k by omega]
        change (let reply := answer k (fullQuery s)
          let t := fullUpdate s reply
          (_ : List ℕ)) = []
        rw [hup,hquery,(hservice k).1]
        exact he
      · change (fullUpdate s (answer k (fullQuery s))).remaining = []
        rw [hup]
        exact he
    have freyaDevelopmentAllPending {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (hne : (fullTrace n labels x start rows answer k).remaining ≠ []) :
        ∀ i, ∃ job, (fullTrace n labels x start rows answer k).pending i = some job := by
      classical
      induction k with
      | zero =>
        intro i
        have hb : ∀ a ∈ List.range labels.length, a < labels.length := fun a ha => List.mem_range.mp ha
        obtain ⟨a,b,_,_,_,hs⟩ := freyaDevelopmentChosenLabel labels (List.range labels.length) hb hne (rows i.val)
        refine ⟨⟨b,Sum.inl x,start,i.val⟩,?_⟩
        change dispatch (Sum.inl x) start (0+i.val)
          (selectedLabel labels (List.range labels.length) (rows (0+i.val))) = _
        rw [Nat.zero_add,hs]
        rfl
      | succ k ih =>
        have hprev : (fullTrace n labels x start rows answer k).remaining ≠ [] := by
          intro he
          exact hne (freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he).2
        obtain ⟨i,job,c,hj,hctx,hrem,hpending⟩ :=
          freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k hprev
        have hb := (full_invariant n hn labels x start rows f τ answer hservice (k+1)).2.1
        rw [hrem] at hb hne
        obtain ⟨a,b,_,_,_,hs⟩ := freyaDevelopmentChosenLabel labels _ hb hne (rows (n+k))
        intro l
        rw [hpending,hs]
        by_cases hl : l = i
        · subst l
          rw [Function.update_self]
          exact ⟨_,rfl⟩
        · rw [Function.update_of_ne hl]
          exact ih hprev l
    have freyaDevelopmentServiceClock {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (hne : (fullTrace n labels x start rows answer k).remaining ≠ []) :
        let s := fullTrace n labels x start rows answer k
        let t := fullTrace n labels x start rows answer (k+1)
        s.clock ≤ t.clock ∧
          ∀ i job, s.pending i = some job → (t.clock : ℝ≥0∞) ≤ (job.started : ℝ≥0∞)+τ i := by
      let s := fullTrace n labels x start rows answer k
      have hinv := full_invariant n hn labels x start rows f τ answer hservice k
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := hinv.2.2.2.2.1 hne
      have he : s.remaining.isEmpty = false := by
        cases hh : s.remaining with
        | nil => exact (hne hh).elim
        | cons a as => rfl
      have hquery : fullQuery s = some r := by
        delta fullQuery
        rw [he,ite_eq_right Bool.false_ne_true]
        delta pendingRequest
        have hx : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          exact ⟨i,by change s.pending i = some job at hj; rw [hj]; exact Option.some_ne_none job⟩
        rw [ite_eq_left hx]
      obtain ⟨i,job,c,hj,hr,hc,hdeadline⟩ := (hservice k).2 r hlegal
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      have hclock : (fullTrace n labels x start rows answer (k+1)).clock = c := by
        change (fullUpdate s (answer k (fullQuery s))).clock = c
        rw [hquery,hr]
        delta fullUpdate
        rw [he,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
      dsimp only
      rw [hclock]
      refine ⟨hc,?_⟩
      intro l old hold
      have hkind := (hinv.2.2.2.2.2.1 l old hold).1
      have h := hdeadline l old hold
      change (c : ℝ≥0∞) ≤ (old.started : ℝ≥0∞)+(jobWork old : ℕ)*τ l at h
      have hw : jobWork old = 1 := by delta jobWork; rw [hkind]
      simpa only [hw,Nat.cast_one,one_mul] using h
    have freyaDevelopmentDemandDecrease {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n) (b : Fin m) :
        (uncovered labels ((rem.find? fun a => decide (labels[a]? = some b)).elim rem
          (fun a => rem.erase a)) pending j).length ≤ (uncovered labels rem pending j).length := by
      classical
      have hold := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      have hnew := freyaDevelopmentUncoveredLabelsPerm labels
        ((rem.find? fun a => decide (labels[a]? = some b)).elim rem (fun a => rem.erase a)) pending j
      rw [freyaDevelopmentEraseMap (fun a : ℕ => labels[a]?) (some b) rem] at hnew
      have h := (hnew.trans (freyaDevelopmentEraseFoldDemand _ _ _)).trans (hold.erase (some b)).symm
      have hlen := h.length_eq
      simp only [List.length_map] at hlen
      rw [hlen]
      exact List.length_erase_le.trans_eq (List.length_map _)
    have freyaDevelopmentAssignmentNonincrease {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (hi : pending i = none) (next : Option (Job d m)) :
        (uncovered labels rem (Function.update pending i next) j).length ≤
          (uncovered labels rem pending j).length := by
      classical
      cases next with
      | none =>
        have hp : Function.update pending i none = pending := by
          funext k
          by_cases hk : k = i
          · subst k; rw [Function.update_self,hi]
          · rw [Function.update_of_ne hk]
        rw [hp]
      | some job =>
        by_cases hij : i ≤ j
        · exact (freyaDevelopmentPrefixAssignment labels rem pending j i hij hi job).1
        · have hp := freyaDevelopmentUncoveredSamePrefix labels rem
            (Function.update pending i (some job)) pending j (by
              intro k hk
              rw [Function.update_of_ne (show k ≠ i by intro h; subst k; exact hij hk)])
          have h := hp.length_eq
          simpa only [List.length_map] using h.le
    have freyaDevelopmentCoveredPending {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (hne : rem ≠ []) (hcover : uncovered labels rem pending j = []) :
        ∃ i job, i ≤ j ∧ pending i = some job := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let jobs := workers.filterMap (fun i => (pending i).map fun job => some job.component)
      have hperm := freyaDevelopmentUncoveredLabelsPerm labels rem pending j
      rw [hcover] at hperm
      have hlen := (freyaDevelopmentEraseFoldLength jobs (rem.map fun a => labels[a]?)).2
      have hzero : (List.foldl (fun l b => l.erase b) (rem.map fun a => labels[a]?) jobs).length = 0 :=
        hperm.length_eq.symm
      rw [hzero,List.length_map,Nat.zero_add] at hlen
      have hjobs : jobs ≠ [] := by
        intro he
        rw [he,List.length_nil] at hlen
        exact hne (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen))
      obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil jobs hjobs
      obtain ⟨i,hi,hval⟩ := List.mem_filterMap.mp hb
      have hij : i ≤ j := of_decide_eq_true (List.mem_filter.mp hi).2
      cases hp : pending i with
      | none => simp only [hp,Option.map_none] at hval; cases hval
      | some job => exact ⟨i,job,hij,hp⟩
    have freyaDevelopmentFilterUpdate {α ι : Type} [DecidableEq ι]
        (pending : ι → Option α) (i : ι) (next : Option α) (P : α → Bool) :
        (fun k => (Function.update pending i next k).filter P) =
          Function.update (fun k => (pending k).filter P) i (next.filter P) := by
      funext k
      by_cases hk : k = i
      · subst k; rw [Function.update_self,Function.update_self]
      · rw [Function.update_of_ne hk,Function.update_of_ne hk]
    have freyaDevelopmentFilteredCompletion {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j i : Fin n)
        (job : Job d m) (hi : pending i = some job) (P : Job d m → Bool) :
        let rem' := (rem.find? fun a => decide (labels[a]? = some job.component)).elim rem (fun a => rem.erase a)
        (uncovered labels rem' (fun k => (Function.update pending i none k).filter P) j).length ≤
          (uncovered labels rem (fun k => (pending k).filter P) j).length := by
      classical
      dsimp only
      rw [freyaDevelopmentFilterUpdate]
      dsimp only [Option.filter_none]
      by_cases hij : i ≤ j
      · by_cases hP : P job = true
        · have hjob : (pending i).filter P = some job := by rw [hi]; simp only [Option.filter_some,hP,ite_true]
          exact (freyaDevelopmentPrefixCompletion labels rem _ j i hij job hjob).le
        · have hjob : (pending i).filter P = none := by
            rw [hi]
            simp only [Option.filter_some,hP,Bool.false_eq_true,ite_false]
          have hp : Function.update (fun k => (pending k).filter P) i none =
              (fun k => (pending k).filter P) := by
            funext k
            by_cases hk : k = i
            · subst k; rw [Function.update_self,hjob]
            · rw [Function.update_of_ne hk]
          rw [hp]
          exact freyaDevelopmentDemandDecrease labels rem _ j job.component
      · exact freyaDevelopmentOutsideCompletion labels rem _ j i hij job
    have freyaDevelopmentFilteredTrace {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (P : Job d m → Bool) :
        Antitone (fun k => let s := fullTrace n labels x start rows answer k
          (uncovered labels s.remaining (fun i => (s.pending i).filter P) j).length) := by
      classical
      apply antitone_nat_of_succ_le
      intro k
      dsimp only
      by_cases he : (fullTrace n labels x start rows answer k).remaining = []
      · rw [(freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he).2,
          freyaDevelopmentUncoveredEmpty]
        exact Nat.zero_le _
      obtain ⟨i,job,c,hj,_,hrem,hpending⟩ :=
        freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k he
      rw [hrem,hpending,freyaDevelopmentFilterUpdate]
      let rem := ((fullTrace n labels x start rows answer k).remaining.find? fun a =>
        decide (labels[a]? = some job.component)).elim
          (fullTrace n labels x start rows answer k).remaining
          (fun a => (fullTrace n labels x start rows answer k).remaining.erase a)
      have hcomp := freyaDevelopmentFilteredCompletion labels
        (fullTrace n labels x start rows answer k).remaining _ j i job hj P
      dsimp only at hcomp
      rw [freyaDevelopmentFilterUpdate] at hcomp
      dsimp only [Option.filter_none] at hcomp
      have hassign := freyaDevelopmentAssignmentNonincrease labels rem
        (Function.update (fun l => ((fullTrace n labels x start rows answer k).pending l).filter P) i none)
        j i (Function.update_self _ _ _) (next := (dispatch
          (Sum.inl (fullTrace n labels x start rows answer k).point) c (n+k)
          (selectedLabel labels rem (rows (n+k)))).filter P)
      rw [Function.update_idem] at hassign
      exact hassign.trans hcomp
    have freyaDevelopmentHalt {d m : ℕ} (n : ℕ)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (k : ℕ)
        (he : (fullTrace n labels x start rows answer k).remaining = []) :
        fullTrace n labels x start rows answer (k+1) = fullTrace n labels x start rows answer k := by
      change fullUpdate _ _ = _
      delta fullUpdate
      rw [he]
      rfl
    have freyaDevelopmentCoverageTail {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (k0 : ℕ)
        (hcover : uncovered labels (fullTrace n labels x start rows answer k0).remaining
          (fullTrace n labels x start rows answer k0).pending j = []) :
        ∀ k, k0 ≤ k → ((fullTrace n labels x start rows answer k).clock : ℝ≥0∞) ≤
          ((fullTrace n labels x start rows answer k0).clock : ℝ≥0∞)+τ j := by
      classical
      let tr := fullTrace n labels x start rows answer
      let t0 := (tr k0).clock
      let P : Job d m → Bool := fun job => decide (job.started ≤ t0)
      have hzero : uncovered labels (tr k0).remaining (fun i => ((tr k0).pending i).filter P) j = [] := by
        by_cases he : (tr k0).remaining = []
        · rw [he,freyaDevelopmentUncoveredEmpty]
        have hlegal := (full_invariant n hn labels x start rows f τ answer hservice k0).2.2.2.2.1 he
        have hp : (fun i => ((tr k0).pending i).filter P) = (tr k0).pending := by
          funext i
          cases hj : (tr k0).pending i with
          | none => rfl
          | some job =>
            have hs := (hlegal.2 i job hj).1
            change job.started ≤ t0 at hs
            simp only [Option.filter_some,P,hs,decide_true,ite_true]
        rw [hp]
        exact hcover
      have hzero' (k : ℕ) (hk : k0 ≤ k) :
          uncovered labels (tr k).remaining (fun i => ((tr k).pending i).filter P) j = [] := by
        have h := freyaDevelopmentFilteredTrace n hn labels x start rows f τ answer hservice j P hk
        change (uncovered labels (tr k).remaining (fun i => ((tr k).pending i).filter P) j).length ≤
          (uncovered labels (tr k0).remaining (fun i => ((tr k0).pending i).filter P) j).length at h
        rw [hzero,List.length_nil] at h
        exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
      have hb (r : ℕ) : ((tr (k0+r)).clock : ℝ≥0∞) ≤ (t0 : ℝ≥0∞)+τ j := by
        induction r with
        | zero => exact le_add_of_nonneg_right zero_le
        | succ r ih =>
          rw [show k0+(r+1)=(k0+r)+1 by omega]
          by_cases he : (tr (k0+r)).remaining = []
          · have heq : tr (k0+r+1) = tr (k0+r) :=
              freyaDevelopmentHalt n labels x start rows answer (k0+r) he
            rw [heq]
            exact ih
          obtain ⟨i,job,hij,hjob⟩ := freyaDevelopmentCoveredPending labels (tr (k0+r)).remaining
            (fun i => ((tr (k0+r)).pending i).filter P) j he (hzero' (k0+r) (by omega))
          have horiginal : (tr (k0+r)).pending i = some job ∧ job.started ≤ t0 := by
            cases hp : (tr (k0+r)).pending i with
            | none => simp only [hp,Option.filter_none] at hjob; cases hjob
            | some old =>
              rw [hp] at hjob
              by_cases hP : P old = true
              · simp only [Option.filter_some,hP,ite_true,Option.some.injEq] at hjob
                subst old
                exact ⟨rfl,of_decide_eq_true hP⟩
              · simp only [Option.filter_some,hP,Bool.false_eq_true,ite_false] at hjob
                cases hjob
          have hcap := (freyaDevelopmentServiceClock n hn labels x start rows f τ answer hservice (k0+r) he).2
            i job horiginal.1
          exact hcap.trans (add_le_add (by exact_mod_cast horiginal.2) (hmono hij))
      intro k hk
      have h := hb (k-k0)
      rw [Nat.add_sub_of_le hk] at h
      exact h
    have freyaDevelopmentContextClock {d m : ℕ} (n : ℕ)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (k : ℕ) :
        (dispatchContext n labels x start rows answer (n+k)).2.2.2 =
          (fullTrace n labels x start rows answer (k+1)).clock := by
      delta dispatchContext
      rw [dite_eq_right (show ¬n+k<n by omega)]
      dsimp only
      rw [show n+k-n=k by omega]
      conv_rhs => change (fullUpdate (fullTrace n labels x start rows answer k)
        (answer k (fullQuery (fullTrace n labels x start rows answer k)))).clock
      cases hr : answer k (fullQuery (fullTrace n labels x start rows answer k)) with
      | none => rfl
      | some reply => obtain ⟨i,id,c,value⟩ := reply; rfl
    have freyaDevelopmentStartedUpdate {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (k : ℕ)
        (hne : (fullTrace n labels x start rows answer (k+1)).remaining ≠ []) :
        let s := fullTrace n labels x start rows answer k
        let t := fullTrace n labels x start rows answer (k+1)
        ∃ i, (dispatchContext n labels x start rows answer (n+k)).2.2.1 = some i ∧
          (fun l => ((t.pending l).map Job.started).getD 0) =
            Function.update (fun l => ((s.pending l).map Job.started).getD 0) i t.clock ∧
          (t.clock : ℝ≥0∞) ≤
            ((((s.pending i).map Job.started).getD 0 : ℝ≥0) : ℝ≥0∞)+τ i := by
      classical
      have hprev : (fullTrace n labels x start rows answer k).remaining ≠ [] := by
        intro he
        exact hne (freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he).2
      obtain ⟨i,job,c,hj,hctx,hrem,hpending⟩ :=
        freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k hprev
      have hb := (full_invariant n hn labels x start rows f τ answer hservice (k+1)).2.1
      rw [hrem] at hb hne
      obtain ⟨a,b,_,_,_,hs⟩ := freyaDevelopmentChosenLabel labels _ hb hne (rows (n+k))
      have hclock := freyaDevelopmentContextClock n labels x start rows answer k
      rw [hctx] at hclock
      dsimp only at hclock
      dsimp only
      refine ⟨i,?_,?_,?_⟩
      · rw [hctx]
        dsimp only
        have he : ((fullTrace n labels x start rows answer (k+1)).remaining).isEmpty = false := by
          rw [hrem]
          cases hh : ((fullTrace n labels x start rows answer k).remaining.find?
              fun a => decide (labels[a]? = some job.component)).elim
            (fullTrace n labels x start rows answer k).remaining
            (fun a => (fullTrace n labels x start rows answer k).remaining.erase a) with
          | nil => exact (hne hh).elim
          | cons a as => rfl
        rw [hrem] at he
        rw [he,ite_eq_right Bool.false_ne_true]
      · rw [hpending,hs,←hclock]
        funext l
        by_cases hl : l = i
        · subst l
          rw [Function.update_self,Function.update_self]
          rfl
        · rw [Function.update_of_ne hl,Function.update_of_ne hl]
      · have hcap := (freyaDevelopmentServiceClock n hn labels x start rows f τ answer hservice k hprev).2 i job hj
        simpa only [hj,Option.map_some,Option.getD_some] using hcap
    have freyaDevelopmentPositiveDispatchCount {d m : ℕ} (n : ℕ)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (j : Fin n)
        (D : Finset ℕ) (hD : D ⊆ Finset.range (n+n*labels.length))
        (hpositive : ∀ a ∈ D, let c := dispatchContext n labels x start rows answer a
          (∃ i, c.2.2.1 = some i ∧ i ≤ j) ∧ 0 < (uncovered labels c.1 c.2.1 j).length) :
        D.card ≤ couponWork n labels x start rows answer j := by
      classical
      let ctx := fun a => dispatchContext n labels x start rows answer a
      let V := fun a => (uncovered labels (ctx a).1 (ctx a).2.1 j).length
      have hbound (a : ℕ) : V a ≤ labels.length := by
        have h := (freyaDevelopmentUncoveredSublist labels (ctx a).1 (ctx a).2.1 j).length_le.trans
          (freyaDevelopmentContextSublist n labels x start rows answer a).length_le
        simpa only [List.length_range] using h
      have hf : ∀ a ∈ D, V a-1 ∈ Finset.range labels.length := by
        intro a ha
        have hp := (hpositive a ha).2
        have hb := hbound a
        change 0 < V a at hp
        exact Finset.mem_range.mpr (by omega)
      have hcard := Finset.card_eq_sum_card_fiberwise hf
      calc
        D.card = ∑ u ∈ Finset.range labels.length, (D.filter fun a => V a-1=u).card := hcard
        _ ≤ ∑ u ∈ Finset.range labels.length,
            (couponWaiting n labels x start rows answer j (u+1)+1) := by
          apply Finset.sum_le_sum
          intro u hu
          apply Nat.le_succ_of_le
          apply Finset.card_le_card
          intro a ha
          obtain ⟨haD,hvalue⟩ := Finset.mem_filter.mp ha
          have hp := hpositive a haD
          change a ∈ ((Finset.range (n+n*labels.length)).filter fun a =>
            (∃ i, (ctx a).2.2.1=some i ∧ i≤j) ∧ V a=u+1)
          apply Finset.mem_filter.mpr
          refine ⟨hD haD,hp.1,?_⟩
          have hpos : 0 < V a := hp.2
          omega
        _ = couponWork n labels x start rows answer j := by
          delta couponWork
          rw [Fin.sum_univ_eq_sum_range
            (fun u : ℕ => couponWaiting n labels x start rows answer j (u+1)+1) labels.length]
    have freyaDevelopmentAssignmentCoverage {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) (k : ℕ) :
        let s := fullTrace n labels x start rows answer (k+1)
        let c := dispatchContext n labels x start rows answer (n+k)
        (uncovered labels s.remaining s.pending j).length ≤ (uncovered labels c.1 c.2.1 j).length := by
      classical
      dsimp only
      by_cases he : (fullTrace n labels x start rows answer k).remaining = []
      · rw [(freyaDevelopmentEmptyTraceContext n labels x start rows f τ answer hservice k he).2,
          freyaDevelopmentUncoveredEmpty]
        exact Nat.zero_le _
      obtain ⟨i,job,c,_,hctx,hrem,hpending⟩ :=
        freyaDevelopmentActiveDispatch n hn labels x start rows f τ answer hservice k he
      rw [hrem,hpending,hctx]
      dsimp only
      let s := fullTrace n labels x start rows answer k
      let rem := (s.remaining.find? fun a => decide (labels[a]? = some job.component)).elim
        s.remaining (fun a => s.remaining.erase a)
      have h := freyaDevelopmentAssignmentNonincrease labels rem
        (Function.update s.pending i none) j i (Function.update_self _ _ _)
        (dispatch (Sum.inl s.point) c (n+k) (selectedLabel labels rem (rows (n+k))))
      rw [Function.update_idem] at h
      exact h
    have freyaDevelopmentWeightedUpdate {n : ℕ} (j i : Fin n)
        (v : Fin n → ℝ≥0) (c : ℝ≥0) (r : Fin n → ℝ)
        (hpos : ∀ l ∈ Finset.Iic j, 0 < r l)
        (hcap : i ≤ j → (c : ℝ) ≤ (v i : ℝ)+r i) :
        (∑ l ∈ Finset.Iic j, ((Function.update v i c l : ℝ≥0) : ℝ)/r l) ≤
          (∑ l ∈ Finset.Iic j, (v l : ℝ)/r l)+(if i ≤ j then 1 else 0 : ℝ) := by
      classical
      have hpoint (l : Fin n) : ((Function.update v i c l : ℝ≥0) : ℝ)/r l =
          (v l : ℝ)/r l + (if l=i then ((c : ℝ)-(v i : ℝ))/r i else 0) := by
        by_cases hl : l = i
        · subst l
          rw [Function.update_self,ite_eq_left rfl]
          ring
        · rw [Function.update_of_ne hl,ite_eq_right hl,add_zero]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib,Finset.sum_ite_eq']
      by_cases hij : i ≤ j
      · rw [ite_eq_left (Finset.mem_Iic.mpr hij),ite_eq_left hij]
        apply add_le_add le_rfl
        apply (div_le_one (hpos i (Finset.mem_Iic.mpr hij))).mpr
        linarith only [hcap hij]
      · rw [ite_eq_right (by simpa only [Finset.mem_Iic] using hij),ite_eq_right hij]
    have freyaDevelopmentRealDeadline (c started : ℝ≥0) (τ : ℝ≥0∞) (hfinite : τ ≠ ⊤)
        (h : (c : ℝ≥0∞) ≤ (started : ℝ≥0∞)+τ) :
        (c : ℝ) ≤ (started : ℝ)+τ.toReal := by
      have hf : (started : ℝ≥0∞)+τ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp,hfinite⟩
      have hh := ENNReal.toReal_mono hf h
      rw [ENNReal.toReal_add (by simp) hfinite] at hh
      exact hh
    have freyaDevelopmentZeroWorkerClock {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (i : Fin n) (hi : τ i = 0) (k : ℕ) :
        (fullTrace n labels x start rows answer k).clock = start := by
      induction k with
      | zero => rfl
      | succ k ih =>
        by_cases he : (fullTrace n labels x start rows answer k).remaining = []
        · rw [freyaDevelopmentHalt n labels x start rows answer k he]
          exact ih
        obtain ⟨job,hjob⟩ := freyaDevelopmentAllPending n hn labels x start rows f τ answer hservice k he i
        have hlegal := (full_invariant n hn labels x start rows f τ answer hservice k).2.2.2.2.1 he
        have hs := (hlegal.2 i job hjob).1
        have hcap := freyaDevelopmentServiceClock n hn labels x start rows f τ answer hservice k he
        have hc := hcap.2 i job hjob
        rw [hi,add_zero] at hc
        have hnn : (fullTrace n labels x start rows answer (k+1)).clock ≤ job.started := by exact_mod_cast hc
        exact (le_antisymm (hnn.trans hs) hcap.1).trans ih
    have freyaDevelopmentPrecoverageCapacity {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n)
        (hfinite : ∀ i ∈ Finset.Iic j, τ i ≠ ⊤)
        (hpos : ∀ i ∈ Finset.Iic j, 0 < (τ i).toReal)
        (k : ℕ) (hk : k < n*labels.length)
        (hpositive : ∀ a ≤ k, 0 < (uncovered labels
          (fullTrace n labels x start rows answer a).remaining
          (fullTrace n labels x start rows answer a).pending j).length) :
        (((fullTrace n labels x start rows answer (k+1)).clock : ℝ)-(start : ℝ)) *
          (∑ i ∈ Finset.Iic j, (τ i).toReal⁻¹) ≤
            (couponWork n labels x start rows answer j : ℝ)+(j.val+1 : ℕ) := by
      classical
      let tr := fullTrace n labels x start rows answer
      let V := fun a i => (((tr a).pending i).map Job.started).getD 0
      let H := ∑ i ∈ Finset.Iic j, (τ i).toReal⁻¹
      let F := fun a => ∑ i ∈ Finset.Iic j, (V a i : ℝ)/(τ i).toReal
      let flag := fun a => ∃ i, (dispatchContext n labels x start rows answer (n+a)).2.2.1=some i ∧ i≤j
      let charge := fun a => if flag a then (1 : ℝ) else 0
      have hactive (a : ℕ) (ha : a ≤ k) : (tr a).remaining ≠ [] := by
        intro he
        have h := hpositive a ha
        change 0 < (uncovered labels (tr a).remaining (tr a).pending j).length at h
        rw [he,freyaDevelopmentUncoveredEmpty,List.length_nil] at h
        omega
      have hV0 (i : Fin n) : V 0 i = start := by
        have hne := hactive 0 (Nat.zero_le k)
        obtain ⟨a,b,_,_,_,hs⟩ := freyaDevelopmentChosenLabel labels (List.range labels.length)
          (fun a ha => List.mem_range.mp ha) hne (rows i.val)
        change ((dispatch (Sum.inl x) start (0+i.val)
          (selectedLabel labels (List.range labels.length) (rows (0+i.val)))).map Job.started).getD 0 = start
        rw [Nat.zero_add,hs]
        rfl
      have hF0 : F 0 = (start : ℝ)*H := by
        dsimp only [F,H]
        simp_rw [hV0,div_eq_mul_inv]
        rw [Finset.mul_sum]
      have hstep (a : ℕ) (ha : a < k) : F (a+1) ≤ F a+charge a := by
        obtain ⟨i,hflag,hupdate,hcap⟩ := freyaDevelopmentStartedUpdate n hn labels x start rows f τ answer
          hservice a (hactive (a+1) (by omega))
        change V (a+1) = Function.update (V a) i (tr (a+1)).clock at hupdate
        have hch : charge a = if i≤j then 1 else 0 := by
          have hf : flag a ↔ i ≤ j := by
            dsimp only [flag]
            rw [hflag]
            constructor
            · rintro ⟨l,hl,hij⟩
              exact (Option.some.inj hl) ▸ hij
            · intro hij
              exact ⟨i,rfl,hij⟩
          simp only [charge,hf]
        dsimp only [F]
        rw [hupdate,hch]
        exact freyaDevelopmentWeightedUpdate j i (V a) (tr (a+1)).clock (fun i => (τ i).toReal) hpos
          (fun hi => freyaDevelopmentRealDeadline _ _ _ (hfinite i (Finset.mem_Iic.mpr hi)) hcap)
      have hFbound (a : ℕ) (ha : a ≤ k) :
          F a ≤ (start : ℝ)*H+∑ b ∈ Finset.range a, charge b := by
        induction a with
        | zero => simpa only [Finset.range_zero,Finset.sum_empty,add_zero] using hF0.le
        | succ a ih =>
          have hh := hstep a (by omega)
          have hb := ih (by omega)
          rw [Finset.sum_range_succ]
          linarith only [hh,hb]
      let D := (Finset.range k).filter flag
      let E := D.image (fun a => n+a)
      have hE : E ⊆ Finset.range (n+n*labels.length) := by
        intro a ha
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
        have hbk := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        exact Finset.mem_range.mpr (by omega)
      have hpE : ∀ a ∈ E, let c := dispatchContext n labels x start rows answer a
          (∃ i, c.2.2.1=some i ∧ i≤j) ∧ 0 < (uncovered labels c.1 c.2.1 j).length := by
        intro a ha
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hbk,hflag⟩ := Finset.mem_filter.mp hb
        have hbk' := Finset.mem_range.mp hbk
        refine ⟨hflag,?_⟩
        have hpos' := hpositive (b+1) (by omega)
        exact lt_of_lt_of_le hpos' (freyaDevelopmentAssignmentCoverage n hn labels x start rows f τ answer hservice j b)
      have hcount := freyaDevelopmentPositiveDispatchCount n labels x start rows answer j E hE hpE
      have hcard : E.card = D.card := Finset.card_image_iff.mpr (by
        intro a ha b hb hab
        exact Nat.add_left_cancel hab)
      rw [hcard] at hcount
      have hsum : (∑ a ∈ Finset.range k, charge a) = (D.card : ℝ) := by
        exact Finset.sum_boole flag (Finset.range k)
      have hF : F k ≤ (start : ℝ)*H+(couponWork n labels x start rows answer j : ℝ) := by
        have h := hFbound k le_rfl
        rw [hsum] at h
        exact h.trans (add_le_add le_rfl (by exact_mod_cast hcount))
      have hC : ((tr (k+1)).clock : ℝ)*H ≤ F k+(j.val+1 : ℕ) := by
        calc
          ((tr (k+1)).clock : ℝ)*H = ∑ i ∈ Finset.Iic j,
              ((tr (k+1)).clock : ℝ)/(τ i).toReal := by
            dsimp only [H]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ ≤ ∑ i ∈ Finset.Iic j, ((V k i : ℝ)/(τ i).toReal+1) := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨job,hjob⟩ := freyaDevelopmentAllPending n hn labels x start rows f τ answer hservice k (hactive k le_rfl) i
            have hc := (freyaDevelopmentServiceClock n hn labels x start rows f τ answer hservice k (hactive k le_rfl)).2 i job hjob
            have hr := freyaDevelopmentRealDeadline _ _ _ (hfinite i hi) hc
            have he : V k i = job.started := by simp only [V,tr,hjob,Option.map_some,Option.getD_some]
            rw [←he] at hr
            apply (div_le_iff₀ (hpos i hi)).mpr
            have halg : ((V k i : ℝ)/(τ i).toReal+1)*(τ i).toReal = (V k i : ℝ)+(τ i).toReal := by
              field_simp [(hpos i hi).ne']
            rw [halg]
            exact hr
          _ = F k+(j.val+1 : ℕ) := by
            rw [Finset.sum_add_distrib]
            congr 1
            simp
      change (((tr (k+1)).clock : ℝ)-(start : ℝ))*H ≤ _
      nlinarith only [hC,hF]
    have freyaDevelopmentCapacityActual {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
        (answer : ℕ → Option (Request d m n) → Reply d n)
        (hservice : servicePath f τ answer) (j : Fin n) :
        (((fullTrace n labels x start rows answer (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞) ≤
          ((couponWork n labels x start rows answer j+(j.val+1) : ℕ) : ℝ≥0∞)/
            (∑ i ∈ Finset.Iic j, (τ i)⁻¹)+τ j := by
      classical
      by_cases hjtop : τ j = ⊤
      · rw [hjtop,add_top]
        exact le_top
      by_cases hz : ∃ i ∈ Finset.Iic j, τ i = 0
      · obtain ⟨i,_,hi⟩ := hz
        rw [freyaDevelopmentZeroWorkerClock n hn labels x start rows f τ answer hservice i hi,
          tsub_self,ENNReal.coe_zero]
        exact zero_le
      have hfinite (i : Fin n) (hi : i ∈ Finset.Iic j) : τ i ≠ ⊤ :=
        ne_top_of_le_ne_top hjtop (hmono (Finset.mem_Iic.mp hi))
      have hnonzero (i : Fin n) (hi : i ∈ Finset.Iic j) : τ i ≠ 0 := fun h => hz ⟨i,hi,h⟩
      have hpos (i : Fin n) (hi : i ∈ Finset.Iic j) : 0 < (τ i).toReal :=
        ENNReal.toReal_pos (hnonzero i hi) (hfinite i hi)
      let tr := fullTrace n labels x start rows answer
      let N := n*labels.length
      let H := ∑ i ∈ Finset.Iic j, (τ i).toReal⁻¹
      let R : ℝ≥0∞ := ∑ i ∈ Finset.Iic j, (τ i)⁻¹
      let Q := couponWork n labels x start rows answer j
      let A : ℝ≥0∞ := ((Q+(j.val+1) : ℕ) : ℝ≥0∞)/R
      have hH : 0 < H := by
        apply Finset.sum_pos'
        · intro i hi
          exact (inv_pos.mpr (hpos i hi)).le
        · exact ⟨j,Finset.mem_Iic.mpr le_rfl,inv_pos.mpr (hpos j (Finset.mem_Iic.mpr le_rfl))⟩
      have hRfinite : R ≠ ⊤ := by
        apply ENNReal.sum_ne_top.mpr
        intro i hi
        exact ENNReal.inv_ne_top.mpr (hnonzero i hi)
      have hRreal : R.toReal = H := by
        dsimp only [R,H]
        rw [ENNReal.toReal_sum (fun i hi => ENNReal.inv_ne_top.mpr (hnonzero i hi))]
        apply Finset.sum_congr rfl
        intro i _
        exact ENNReal.toReal_inv (τ i)
      have hRzero : R ≠ 0 := by
        intro he
        rw [he,ENNReal.toReal_zero] at hRreal
        exact hH.ne' hRreal.symm
      have hAfin : A ≠ ⊤ := ENNReal.div_ne_top (by simp) hRzero
      have hAreal : A.toReal = ((Q : ℝ)+(j.val+1 : ℕ))/H := by
        dsimp only [A]
        rw [ENNReal.toReal_div,ENNReal.toReal_natCast,hRreal,Nat.cast_add]
      have hend : (tr N).remaining = [] := (full_event_bound n hn labels x start rows f τ answer hservice).1
      have hex : ∃ k, uncovered labels (tr k).remaining (tr k).pending j = [] :=
        ⟨N,by rw [hend,freyaDevelopmentUncoveredEmpty]⟩
      let k0 := Nat.find hex
      have hcover : uncovered labels (tr k0).remaining (tr k0).pending j = [] := Nat.find_spec hex
      have hk0 : k0 ≤ N := Nat.find_min' hex (by rw [hend,freyaDevelopmentUncoveredEmpty])
      have hC0 : ((tr k0).clock : ℝ≥0∞) ≤ (start : ℝ≥0∞)+A := by
        by_cases he : k0 = 0
        · rw [he]
          exact le_add_of_nonneg_right zero_le
        have hk : k0-1 < N := by omega
        have hpositive : ∀ a ≤ k0-1,
            0 < (uncovered labels (tr a).remaining (tr a).pending j).length := by
          intro a ha
          apply List.length_pos_iff.mpr
          exact Nat.find_min hex (by omega)
        have hcap := freyaDevelopmentPrecoverageCapacity n hn labels x start rows f τ answer hservice j
          hfinite hpos (k0-1) hk hpositive
        rw [show k0-1+1=k0 by omega] at hcap
        change (((tr k0).clock : ℝ)-(start : ℝ))*H ≤ (Q : ℝ)+(j.val+1 : ℕ) at hcap
        have hreal : ((tr k0).clock : ℝ)-(start : ℝ) ≤ ((Q : ℝ)+(j.val+1 : ℕ))/H :=
          (le_div_iff₀ hH).mpr hcap
        apply (ENNReal.toReal_le_toReal (by simp) (ENNReal.add_ne_top.mpr ⟨by simp,hAfin⟩)).mp
        rw [ENNReal.toReal_add (by simp) hAfin,ENNReal.coe_toReal,ENNReal.coe_toReal,hAreal]
        linarith only [hreal]
      have htail := freyaDevelopmentCoverageTail n hn labels x start rows f τ hmono answer hservice j k0 hcover N hk0
      have hall : ((tr N).clock : ℝ≥0∞) ≤ (start : ℝ≥0∞)+A+τ j :=
        htail.trans (add_le_add hC0 le_rfl)
      have hstart := (full_invariant n hn labels x start rows f τ answer hservice N).2.2.1
      have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨by simp,hAfin⟩,hjtop⟩) hall
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨by simp,hAfin⟩) hjtop,
        ENNReal.toReal_add (by simp) hAfin,ENNReal.coe_toReal,ENNReal.coe_toReal] at hreal
      change (((tr N).clock-start : ℝ≥0) : ℝ≥0∞) ≤ A+τ j
      apply (ENNReal.toReal_le_toReal (by simp) (ENNReal.add_ne_top.mpr ⟨hAfin,hjtop⟩)).mp
      rw [ENNReal.coe_toReal,NNReal.coe_sub hstart,ENNReal.toReal_add hAfin hjtop]
      linarith only [hreal]
    exact freyaDevelopmentCapacityActual n hn labels x start rows f τ hmono answer hservice j


theorem full_multiset_correct {d m : ℕ} (n : ℕ) (hn : 0 < n)
    (labels : List (Fin m)) (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) :
    fullResult (fullTrace n labels x start rows answer (n * labels.length)) =
      (labels.length : ℝ)⁻¹ • (labels.map fun i => gradient (f i) x).sum := by
  have hmeta : ∀ a, (fullTrace n labels x start rows answer a).original = labels := by
    intro a
    induction a with
    | zero => rfl
    | succ a ih =>
      change (fullUpdate (fullTrace n labels x start rows answer a)
        (answer a (fullQuery (fullTrace n labels x start rows answer a)))).original = labels
      delta fullUpdate
      by_cases he : (fullTrace n labels x start rows answer a).remaining.isEmpty = true
      · rw [ite_eq_left he]
        exact ih
      · rw [ite_eq_right he]
        cases hr : answer a (fullQuery (fullTrace n labels x start rows answer a)) with
        | none => exact ih
        | some reply =>
          obtain ⟨i, id, c, value⟩ := reply
          dsimp only
          cases hp : (fullTrace n labels x start rows answer a).pending i with
          | none => exact ih
          | some job =>
            dsimp only
            split <;> exact ih
  let s := fullTrace n labels x start rows answer (n*labels.length)
  have he : s.remaining = [] := (full_event_bound n hn labels x start rows f τ answer hservice).1
  have hinv := full_invariant n hn labels x start rows f τ answer hservice (n*labels.length)
  have hsum : s.sum + (s.remaining.map (contribution f labels x)).sum =
      (labels.map fun i => gradient (f i) x).sum := hinv.2.2.2.1
  have horig : s.original = labels := hmeta _
  simp only [he, List.map_nil, List.sum_nil, add_zero] at hsum
  change (s.original.length : ℝ)⁻¹ • s.sum = _
  rw [horig, hsum]


theorem full_multiset_time {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} (n : ℕ) (hn : 0 < n) (labels : List (Fin m)) (hq : 0 < labels.length)
    (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
    (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
    (hrows : Measurable rows)
    (hanswer : ∀ a, Measurable (fun z : Option (Request d m n) × Ω => answer a z.1 z.2))
    (hservice : ∀ᵐ ω ∂(P : Measure Ω), servicePath f τ (fun a r => answer a r ω))
    (hfresh : FullFresh P n labels x start rows answer) :
    Measurable (fun ω => (fullTrace n labels x start (rows ω)
      (fun a r => answer a r ω) (n * labels.length)).clock) ∧
      (∫⁻ ω, (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
        (n * labels.length)).clock - start : ℝ≥0) : ℝ≥0∞) ∂(P : Measure Ω)) ≤
        multisetTimeBound τ labels.length := by
  open scoped BigOperators ENNReal NNReal in
    have freyaDevelopmentFullClockMeas {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        {d m : ℕ} (n : ℕ) (hn : 0 < n) (labels : List (Fin m)) (hq : 0 < labels.length)
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) :
        Measurable (fun ω => (fullTrace n labels x start (rows ω)
          (fun a r => answer a r ω) (n*labels.length)).clock) := by
      classical
      obtain ⟨H,_,hfresh,hcontext,_⟩ := hfresh
      let N := n*labels.length
      have hN : 0 < N := Nat.mul_pos hn hq
      let a := n+N-1
      have ha : ¬ a < n := by omega
      have haN : a-n+1 = N := by omega
      have hclock (ω : Ω) :
          (dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a).2.2.2 =
            (fullTrace n labels x start (rows ω) (fun k r => answer k r ω) N).clock := by
        delta dispatchContext
        rw [dite_eq_right ha]
        conv_rhs => rw [← haN]
        conv_rhs =>
          change (fullUpdate (fullTrace n labels x start (rows ω) (fun k r => answer k r ω) (a-n))
            (answer (a-n) (fullQuery (fullTrace n labels x start (rows ω) (fun k r => answer k r ω) (a-n))) ω)).clock
        dsimp only
        cases hr : answer (a-n)
            (fullQuery (fullTrace n labels x start (rows ω) (fun k r => answer k r ω) (a-n))) ω with
        | none => rfl
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          rfl
      have hm := ((hcontext a).snd.snd.snd).mono (hfresh a).1 le_rfl
      have heq := funext hclock
      rw [heq] at hm
      exact hm
    have freyaDevelopmentEraseMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (b : β) (l : List α) :
        ((l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)).map φ = (l.map φ).erase b := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        by_cases ha : φ a = b
        · simp [ha]
        · cases hf : l.find? (fun a => decide (φ a = b)) with
          | none =>
            have hnot : b ∉ l.map φ := by
              intro hb
              obtain ⟨v,hv,heq⟩ := List.mem_map.mp hb
              have h := List.find?_eq_none.mp hf v hv
              simp only [heq,decide_true,not_true_eq_false] at h
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_none,
              List.map_cons]
            rw [List.erase_of_not_mem (by simpa only [List.mem_cons,not_or] using And.intro (Ne.symm ha) hnot)]
          | some v =>
            have hv : φ v = b := by
              have h := List.find?_some hf
              simpa only [decide_eq_true_eq] using h
            have hva : v ≠ a := by intro h; subst v; exact ha hv
            have hi := ih
            rw [hf] at hi
            simp only [Option.elim_some] at hi
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_some,
              List.map_cons]
            rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using Ne.symm hva), List.map_cons,hi,List.erase_cons_tail (by simpa only [beq_iff_eq] using ha)]
    have freyaDevelopmentEraseFoldCount {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) l).count b = l.count b - jobs.count b := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        by_cases hab : a = b
        · subst a
          simp only [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne (Ne.symm hab)]
          simp only [List.count_cons,hab,beq_iff_eq,ite_false]
          omega
    have freyaDevelopmentEraseFoldMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (jobs : List β) (l : List α) :
        (jobs.foldl (fun rem b => (rem.find? fun a => decide (φ a = b)).elim rem
          (fun a => rem.erase a)) l).map φ =
          jobs.foldl (fun rem b => rem.erase b) (l.map φ) := by
      induction jobs generalizing l with
      | nil => rfl
      | cons b jobs ih =>
        simp only [List.foldl_cons]
        rw [ih,freyaDevelopmentEraseMap]
    have freyaDevelopmentFilterMapFold {ι α β : Type}
        (f : List α → β → List α) (p : ι → Option β) (workers : List ι) (l : List α) :
        workers.foldl (fun rem i => (p i).elim rem (f rem)) l =
          (workers.filterMap p).foldl f l := by
      induction workers generalizing l with
      | nil => rfl
      | cons i workers ih =>
        simp (config := { iota := false }) only [List.foldl_cons,List.filterMap_cons]
        cases hp : p i with
        | none => exact ih l
        | some b => exact ih (f l b)
    have freyaDevelopmentUncoveredCounts {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (b : Option (Fin m)) :
        ((uncovered labels rem pending j).map (fun a => labels[a]?)).count b =
          (rem.map (fun a => labels[a]?)).count b -
            ((((List.finRange n).filter fun i => decide (i ≤ j)).filterMap
              (fun i => (pending i).map fun job => some job.component)).count b) := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let φ := fun a : ℕ => labels[a]?
      let p := fun i => (pending i).map fun job => some job.component
      let eraseOne := fun (l : List ℕ) (b : Option (Fin m)) =>
        (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)
      have hf : (fun (l : List ℕ) i => (pending i).elim l fun job =>
          (l.find? fun a => decide (labels[a]? = some job.component)).elim l
            (fun a => l.erase a)) = (fun l i => (p i).elim l (eraseOne l)) := by
        funext l i
        dsimp only [p]
        cases hp : pending i with
        | none => rfl
        | some job => rfl
      have heq : uncovered labels rem pending j = (workers.filterMap p).foldl eraseOne rem := by
        delta uncovered
        rw [hf]
        exact freyaDevelopmentFilterMapFold eraseOne p workers rem
      rw [heq]
      change ((workers.filterMap p).foldl
        (fun l b => (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)) rem
          |>.map φ |>.count b) = _
      rw [freyaDevelopmentEraseFoldMap]
      exact freyaDevelopmentEraseFoldCount (workers.filterMap p) (rem.map φ) b
    have freyaDevelopmentCountSum {α : Type} [Fintype α] [DecidableEq α] [BEq α] [LawfulBEq α] (l : List α) :
        (∑ b : α, l.count b) = l.length := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.count_cons,beq_iff_eq,List.length_cons]
        simp only [Finset.sum_ite,Finset.sum_add_distrib,Finset.sum_const_zero]
        simp only [Finset.sum_const,smul_eq_mul,mul_one,ih]
        have hset : (Finset.univ.filter fun x : α => a = x) = {a} := by
          ext x
          simp [eq_comm]
        rw [hset]
        simp only [Finset.card_singleton,Nat.add_zero]
    have freyaDevelopmentContextNodup {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
        (dispatchContext n labels x start rows answer a).1.Nodup := by
      classical
      have hup (s : FullState d m n) (reply : Reply d n) (hs : s.remaining.Nodup) :
          (fullUpdate s reply).remaining.Nodup := by
        delta fullUpdate
        by_cases he : s.remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact hs
        · rw [ite_eq_right he]
          cases reply with
          | none => exact hs
          | some reply =>
            obtain ⟨i,id,c,value⟩ := reply
            dsimp only
            cases hp : s.pending i with
            | none => exact hs
            | some job =>
              dsimp only
              split
              · dsimp only
                cases hf : s.remaining.find? (fun b => decide (s.original[b]? = some job.component)) with
                | none => exact hs
                | some b => exact hs.erase b
              · exact hs
      have htrace : ∀ k, (fullTrace n labels x start rows answer k).remaining.Nodup := by
        intro k
        induction k with
        | zero => exact List.nodup_range
        | succ k ih => exact hup _ _ ih
      delta dispatchContext
      by_cases ha : a < n
      · rw [dite_eq_left ha]
        exact List.nodup_range
      · rw [dite_eq_right ha]
        dsimp only
        have h := hup (fullTrace n labels x start rows answer (a-n))
          (answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n)))) (htrace (a-n))
        cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
        | none => simpa only [hr] using h
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          simpa only [hr] using h
    have freyaDevelopmentUncoveredLengthPerm {d m n : ℕ} (labels : List (Fin m))
        (rem rem' : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (hrem : rem.Perm rem') :
        (uncovered labels rem pending j).length = (uncovered labels rem' pending j).length := by
      classical
      have hp : ((uncovered labels rem pending j).map (fun a => labels[a]?)).Perm
          ((uncovered labels rem' pending j).map (fun a => labels[a]?)) := by
        apply List.perm_iff_count.mpr
        intro b
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,
          (hrem.map (fun a => labels[a]?)).count_eq b]
      simpa only [List.length_map] using hp.length_eq
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaDevelopmentPendingCodesMeas {d m n : ℕ} :
        Measurable (fun pending : Fin n → Option (Job d m) =>
          fun i => (pending i).elim 0 (fun job => job.component.val+1)) := by
      have hj : Measurable (fun job : Job d m => job.component) := measurable_fst.comp (comap_measurable _)
      have hv : Measurable (fun job : Job d m => job.component.val+1) :=
        (measurable_of_countable (fun i : Fin m => i.val+1)).comp hj
      exact Measurable.of_eval fun i => (freyaDevelopmentOptionElimMeas 0 _ hv).comp (measurable_pi_apply i)
    have freyaDevelopmentPendingCountCodes {d m n : ℕ}
        (pending : Fin n → Option (Job d m)) (workers : List (Fin n)) (b : Option (Fin m)) :
        (workers.filterMap (fun i => (pending i).map fun job => some job.component)).count b =
          b.elim 0 (fun v => (workers.filter fun i =>
            decide ((pending i).elim 0 (fun job => job.component.val+1) = v.val+1)).length) := by
      cases b with
      | none =>
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          simp (config := { iota := false }) only [List.filterMap_cons]
          cases hp : pending i with
          | none => exact ih
          | some job =>
            dsimp only [Option.map] at ih ⊢
            simpa (config := { iota := false }) only [Option.map_some,List.count_cons,Option.some_beq_none,
              Bool.false_eq_true,ite_false,Nat.add_zero,Option.elim_none] using ih
      | some v =>
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          simp (config := { iota := false }) only [List.filterMap_cons,Option.elim_some,List.filter_cons]
          cases hp : pending i with
          | none => simpa (config := { iota := false }) using ih
          | some job =>
            dsimp only [Option.map] at ih ⊢
            by_cases hv : job.component = v
            · have hv' : job.component.val = v.val := congrArg Fin.val hv
              simpa (config := { iota := false }) only [Option.map_some,Option.elim_some,List.count_cons,beq_iff_eq,
                Option.some.injEq,hv,hv',ite_true,Nat.add_right_cancel_iff,
                decide_true,List.length_cons] using ih
            · have hv' : job.component.val ≠ v.val := fun h => hv (Fin.ext h)
              simpa (config := { iota := false }) only [Option.map_some,Option.elim_some,List.count_cons,beq_iff_eq,
                Option.some.injEq,hv,hv',ite_false,Nat.add_right_cancel_iff,
                decide_false,Bool.false_eq_true,Nat.add_zero] using ih
    have freyaDevelopmentWaitingMeas {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n) (u : ℕ) :
        Measurable (fun ω => couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u) := by
      classical
      obtain ⟨H,_,hfresh,hcontext,_⟩ := hfresh
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let F := fun z : Finset ℕ × (Fin n → ℕ) => ∑ b : Option (Fin m),
        ((z.1.toList.map (fun a => labels[a]?)).count b -
          b.elim 0 (fun v => (workers.filter fun i => decide (z.2 i = v.val+1)).length))
      let ctx := fun a ω => dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a
      have hformula (a : ℕ) (ω : Ω) :
          (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length =
            F ((ctx a ω).1.toFinset,fun i => ((ctx a ω).2.1 i).elim 0 (fun job => job.component.val+1)) := by
        have hn := freyaDevelopmentContextNodup n labels x start (rows ω) (fun k r => answer k r ω) a
        have hp : (ctx a ω).1.Perm (ctx a ω).1.toFinset.toList := by
          apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
          intro b
          simp only [Finset.mem_toList,List.mem_toFinset,ctx]
        rw [freyaDevelopmentUncoveredLengthPerm _ _ _ _ _ hp]
        have hsum := freyaDevelopmentCountSum
          ((uncovered labels (ctx a ω).1.toFinset.toList (ctx a ω).2.1 j).map (fun a => labels[a]?))
        rw [List.length_map] at hsum
        rw [← hsum]
        dsimp only [F]
        apply Finset.sum_congr rfl
        intro b _
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentPendingCountCodes]
      have huMeas (a : ℕ) : Measurable[H a] (fun ω =>
          (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length) := by
        have hm := (measurable_of_countable F).comp ((hcontext a).fst.prodMk
          (freyaDevelopmentPendingCodesMeas.comp (hcontext a).snd.fst))
        have heq := funext (hformula a)
        rw [heq]
        exact hm
      have hevent (a : ℕ) : MeasurableSet[H a] {ω |
          (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ∧
            (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length = u} := by
        have hflag := (freyaDevelopmentOptionElimMeas false (fun i : Fin n => decide (i ≤ j))
          (measurable_of_countable _)).comp (hcontext a).snd.snd.fst
        have hset : {ω | ∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j} =
            {ω | ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true} := by
          ext ω
          change (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ↔
            ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true
          cases hc : (ctx a ω).2.2.1 <;> simp
        have hflagset : MeasurableSet[H a] {ω |
            ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true} :=
          hflag (measurableSet_singleton true)
        rw [← hset] at hflagset
        exact hflagset.inter ((huMeas a) (measurableSet_singleton u))
      have hm (a : ℕ) : Measurable (fun ω => if
          (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ∧
            (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length = u then (1 : ℕ) else 0) :=
        measurable_const.ite ((hfresh a).1 _ (hevent a)) measurable_const
      have hsum := Finset.measurable_sum (Finset.range (n+n*labels.length)) (fun a _ => hm a)
      delta couponWaiting
      simpa only [Finset.card_filter,ctx] using hsum
    have freyaDevelopmentCouponWorkBound {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n)
        (hwait : ∀ u : ℕ, 0 < u →
          (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
            ∂(P : Measure Ω)) ≤ 1 + (min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞)) :
        (∫⁻ ω, (couponWork n labels x start (rows ω) (fun a r => answer a r ω) j : ℝ≥0∞)
          ∂(P : Measure Ω)) ≤ 2*(labels.length : ℝ≥0∞) +
            ∑ u : Fin labels.length, (min (j.val+1) labels.length : ℕ)/((u.val+1 : ℕ) : ℝ≥0∞) := by
      have hm (u : ℕ) : Measurable (fun ω =>
          (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)) :=
        (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
          (freyaDevelopmentWaitingMeas P n labels x start rows answer hfresh j u)
      delta couponWork
      simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_one]
      rw [lintegral_finsetSum _ (fun u _ => (hm (u.val+1)).add measurable_const)]
      calc
        _ ≤ ∑ u : Fin labels.length,
            (1 + (min (j.val+1) labels.length : ℕ)/((u.val+1 : ℕ) : ℝ≥0∞) + 1) := by
          apply Finset.sum_le_sum
          intro u _
          rw [lintegral_add_right _ measurable_const]
          simpa only [lintegral_const,measure_univ,mul_one] using
            add_le_add (hwait (u.val+1) (Nat.zero_lt_succ _)) (le_refl 1)
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
            nsmul_eq_mul,mul_one]
          simp only [Nat.cast_add,Nat.cast_one]
          rw [two_mul]
          ac_rfl
    have freyaDevelopmentHarmonicProduct (q s : ℕ) (hs : 0 < s) (hsq : s ≤ q) :
        (s : ℝ)*(harmonic q : ℝ) ≤ q + s*Real.log s := by
      have hq : 0 < q := hs.trans_le hsq
      have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      have hH := LongTails.Proofs.FreyaEquilibrium.harmonic_bound hq
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqR hsR)
      rw [Real.log_div (ne_of_gt hqR) (ne_of_gt hsR)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hsR.le
      have hdiv : (s : ℝ)*((q : ℝ)/s) = q := by field_simp
      have hh := mul_le_mul_of_nonneg_left hH hsR.le
      nlinarith
    have freyaDevelopmentHarmonicENNReal (q k : ℕ) :
        (∑ u : Fin q, (k : ℝ≥0∞)/((u.val+1 : ℕ) : ℝ≥0∞)) =
          (k : ℝ≥0∞)*ENNReal.ofReal (harmonic q : ℝ) := by
      have hreal : (harmonic q : ℝ) = ∑ u : Fin q, ((u.val+1 : ℕ) : ℝ)⁻¹ := by
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i+1 : ℕ) : ℝ)⁻¹) q]
        delta harmonic
        push_cast
        rfl
      rw [hreal,ENNReal.ofReal_sum_of_nonneg (fun u _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_natCast]
      rfl
    have freyaDevelopmentExpectedCapacity {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (T : Ω → ℝ≥0∞) (Q : Ω → ℕ) (hQ : Measurable Q) (k : ℕ) (H τ : ℝ≥0∞)
        (hbound : ∀ᵐ ω ∂(P : Measure Ω), T ω ≤ ((Q ω : ℝ≥0∞)+k)/H+τ) :
        (∫⁻ ω, T ω ∂(P : Measure Ω)) ≤ ((∫⁻ ω, (Q ω : ℝ≥0∞) ∂(P : Measure Ω))+k)/H+τ := by
      have hm : Measurable (fun ω => (Q ω : ℝ≥0∞)) :=
        (measurable_of_countable (fun z : ℕ => (z : ℝ≥0∞))).comp hQ
      refine (lintegral_mono_ae hbound).trans_eq ?_
      have heq : (fun ω => ((Q ω : ℝ≥0∞)+k)/H+τ) =
          (fun ω => H⁻¹*((Q ω : ℝ≥0∞)+k)+τ) := by
        funext ω
        rw [div_eq_mul_inv,mul_comm]
      have hadd : Measurable (fun ω => (Q ω : ℝ≥0∞)+(k : ℝ≥0∞)) := hm.add measurable_const
      rw [heq,lintegral_add_right _ measurable_const,
        lintegral_const_mul (μ := (P : Measure Ω)) (f := fun ω => (Q ω : ℝ≥0∞)+k) H⁻¹ hadd,
        lintegral_add_right _ measurable_const]
      simp only [lintegral_const,measure_univ,mul_one,div_eq_mul_inv]
      rw [mul_comm]
    have freyaDevelopmentCapacityAlgebra (A r k H τ t : ℝ≥0∞)
        (hA : A ≤ 3*r) (hτ : τ ≤ t) (ht : t = (r+k)/H) :
        (A+k)/H+τ ≤ 4*t := by
      have hk : k ≤ 3*k := by
        calc
          k = 1*k := (one_mul _).symm
          _ ≤ 3*k := by gcongr; norm_num
      calc
        (A+k)/H+τ ≤ (3*r+3*k)/H+t := by gcongr
        _ = 4*t := by
          rw [← mul_add,div_eq_mul_inv,mul_assoc,← div_eq_mul_inv,← ht]
          have hfour : (4 : ℝ≥0∞) = 3+1 := by norm_num
          rw [hfour,add_mul,one_mul]
    have freyaDevelopmentHarmonicWorkAlgebra (q n k : ℕ) (hq : 0 < q) (hn : 0 < n)
        (hk : k ≤ min q n) :
        2*(q : ℝ≥0∞)+(k : ℝ≥0∞)*ENNReal.ofReal (harmonic q : ℝ) ≤
          3*((q : ℝ≥0∞)+ENNReal.ofReal ((min q n : ℕ)*Real.log (min q n))) := by
      let s := min q n
      have hs : 0 < s := Nat.lt_min.mpr ⟨hq,hn⟩
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hnonneg : 0 ≤ (s : ℝ)*Real.log s :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hsR)
      have hH : (s : ℝ≥0∞)*ENNReal.ofReal (harmonic q : ℝ) ≤
          (q : ℝ≥0∞)+ENNReal.ofReal ((s : ℝ)*Real.log s) := by
        have h := ENNReal.ofReal_le_ofReal (freyaDevelopmentHarmonicProduct q s hs (Nat.min_le_left _ _))
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg s),ENNReal.ofReal_natCast,
          ENNReal.ofReal_add (Nat.cast_nonneg q) hnonneg,ENNReal.ofReal_natCast] at h
        exact h
      calc
        _ ≤ 2*(q : ℝ≥0∞)+(s : ℝ≥0∞)*ENNReal.ofReal (harmonic q : ℝ) := by
          gcongr
        _ ≤ 2*(q : ℝ≥0∞)+((q : ℝ≥0∞)+ENNReal.ofReal ((s : ℝ)*Real.log s)) :=
          add_le_add le_rfl hH
        _ ≤ _ := by
          simp only [← Nat.cast_min]
          change _ ≤ 3*((q : ℝ≥0∞)+ENNReal.ofReal ((s : ℝ)*Real.log s))
          rw [mul_add]
          have hthree : (3 : ℝ≥0∞) = 2+1 := by norm_num
          rw [hthree,add_mul,one_mul]
          rw [← add_assoc]
          gcongr
          calc
            ENNReal.ofReal ((s : ℝ)*Real.log s) = 1*ENNReal.ofReal ((s : ℝ)*Real.log s) := (one_mul _).symm
            _ ≤ (2+1)*ENNReal.ofReal ((s : ℝ)*Real.log s) := by gcongr; norm_num
    have freyaDevelopmentTimeFromCouponAndCapacity {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (hq : 0 < labels.length) (x : Space d) (start : ℝ≥0)
        (rows : Ω → ℕ → ChoiceRow) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer)
        (hwait : ∀ j : Fin n, ∀ u : ℕ, 0 < u →
          (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
            ∂(P : Measure Ω)) ≤ 1 + (min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞))
        (hcapacity : ∀ j : Fin n, ∀ᵐ ω ∂(P : Measure Ω),
          (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
            (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞) ≤
            ((couponWork n labels x start (rows ω) (fun a r => answer a r ω) j + (j.val+1) : ℕ) : ℝ≥0∞)/
              (∑ i ∈ Finset.Iic j, (τ i)⁻¹)+τ j) :
        Measurable (fun ω => (fullTrace n labels x start (rows ω)
          (fun a r => answer a r ω) (n*labels.length)).clock) ∧
          (∫⁻ ω, (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
            (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞) ∂(P : Measure Ω)) ≤
              multisetTimeBound τ labels.length := by
      classical
      refine ⟨freyaDevelopmentFullClockMeas P n hn labels hq x start rows answer hfresh,?_⟩
      let r : ℝ≥0∞ := labels.length + ENNReal.ofReal
        ((min labels.length n : ℕ)*Real.log (min labels.length n))
      have hb : multisetTimeBound τ labels.length = 12*equilibriumTime τ r := rfl
      rw [hb]
      by_cases htop : ∀ i, τ i = ⊤
      · rw [LongTails.Proofs.FreyaEquilibrium.equilibrium_top τ htop]
        simp
      by_cases hz : ∃ i, τ i = 0
      · obtain ⟨i,hi⟩ := hz
        have hden : (∑ a ∈ Finset.Iic i, (τ a)⁻¹) = ⊤ := by
          apply top_unique
          have h := Finset.single_le_sum (fun a _ => bot_le : ∀ a ∈ Finset.Iic i, (0 : ℝ≥0∞) ≤ (τ a)⁻¹)
            (Finset.mem_Iic.mpr (le_refl i))
          simpa only [hi,ENNReal.inv_zero] using h
        have hcap := hcapacity i
        simp only [hden,ENNReal.div_top,hi,zero_add] at hcap
        exact (lintegral_mono_ae hcap).trans (by simp)
      have hpos : ∀ i, 0 < τ i := fun i => pos_iff_ne_zero.mpr (fun hi => hz ⟨i,hi⟩)
      have hfinite : ∃ i, τ i ≠ ⊤ := not_forall.mp htop
      have hr : 0 < r := (show (0 : ℝ≥0∞) < labels.length by exact_mod_cast hq).trans_le le_self_add
      have hrfin : r ≠ ⊤ := by
        exact ENNReal.add_ne_top.mpr ⟨by simp,ENNReal.ofReal_ne_top⟩
      obtain ⟨j,hτ,ht⟩ := LongTails.Proofs.FreyaEquilibrium.prefix_threshold hn τ hmono hpos hfinite r hr hrfin
      let Q := fun ω => couponWork n labels x start (rows ω) (fun a r => answer a r ω) j
      have hQ : Measurable Q := by
        change Measurable (fun ω => couponWork n labels x start (rows ω) (fun a r => answer a r ω) j)
        delta couponWork
        apply Finset.measurable_sum
        intro u _
        exact (freyaDevelopmentWaitingMeas P n labels x start rows answer hfresh j (u.val+1)).add measurable_const
      have hwork := freyaDevelopmentCouponWorkBound P n labels x start rows answer hfresh j (hwait j)
      rw [freyaDevelopmentHarmonicENNReal] at hwork
      have hk : min (j.val+1) labels.length ≤ min labels.length n :=
        Nat.le_min.mpr ⟨Nat.min_le_right _ _,(Nat.min_le_left _ _).trans (Nat.succ_le_of_lt j.isLt)⟩
      have hA : (∫⁻ ω, (Q ω : ℝ≥0∞) ∂(P : Measure Ω)) ≤ 3*r :=
        hwork.trans (freyaDevelopmentHarmonicWorkAlgebra labels.length n (min (j.val+1) labels.length) hq hn hk)
      have hc := freyaDevelopmentExpectedCapacity P
        (fun ω => (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
          (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞)) Q hQ (j.val+1)
        (∑ i ∈ Finset.Iic j, (τ i)⁻¹) (τ j) (by simpa only [Nat.cast_add] using hcapacity j)
      refine hc.trans ((freyaDevelopmentCapacityAlgebra _ r _ _ _ _ hA hτ ht).trans ?_)
      gcongr
      norm_num
    exact freyaDevelopmentTimeFromCouponAndCapacity P n hn labels hq x start rows τ hmono answer hfresh
      (fun j u hu => coupon_progress P n hn labels hq x start rows f τ answer hrows hanswer hservice hfresh j u hu)
      (fun j => hservice.mono (fun ω hs => capacity_bound n hn labels x start (rows ω) f τ hmono
        (fun a r => answer a r ω) hs j))


theorem full_gradient_correct {d m : ℕ} (hm : 0 < m) (n : ℕ) (hn : 0 < n)
    (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (τ : Fin n → ℝ≥0∞) (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) :
    fullResult (fullTrace n (List.ofFn id) x start rows answer (n * m)) =
      gradient (objective f) x := by
  open scoped BigOperators in
    have _ := hm
    have h := full_multiset_correct n hn (List.ofFn id) x start rows f τ answer hservice
    have hg : HasGradientAt (objective f) ((m : ℝ)⁻¹ • (∑ i, gradient (f i) x)) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      have hd := (HasFDerivAt.sum (u := Finset.univ)
        (fun i _ => (hf i x).hasGradientAt.hasFDerivAt)).const_mul (m : ℝ)⁻¹
      simp only [Finset.sum_apply] at hd
      simp only [map_sum, map_smul]
      exact hd
    rw [hg.gradient]
    simpa only [List.length_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def, id_eq] using h


theorem full_gradient_time {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} (hm : 0 < m) (n : ℕ) (hn : 0 < n)
    (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
    (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
    (hrows : Measurable rows)
    (hanswer : ∀ a, Measurable (fun z : Option (Request d m n) × Ω => answer a z.1 z.2))
    (hservice : ∀ᵐ ω ∂(P : Measure Ω), servicePath f τ (fun a r => answer a r ω))
    (hfresh : FullFresh P n (List.ofFn id) x start rows answer) :
    Measurable (fun ω => (fullTrace n (List.ofFn id) x start (rows ω)
      (fun a r => answer a r ω) (n * m)).clock) ∧
      (∫⁻ ω, (((fullTrace n (List.ofFn id) x start (rows ω)
        (fun a r => answer a r ω) (n * m)).clock - start : ℝ≥0) : ℝ≥0∞) ∂(P : Measure Ω)) ≤
        multisetTimeBound τ m := by
  simpa only [List.length_ofFn] using
    full_multiset_time P n hn (List.ofFn id) (by simpa only [List.length_ofFn] using hm)
      x start rows f τ hmono answer hrows hanswer hservice hfresh


theorem full_gradient_time_sharp {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {d m : ℕ} (hm : 0 < m) (n : ℕ) (hn : 0 < n) (hlarge : largeSample m n)
    (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
    (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
    (hrows : Measurable rows)
    (hanswer : ∀ a, Measurable (fun z : Option (Request d m n) × Ω => answer a z.1 z.2))
    (hservice : ∀ᵐ ω ∂(P : Measure Ω), servicePath f τ (fun a r => answer a r ω))
    (hfresh : FullFresh P n (List.ofFn id) x start rows answer) :
    (∫⁻ ω, (((fullTrace n (List.ofFn id) x start (rows ω)
      (fun a r => answer a r ω) (n * m)).clock - start : ℝ≥0) : ℝ≥0∞) ∂(P : Measure Ω)) ≤
      5 * equilibriumTime τ m := by
  set_option maxHeartbeats 1600000 in
  open scoped BigOperators ENNReal NNReal in
    have freyaDevelopmentEraseMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (b : β) (l : List α) :
        ((l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)).map φ = (l.map φ).erase b := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        by_cases ha : φ a = b
        · simp [ha]
        · cases hf : l.find? (fun a => decide (φ a = b)) with
          | none =>
            have hnot : b ∉ l.map φ := by
              intro hb
              obtain ⟨v,hv,heq⟩ := List.mem_map.mp hb
              have h := List.find?_eq_none.mp hf v hv
              simp only [heq,decide_true,not_true_eq_false] at h
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_none,
              List.map_cons]
            rw [List.erase_of_not_mem (by simpa only [List.mem_cons,not_or] using And.intro (Ne.symm ha) hnot)]
          | some v =>
            have hv : φ v = b := by
              have h := List.find?_some hf
              simpa only [decide_eq_true_eq] using h
            have hva : v ≠ a := by intro h; subst v; exact ha hv
            have hi := ih
            rw [hf] at hi
            simp only [Option.elim_some] at hi
            simp only [List.find?_cons,ha,decide_false,hf,Option.elim_some,
              List.map_cons]
            rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using Ne.symm hva), List.map_cons,hi,List.erase_cons_tail (by simpa only [beq_iff_eq] using ha)]
    have freyaDevelopmentEraseFoldCount {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
        (jobs l : List α) (b : α) :
        (jobs.foldl (fun rem a => rem.erase a) l).count b = l.count b - jobs.count b := by
      induction jobs generalizing l with
      | nil => simp
      | cons a jobs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        by_cases hab : a = b
        · subst a
          simp only [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne (Ne.symm hab)]
          simp only [List.count_cons,hab,beq_iff_eq,ite_false]
          omega
    have freyaDevelopmentEraseFoldMap {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
        (φ : α → β) (jobs : List β) (l : List α) :
        (jobs.foldl (fun rem b => (rem.find? fun a => decide (φ a = b)).elim rem
          (fun a => rem.erase a)) l).map φ =
          jobs.foldl (fun rem b => rem.erase b) (l.map φ) := by
      induction jobs generalizing l with
      | nil => rfl
      | cons b jobs ih =>
        simp only [List.foldl_cons]
        rw [ih,freyaDevelopmentEraseMap]
    have freyaDevelopmentFilterMapFold {ι α β : Type}
        (f : List α → β → List α) (p : ι → Option β) (workers : List ι) (l : List α) :
        workers.foldl (fun rem i => (p i).elim rem (f rem)) l =
          (workers.filterMap p).foldl f l := by
      induction workers generalizing l with
      | nil => rfl
      | cons i workers ih =>
        simp (config := { iota := false }) only [List.foldl_cons,List.filterMap_cons]
        cases hp : p i with
        | none => exact ih l
        | some b => exact ih (f l b)
    have freyaDevelopmentUncoveredCounts {d m n : ℕ} (labels : List (Fin m))
        (rem : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (b : Option (Fin m)) :
        ((uncovered labels rem pending j).map (fun a => labels[a]?)).count b =
          (rem.map (fun a => labels[a]?)).count b -
            ((((List.finRange n).filter fun i => decide (i ≤ j)).filterMap
              (fun i => (pending i).map fun job => some job.component)).count b) := by
      classical
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let φ := fun a : ℕ => labels[a]?
      let p := fun i => (pending i).map fun job => some job.component
      let eraseOne := fun (l : List ℕ) (b : Option (Fin m)) =>
        (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)
      have hf : (fun (l : List ℕ) i => (pending i).elim l fun job =>
          (l.find? fun a => decide (labels[a]? = some job.component)).elim l
            (fun a => l.erase a)) = (fun l i => (p i).elim l (eraseOne l)) := by
        funext l i
        dsimp only [p]
        cases hp : pending i with
        | none => rfl
        | some job => rfl
      have heq : uncovered labels rem pending j = (workers.filterMap p).foldl eraseOne rem := by
        delta uncovered
        rw [hf]
        exact freyaDevelopmentFilterMapFold eraseOne p workers rem
      rw [heq]
      change ((workers.filterMap p).foldl
        (fun l b => (l.find? fun a => decide (φ a = b)).elim l (fun a => l.erase a)) rem
          |>.map φ |>.count b) = _
      rw [freyaDevelopmentEraseFoldMap]
      exact freyaDevelopmentEraseFoldCount (workers.filterMap p) (rem.map φ) b
    have freyaDevelopmentCountSum {α : Type} [Fintype α] [DecidableEq α] [BEq α] [LawfulBEq α] (l : List α) :
        (∑ b : α, l.count b) = l.length := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.count_cons,beq_iff_eq,List.length_cons]
        simp only [Finset.sum_ite,Finset.sum_add_distrib,Finset.sum_const_zero]
        simp only [Finset.sum_const,smul_eq_mul,mul_one,ih]
        have hset : (Finset.univ.filter fun x : α => a = x) = {a} := by
          ext x
          simp [eq_comm]
        rw [hset]
        simp only [Finset.card_singleton,Nat.add_zero]
    have freyaDevelopmentContextNodup {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Reply d n) (a : ℕ) :
        (dispatchContext n labels x start rows answer a).1.Nodup := by
      classical
      have hup (s : FullState d m n) (reply : Reply d n) (hs : s.remaining.Nodup) :
          (fullUpdate s reply).remaining.Nodup := by
        delta fullUpdate
        by_cases he : s.remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact hs
        · rw [ite_eq_right he]
          cases reply with
          | none => exact hs
          | some reply =>
            obtain ⟨i,id,c,value⟩ := reply
            dsimp only
            cases hp : s.pending i with
            | none => exact hs
            | some job =>
              dsimp only
              split
              · dsimp only
                cases hf : s.remaining.find? (fun b => decide (s.original[b]? = some job.component)) with
                | none => exact hs
                | some b => exact hs.erase b
              · exact hs
      have htrace : ∀ k, (fullTrace n labels x start rows answer k).remaining.Nodup := by
        intro k
        induction k with
        | zero => exact List.nodup_range
        | succ k ih => exact hup _ _ ih
      delta dispatchContext
      by_cases ha : a < n
      · rw [dite_eq_left ha]
        exact List.nodup_range
      · rw [dite_eq_right ha]
        dsimp only
        have h := hup (fullTrace n labels x start rows answer (a-n))
          (answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n)))) (htrace (a-n))
        cases hr : answer (a-n) (fullQuery (fullTrace n labels x start rows answer (a-n))) with
        | none => simpa only [hr] using h
        | some reply =>
          obtain ⟨i,id,c,value⟩ := reply
          simpa only [hr] using h
    have freyaDevelopmentUncoveredLengthPerm {d m n : ℕ} (labels : List (Fin m))
        (rem rem' : List ℕ) (pending : Fin n → Option (Job d m)) (j : Fin n)
        (hrem : rem.Perm rem') :
        (uncovered labels rem pending j).length = (uncovered labels rem' pending j).length := by
      classical
      have hp : ((uncovered labels rem pending j).map (fun a => labels[a]?)).Perm
          ((uncovered labels rem' pending j).map (fun a => labels[a]?)) := by
        apply List.perm_iff_count.mpr
        intro b
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentUncoveredCounts,
          (hrem.map (fun a => labels[a]?)).count_eq b]
      simpa only [List.length_map] using hp.length_eq
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaDevelopmentPendingCodesMeas {d m n : ℕ} :
        Measurable (fun pending : Fin n → Option (Job d m) =>
          fun i => (pending i).elim 0 (fun job => job.component.val+1)) := by
      have hj : Measurable (fun job : Job d m => job.component) := measurable_fst.comp (comap_measurable _)
      have hv : Measurable (fun job : Job d m => job.component.val+1) :=
        (measurable_of_countable (fun i : Fin m => i.val+1)).comp hj
      exact Measurable.of_eval fun i => (freyaDevelopmentOptionElimMeas 0 _ hv).comp (measurable_pi_apply i)
    have freyaDevelopmentPendingCountCodes {d m n : ℕ}
        (pending : Fin n → Option (Job d m)) (workers : List (Fin n)) (b : Option (Fin m)) :
        (workers.filterMap (fun i => (pending i).map fun job => some job.component)).count b =
          b.elim 0 (fun v => (workers.filter fun i =>
            decide ((pending i).elim 0 (fun job => job.component.val+1) = v.val+1)).length) := by
      cases b with
      | none =>
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          simp (config := { iota := false }) only [List.filterMap_cons]
          cases hp : pending i with
          | none => exact ih
          | some job =>
            dsimp only [Option.map] at ih ⊢
            simpa (config := { iota := false }) only [Option.map_some,List.count_cons,Option.some_beq_none,
              Bool.false_eq_true,ite_false,Nat.add_zero,Option.elim_none] using ih
      | some v =>
        induction workers with
        | nil => rfl
        | cons i workers ih =>
          simp (config := { iota := false }) only [List.filterMap_cons,Option.elim_some,List.filter_cons]
          cases hp : pending i with
          | none => simpa (config := { iota := false }) using ih
          | some job =>
            dsimp only [Option.map] at ih ⊢
            by_cases hv : job.component = v
            · have hv' : job.component.val = v.val := congrArg Fin.val hv
              simpa (config := { iota := false }) only [Option.map_some,Option.elim_some,List.count_cons,beq_iff_eq,
                Option.some.injEq,hv,hv',ite_true,Nat.add_right_cancel_iff,
                decide_true,List.length_cons] using ih
            · have hv' : job.component.val ≠ v.val := fun h => hv (Fin.ext h)
              simpa (config := { iota := false }) only [Option.map_some,Option.elim_some,List.count_cons,beq_iff_eq,
                Option.some.injEq,hv,hv',ite_false,Nat.add_right_cancel_iff,
                decide_false,Bool.false_eq_true,Nat.add_zero] using ih
    have freyaDevelopmentWaitingMeas {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n) (u : ℕ) :
        Measurable (fun ω => couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u) := by
      classical
      obtain ⟨H,_,hfresh,hcontext,_⟩ := hfresh
      let workers := (List.finRange n).filter fun i => decide (i ≤ j)
      let F := fun z : Finset ℕ × (Fin n → ℕ) => ∑ b : Option (Fin m),
        ((z.1.toList.map (fun a => labels[a]?)).count b -
          b.elim 0 (fun v => (workers.filter fun i => decide (z.2 i = v.val+1)).length))
      let ctx := fun a ω => dispatchContext n labels x start (rows ω) (fun k r => answer k r ω) a
      have hformula (a : ℕ) (ω : Ω) :
          (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length =
            F ((ctx a ω).1.toFinset,fun i => ((ctx a ω).2.1 i).elim 0 (fun job => job.component.val+1)) := by
        have hn := freyaDevelopmentContextNodup n labels x start (rows ω) (fun k r => answer k r ω) a
        have hp : (ctx a ω).1.Perm (ctx a ω).1.toFinset.toList := by
          apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
          intro b
          simp only [Finset.mem_toList,List.mem_toFinset,ctx]
        rw [freyaDevelopmentUncoveredLengthPerm _ _ _ _ _ hp]
        have hsum := freyaDevelopmentCountSum
          ((uncovered labels (ctx a ω).1.toFinset.toList (ctx a ω).2.1 j).map (fun a => labels[a]?))
        rw [List.length_map] at hsum
        rw [← hsum]
        dsimp only [F]
        apply Finset.sum_congr rfl
        intro b _
        rw [freyaDevelopmentUncoveredCounts,freyaDevelopmentPendingCountCodes]
      have huMeas (a : ℕ) : Measurable[H a] (fun ω =>
          (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length) := by
        have hm := (measurable_of_countable F).comp ((hcontext a).fst.prodMk
          (freyaDevelopmentPendingCodesMeas.comp (hcontext a).snd.fst))
        have heq := funext (hformula a)
        rw [heq]
        exact hm
      have hevent (a : ℕ) : MeasurableSet[H a] {ω |
          (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ∧
            (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length = u} := by
        have hflag := (freyaDevelopmentOptionElimMeas false (fun i : Fin n => decide (i ≤ j))
          (measurable_of_countable _)).comp (hcontext a).snd.snd.fst
        have hset : {ω | ∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j} =
            {ω | ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true} := by
          ext ω
          change (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ↔
            ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true
          cases hc : (ctx a ω).2.2.1 <;> simp
        have hflagset : MeasurableSet[H a] {ω |
            ((ctx a ω).2.2.1).elim false (fun i => decide (i ≤ j)) = true} :=
          hflag (measurableSet_singleton true)
        rw [← hset] at hflagset
        exact hflagset.inter ((huMeas a) (measurableSet_singleton u))
      have hm (a : ℕ) : Measurable (fun ω => if
          (∃ i, (ctx a ω).2.2.1 = some i ∧ i ≤ j) ∧
            (uncovered labels (ctx a ω).1 (ctx a ω).2.1 j).length = u then (1 : ℕ) else 0) :=
        measurable_const.ite ((hfresh a).1 _ (hevent a)) measurable_const
      have hsum := Finset.measurable_sum (Finset.range (n+n*labels.length)) (fun a _ => hm a)
      delta couponWaiting
      simpa only [Finset.card_filter,ctx] using hsum
    have freyaDevelopmentCouponWorkBound {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        {d m : ℕ} (n : ℕ) (labels : List (Fin m))
        (x : Space d) (start : ℝ≥0) (rows : Ω → ℕ → ChoiceRow)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer) (j : Fin n)
        (hwait : ∀ u : ℕ, 0 < u →
          (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
            ∂(P : Measure Ω)) ≤ 1 + (min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞)) :
        (∫⁻ ω, (couponWork n labels x start (rows ω) (fun a r => answer a r ω) j : ℝ≥0∞)
          ∂(P : Measure Ω)) ≤ 2*(labels.length : ℝ≥0∞) +
            ∑ u : Fin labels.length, (min (j.val+1) labels.length : ℕ)/((u.val+1 : ℕ) : ℝ≥0∞) := by
      have hm (u : ℕ) : Measurable (fun ω =>
          (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)) :=
        (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
          (freyaDevelopmentWaitingMeas P n labels x start rows answer hfresh j u)
      delta couponWork
      simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_one]
      rw [lintegral_finsetSum _ (fun u _ => (hm (u.val+1)).add measurable_const)]
      calc
        _ ≤ ∑ u : Fin labels.length,
            (1 + (min (j.val+1) labels.length : ℕ)/((u.val+1 : ℕ) : ℝ≥0∞) + 1) := by
          apply Finset.sum_le_sum
          intro u _
          rw [lintegral_add_right _ measurable_const]
          simpa only [lintegral_const,measure_univ,mul_one] using
            add_le_add (hwait (u.val+1) (Nat.zero_lt_succ _)) (le_refl 1)
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
            nsmul_eq_mul,mul_one]
          simp only [Nat.cast_add,Nat.cast_one]
          rw [two_mul]
          ac_rfl
    have freyaDevelopmentHarmonicENNReal (q k : ℕ) :
        (∑ u : Fin q, (k : ℝ≥0∞)/((u.val+1 : ℕ) : ℝ≥0∞)) =
          (k : ℝ≥0∞)*ENNReal.ofReal (harmonic q : ℝ) := by
      have hreal : (harmonic q : ℝ) = ∑ u : Fin q, ((u.val+1 : ℕ) : ℝ)⁻¹ := by
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i+1 : ℕ) : ℝ)⁻¹) q]
        delta harmonic
        push_cast
        rfl
      rw [hreal,ENNReal.ofReal_sum_of_nonneg (fun u _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_natCast]
      rfl
    have freyaDevelopmentExpectedCapacity {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
        (T : Ω → ℝ≥0∞) (Q : Ω → ℕ) (hQ : Measurable Q) (k : ℕ) (H τ : ℝ≥0∞)
        (hbound : ∀ᵐ ω ∂(P : Measure Ω), T ω ≤ ((Q ω : ℝ≥0∞)+k)/H+τ) :
        (∫⁻ ω, T ω ∂(P : Measure Ω)) ≤ ((∫⁻ ω, (Q ω : ℝ≥0∞) ∂(P : Measure Ω))+k)/H+τ := by
      have hm : Measurable (fun ω => (Q ω : ℝ≥0∞)) :=
        (measurable_of_countable (fun z : ℕ => (z : ℝ≥0∞))).comp hQ
      refine (lintegral_mono_ae hbound).trans_eq ?_
      have heq : (fun ω => ((Q ω : ℝ≥0∞)+k)/H+τ) =
          (fun ω => H⁻¹*((Q ω : ℝ≥0∞)+k)+τ) := by
        funext ω
        rw [div_eq_mul_inv,mul_comm]
      have hadd : Measurable (fun ω => (Q ω : ℝ≥0∞)+(k : ℝ≥0∞)) := hm.add measurable_const
      rw [heq,lintegral_add_right _ measurable_const,
        lintegral_const_mul (μ := (P : Measure Ω)) (f := fun ω => (Q ω : ℝ≥0∞)+k) H⁻¹ hadd,
        lintegral_add_right _ measurable_const]
      simp only [lintegral_const,measure_univ,mul_one,div_eq_mul_inv]
      rw [mul_comm]
    have freyaDevelopmentCapacityAlgebra (A r k H τ t : ℝ≥0∞)
        (hA : A ≤ 3*r) (hτ : τ ≤ t) (ht : t = (r+k)/H) :
        (A+k)/H+τ ≤ 4*t := by
      have hk : k ≤ 3*k := by
        calc
          k = 1*k := (one_mul _).symm
          _ ≤ 3*k := by gcongr; norm_num
      calc
        (A+k)/H+τ ≤ (3*r+3*k)/H+t := by gcongr
        _ = 4*t := by
          rw [← mul_add,div_eq_mul_inv,mul_assoc,← div_eq_mul_inv,← ht]
          have hfour : (4 : ℝ≥0∞) = 3+1 := by norm_num
          rw [hfour,add_mul,one_mul]
    have freyaDevelopmentCapacityAlgebraFour (A r k H τ t : ℝ≥0∞)
        (hA : A ≤ 4*r) (hτ : τ ≤ t) (ht : t = (r+k)/H) :
        (A+k)/H+τ ≤ 5*t := by
      have hk : k ≤ 4*k := by
        calc
          k = 1*k := (one_mul _).symm
          _ ≤ 4*k := by gcongr; norm_num
      calc
        (A+k)/H+τ ≤ (4*r+4*k)/H+t := by gcongr
        _ = 5*t := by
          rw [← mul_add,div_eq_mul_inv,mul_assoc,← div_eq_mul_inv,← ht]
          have hfive : (5 : ℝ≥0∞) = 4+1 := by norm_num
          rw [hfive,add_mul,one_mul]
    have freyaDevelopmentSharpTimeFromCouponAndCapacity {Ω : Type} [MeasurableSpace Ω]
        (P : ProbabilityMeasure Ω) {d m : ℕ} (n : ℕ) (hn : 0 < n)
        (labels : List (Fin m)) (hq : 0 < labels.length) (hlarge : largeSample labels.length n) (x : Space d) (start : ℝ≥0)
        (rows : Ω → ℕ → ChoiceRow) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
        (answer : ℕ → Option (Request d m n) → Ω → Reply d n)
        (hfresh : FullFresh P n labels x start rows answer)
        (hwait : ∀ j : Fin n, ∀ u : ℕ, 0 < u →
          (∫⁻ ω, (couponWaiting n labels x start (rows ω) (fun a r => answer a r ω) j u : ℝ≥0∞)
            ∂(P : Measure Ω)) ≤ 1 + (min (j.val+1) labels.length : ℕ)/(u : ℝ≥0∞))
        (hcapacity : ∀ j : Fin n, ∀ᵐ ω ∂(P : Measure Ω),
          (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
            (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞) ≤
            ((couponWork n labels x start (rows ω) (fun a r => answer a r ω) j + (j.val+1) : ℕ) : ℝ≥0∞)/
              (∑ i ∈ Finset.Iic j, (τ i)⁻¹)+τ j) :
        (∫⁻ ω, (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
          (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞) ∂(P : Measure Ω)) ≤
            5*equilibriumTime τ labels.length := by
      classical
      let r : ℝ≥0∞ := labels.length
      by_cases htop : ∀ i, τ i = ⊤
      · rw [LongTails.Proofs.FreyaEquilibrium.equilibrium_top τ htop]
        simp
      by_cases hz : ∃ i, τ i = 0
      · obtain ⟨i,hi⟩ := hz
        have hden : (∑ a ∈ Finset.Iic i, (τ a)⁻¹) = ⊤ := by
          apply top_unique
          have h := Finset.single_le_sum (fun a _ => bot_le : ∀ a ∈ Finset.Iic i, (0 : ℝ≥0∞) ≤ (τ a)⁻¹)
            (Finset.mem_Iic.mpr (le_refl i))
          simpa only [hi,ENNReal.inv_zero] using h
        have hcap := hcapacity i
        simp only [hden,ENNReal.div_top,hi,zero_add] at hcap
        exact (lintegral_mono_ae hcap).trans (by simp)
      have hpos : ∀ i, 0 < τ i := fun i => pos_iff_ne_zero.mpr (fun hi => hz ⟨i,hi⟩)
      have hfinite : ∃ i, τ i ≠ ⊤ := not_forall.mp htop
      have hr : 0 < r := by
        change (0 : ℝ≥0∞) < (labels.length : ℝ≥0∞)
        exact_mod_cast hq
      have hrfin : r ≠ ⊤ := by
        change (labels.length : ℝ≥0∞) ≠ ⊤
        exact ENNReal.natCast_ne_top labels.length
      obtain ⟨j,hτ,ht⟩ := LongTails.Proofs.FreyaEquilibrium.prefix_threshold hn τ hmono hpos hfinite r hr hrfin
      let Q := fun ω => couponWork n labels x start (rows ω) (fun a r => answer a r ω) j
      have hQ : Measurable Q := by
        change Measurable (fun ω => couponWork n labels x start (rows ω) (fun a r => answer a r ω) j)
        delta couponWork
        apply Finset.measurable_sum
        intro u _
        exact (freyaDevelopmentWaitingMeas P n labels x start rows answer hfresh j (u.val+1)).add measurable_const
      have hwork := freyaDevelopmentCouponWorkBound P n labels x start rows answer hfresh j (hwait j)
      rw [freyaDevelopmentHarmonicENNReal] at hwork
      have hk : min (j.val+1) labels.length ≤ n :=
        (Nat.min_le_left _ _).trans (Nat.succ_le_of_lt j.isLt)
      have hHreal := (LongTails.Proofs.FreyaEquilibrium.large_sample_harmonic hq hn hlarge).2
      have hH : (n : ℝ≥0∞)*ENNReal.ofReal (harmonic labels.length : ℝ) ≤ 2*r := by
        have h := ENNReal.ofReal_le_ofReal hHreal
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] at h
        exact h
      have hA : (∫⁻ ω, (Q ω : ℝ≥0∞) ∂(P : Measure Ω)) ≤ 4*r := by
        refine hwork.trans ?_
        calc
          _ ≤ 2*r+(n : ℝ≥0∞)*ENNReal.ofReal (harmonic labels.length : ℝ) := by gcongr
          _ ≤ 2*r+2*r := add_le_add le_rfl hH
          _ = 4*r := by rw [←add_mul]; norm_num
      have hc := freyaDevelopmentExpectedCapacity P
        (fun ω => (((fullTrace n labels x start (rows ω) (fun a r => answer a r ω)
          (n*labels.length)).clock-start : ℝ≥0) : ℝ≥0∞)) Q hQ (j.val+1)
        (∑ i ∈ Finset.Iic j, (τ i)⁻¹) (τ j) (by simpa only [Nat.cast_add] using hcapacity j)
      exact hc.trans (freyaDevelopmentCapacityAlgebraFour _ r _ _ _ _ hA hτ ht)
    have hq : 0 < (List.ofFn (id : Fin m → Fin m)).length := by
      simpa only [List.length_ofFn] using hm
    have hlarge' : largeSample (List.ofFn (id : Fin m → Fin m)).length n := by
      simpa only [List.length_ofFn] using hlarge
    simpa only [List.length_ofFn] using
      freyaDevelopmentSharpTimeFromCouponAndCapacity P n hn (List.ofFn id) hq hlarge'
        x start rows τ hmono answer hfresh
        (fun j u hu => coupon_progress P n hn (List.ofFn id) hq x start rows f τ answer
          hrows hanswer hservice hfresh j u hu)
        (fun j => hservice.mono (fun ω hs => capacity_bound n hn (List.ofFn id) x start
          (rows ω) f τ hmono (fun a r => answer a r ω) hs j))


theorem difference_time {d m : ℕ} (hm : 0 < m) (n S : ℕ) (hn : 0 < n)
    (hS : 0 < S) (x y : Space d) (start : ℝ≥0) (rows : ℕ → ChoiceRow)
    (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞) (hmono : Monotone τ)
    (answer : ℕ → Option (Request d m n) → Reply d n)
    (hservice : servicePath f τ answer) :
    (((differenceTrace n S x y start rows answer S).clock - start : ℝ≥0) : ℝ≥0∞) ≤
      4 * equilibriumTime τ S := by
  open scoped BigOperators ENNReal NNReal in
    classical
    have hlabel (row : ChoiceRow) : ∃ i : Fin m, labelAt row m = some i := by
      delta labelAt
      simp only [hm, dite_true]
      exact ⟨_, rfl⟩
    let tr := differenceTrace n S x y start rows answer
    have hinv : ∀ a, a ≤ S →
        (tr a).target = S ∧ (tr a).count = a ∧
          ∀ i, ∃ job, (tr a).pending i = some job ∧ job.started ≤ (tr a).clock ∧
            ((tr a).clock : ℝ≥0∞) ≤ deadline τ job i := by
      intro a
      induction a with
      | zero =>
        intro _
        refine ⟨rfl, rfl, ?_⟩
        intro i
        obtain ⟨b, hb⟩ := hlabel (rows i.val)
        let job : Job d m := ⟨b, Sum.inr (x,y), start, i.val⟩
        refine ⟨job, ?_, le_rfl, ?_⟩
        · change (if S = 0 then none else dispatch (Sum.inr (x,y)) start (0+i.val)
            (labelAt (rows (0+i.val)) m)) = some job
          rw [ite_eq_right hS.ne']
          simp only [zero_add, hb]
          rfl
        · change (start : ℝ≥0∞) ≤ (start : ℝ≥0∞) + (2 : ℕ) * τ i
          exact le_add_of_nonneg_right zero_le
      | succ a ih =>
        intro ha
        have haS : a < S := by omega
        obtain ⟨htarget, hcount, hpending⟩ := ih (by omega)
        let s := tr a
        let r : Request d m n := ⟨s.clock, s.pending⟩
        change s.target = S at htarget
        change s.count = a at hcount
        have hlegal : legalRequest τ r := by
          constructor
          · let i : Fin n := ⟨0, hn⟩
            obtain ⟨job, hj, _, _⟩ := hpending i
            exact ⟨i, job, hj⟩
          · intro i job hj
            obtain ⟨job', hj', hstart, htime⟩ := hpending i
            have heq : job = job' := Option.some.inj (hj.symm.trans hj')
            subst job'
            exact ⟨hstart, htime⟩
        have hactive : ¬s.target ≤ s.count := by
          rw [htarget, hcount]
          omega
        have hquery : differenceQuery s = some r := by
          delta differenceQuery
          rw [ite_eq_right hactive]
          delta pendingRequest
          have hex : ∃ i, s.pending i ≠ none := by
            obtain ⟨i, job, hj⟩ := hlegal.1
            change s.pending i = some job at hj
            exact ⟨i, by rw [hj]; simp⟩
          rw [ite_eq_left hex]
        obtain ⟨i, job, c, hj, hreply, hc, hdeadline⟩ := (hservice a).2 r hlegal
        change s.pending i = some job at hj
        change s.clock ≤ c at hc
        obtain ⟨b, hb⟩ := hlabel (s.rows s.nextID)
        let next : Job d m := ⟨b, Sum.inr (s.x,s.y), c, s.nextID⟩
        let t : DifferenceState d m n :=
          { s with
            count := s.count+1
            sum := s.sum+jobValue f job
            pending := Function.update s.pending i (some next)
            clock := c
            nextID := s.nextID+1 }
        have hnext : tr (a+1) = t := by
          change differenceUpdate s (answer a (differenceQuery s)) = t
          rw [hquery, hreply]
          delta differenceUpdate
          rw [ite_eq_right hactive]
          dsimp only
          rw [hj]
          dsimp only
          rw [ite_eq_left (And.intro rfl hc)]
          delta dispatch
          rw [hb]
          rfl
        rw [hnext]
        refine ⟨htarget, ?_, ?_⟩
        · change s.count + 1 = a + 1
          rw [hcount]
        · intro k
          by_cases hk : k = i
          · subst k
            refine ⟨next, ?_, le_rfl, ?_⟩
            · exact Function.update_self _ _ _
            · change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞) + (2 : ℕ) * τ i
              exact le_add_of_nonneg_right zero_le
          · obtain ⟨old, hold, hstarted, _⟩ := hpending k
            refine ⟨old, ?_, hstarted.trans hc, hdeadline k old hold⟩
            change Function.update s.pending i (some next) k = some old
            rw [Function.update_of_ne hk]
            exact hold
    let C (a : ℕ) := (tr a).clock
    let V (a : ℕ) (i : Fin n) := (((tr a).pending i).map Job.started).getD 0
    have hVle (a : ℕ) (ha : a ≤ S) (i : Fin n) : V a i ≤ C a := by
      obtain ⟨job,hj,hs,_⟩ := (hinv a ha).2.2 i
      simpa only [V, C, hj, Option.map_some, Option.getD_some] using hs
    have hV0 (i : Fin n) : V 0 i = start := by
      obtain ⟨b,hb⟩ := hlabel (rows i.val)
      change ((if S = 0 then none else dispatch (Sum.inr (x,y)) start (0+i.val)
        (labelAt (rows (0+i.val)) m)).map Job.started).getD 0 = start
      rw [ite_eq_right hS.ne']
      simp only [zero_add,hb]
      rfl
    have hstep (a : ℕ) (ha : a < S) : ∃ i : Fin n, ∃ c : ℝ≥0,
        C a ≤ c ∧ C (a+1) = c ∧ V (a+1) = Function.update (V a) i c ∧
          ∀ k job, (tr a).pending k = some job → (c : ℝ≥0∞) ≤ deadline τ job k := by
      obtain ⟨htarget,hcount,hpending⟩ := hinv a ha.le
      let s := tr a
      let r : Request d m n := ⟨s.clock,s.pending⟩
      change s.target = S at htarget
      change s.count = a at hcount
      have hlegal : legalRequest τ r := by
        constructor
        · obtain ⟨job,hj,_,_⟩ := hpending ⟨0,hn⟩
          exact ⟨⟨0,hn⟩,job,hj⟩
        · intro i job hj
          obtain ⟨job',hj',hs,ht⟩ := hpending i
          have heq : job = job' := Option.some.inj (hj.symm.trans hj')
          subst job'
          exact ⟨hs,ht⟩
      have hactive : ¬s.target ≤ s.count := by rw [htarget,hcount]; omega
      have hquery : differenceQuery s = some r := by
        delta differenceQuery
        rw [ite_eq_right hactive]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          change s.pending i = some job at hj
          exact ⟨i, by rw [hj]; simp⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,c,hj,hreply,hc,hdeadline⟩ := (hservice a).2 r hlegal
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      obtain ⟨b,hb⟩ := hlabel (s.rows s.nextID)
      let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
      let t : DifferenceState d m n :=
        { s with
          count := s.count+1
          sum := s.sum+jobValue f job
          pending := Function.update s.pending i (some next)
          clock := c
          nextID := s.nextID+1 }
      have hnext : tr (a+1) = t := by
        change differenceUpdate s (answer a (differenceQuery s)) = t
        rw [hquery,hreply]
        delta differenceUpdate
        rw [ite_eq_right hactive]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
        delta dispatch
        rw [hb]
        rfl
      refine ⟨i,c,hc,?_,?_,hdeadline⟩
      · change (tr (a+1)).clock = c
        rw [hnext]
      · funext k
        dsimp only [V]
        rw [hnext]
        by_cases hk : k = i
        · subst k
          simp only [t,Function.update_self,Option.map_some,Option.getD_some]
          rfl
        · simp only [t,Function.update_of_ne hk]
          rfl
    have hcap (c : ℝ≥0) (i : Fin n) (job : Job d m) (hfinite : τ i ≠ ⊤)
        (hc : (c : ℝ≥0∞) ≤ deadline τ job i) :
        (c : ℝ) ≤ (job.started : ℝ)+2*(τ i).toReal := by
      have hwork : (jobWork job : ℝ≥0∞) ≤ 2 := by
        delta jobWork
        cases job.kind <;> dsimp only <;> norm_num
      have hh : (c : ℝ≥0∞) ≤ (job.started : ℝ≥0∞)+2*τ i :=
        hc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hwork zero_le))
      have hfin : (job.started : ℝ≥0∞)+2*τ i ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) hfinite⟩
      have hreal := ENNReal.toReal_mono hfin hh
      obtain ⟨h₁,h₂⟩ := ENNReal.add_ne_top.mp hfin
      rw [ENNReal.toReal_add h₁ h₂] at hreal
      simpa only [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hreal
    have hcapV (a : ℕ) (ha : a ≤ S) (i : Fin n) (hi : τ i ≠ ⊤) :
        (C a : ℝ) ≤ (V a i : ℝ)+2*(τ i).toReal := by
      obtain ⟨job,hj,_,ht⟩ := (hinv a ha).2.2 i
      simpa only [V,C,hj,Option.map_some,Option.getD_some] using hcap (C a) i job hi ht
    have hstart : ∀ a, a ≤ S → start ≤ C a := by
      intro a
      induction a with
      | zero => intro _; exact le_rfl
      | succ a ih =>
        intro ha
        obtain ⟨i,c,hc,hnext,_,_⟩ := hstep a (by omega)
        rw [hnext]
        exact (ih (by omega)).trans hc
    by_cases hzero : ∃ i, τ i = 0
    · obtain ⟨i,hi⟩ := hzero
      have hclock : ∀ a, a ≤ S → C a = start := by
        intro a
        induction a with
        | zero => intro _; rfl
        | succ a ih =>
          intro ha
          obtain ⟨k,c,hc,hnext,_,ht⟩ := hstep a (by omega)
          obtain ⟨job,hj,hs,_⟩ := (hinv a (by omega)).2.2 i
          have hb := hcap c i job (by rw [hi]; simp) (ht i job hj)
          rw [hi] at hb
          simp only [ENNReal.toReal_zero,mul_zero,add_zero] at hb
          have hle : c ≤ C a := by exact_mod_cast hb.trans (by exact_mod_cast hs)
          rw [hnext, le_antisymm hle hc, ih (by omega)]
      change ((C S-start : ℝ≥0) : ℝ≥0∞) ≤ _
      rw [hclock S le_rfl,tsub_self]
      exact zero_le
    have hτpos : ∀ i, 0 < τ i := by
      intro i
      exact pos_iff_ne_zero.mpr (fun hi => hzero ⟨i,hi⟩)
    by_cases htop : ∀ i, τ i = ⊤
    · rw [LongTails.Proofs.FreyaEquilibrium.equilibrium_top τ htop]
      simp
    have hτfinite : ∃ i, τ i ≠ ⊤ := by simpa only [not_forall] using htop
    have hSE : (0 : ℝ≥0∞) < S := by exact_mod_cast hS
    obtain ⟨htpos,htfinite⟩ := LongTails.Proofs.FreyaEquilibrium.equilibrium_finite_positive τ hτpos hτfinite S hSE (by simp)
    obtain ⟨j,hjtime,hjeq⟩ := LongTails.Proofs.FreyaEquilibrium.prefix_threshold hn τ hmono hτpos hτfinite S hSE (by simp)
    have hτjfinite : τ j ≠ ⊤ := ne_top_of_le_ne_top htfinite hjtime
    have hfinite (i : Fin n) (hi : i ∈ Finset.Iic j) : τ i ≠ ⊤ :=
      ne_top_of_le_ne_top hτjfinite (hmono (Finset.mem_Iic.mp hi))
    have hpositive (i : Fin n) (hi : i ∈ Finset.Iic j) : 0 < (τ i).toReal :=
      ENNReal.toReal_pos (hτpos i).ne' (hfinite i hi)
    let H : ℝ := ∑ i ∈ Finset.Iic j, 1/(2*(τ i).toReal)
    let F (a : ℕ) : ℝ := ∑ i ∈ Finset.Iic j, (V a i : ℝ)/(2*(τ i).toReal)
    have hH : 0 < H := by
      apply Finset.sum_pos
      · intro i hi
        exact one_div_pos.mpr (mul_pos (by norm_num) (hpositive i hi))
      · exact ⟨j,Finset.mem_Iic.mpr le_rfl⟩
    have hF0 : F 0 = (start : ℝ)*H := by
      dsimp only [F,H]
      simp_rw [hV0, div_eq_mul_inv, one_mul]
      exact (Finset.mul_sum _ _ _).symm
    have hFstep (a : ℕ) (ha : a < S) : F (a+1) ≤ F a+1 := by
      obtain ⟨i,c,hc,hnext,hupdate,hdeadline⟩ := hstep a ha
      have hpoint (k : Fin n) : (V (a+1) k : ℝ)/(2*(τ k).toReal) =
          (V a k : ℝ)/(2*(τ k).toReal) +
            if k = i then ((c : ℝ)-(V a i : ℝ))/(2*(τ i).toReal) else 0 := by
        rw [hupdate]
        by_cases hk : k = i
        · subst k
          rw [Function.update_self,ite_eq_left rfl]
          ring
        · rw [Function.update_of_ne hk,ite_eq_right hk,add_zero]
      change (∑ k ∈ Finset.Iic j, (V (a+1) k : ℝ)/(2*(τ k).toReal)) ≤ _
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib]
      by_cases hi : i ∈ Finset.Iic j
      · rw [Finset.sum_ite_eq',ite_eq_left hi]
        obtain ⟨job,hjob,_,_⟩ := (hinv a ha.le).2.2 i
        have hb := hcap c i job (hfinite i hi) (hdeadline i job hjob)
        have he : V a i = job.started := by simp only [V,hjob,Option.map_some,Option.getD_some]
        rw [← he] at hb
        have hinc : ((c : ℝ)-(V a i : ℝ))/(2*(τ i).toReal) ≤ 1 := by
          apply (div_le_one (mul_pos (by norm_num) (hpositive i hi))).mpr
          linarith only [hb]
        exact add_le_add le_rfl hinc
      · rw [Finset.sum_ite_eq',ite_eq_right hi,add_zero]
        exact le_add_of_nonneg_right zero_le_one
    have hFbound : ∀ a, a ≤ S → F a ≤ (start : ℝ)*H+a := by
      intro a
      induction a with
      | zero => intro _; simp only [Nat.cast_zero,add_zero]; exact hF0.le
      | succ a ih =>
        intro ha
        have hs := hFstep a (by omega)
        have hi := ih (by omega)
        rw [Nat.cast_add,Nat.cast_one]
        linarith only [hs,hi]
    have hCbound : (C S : ℝ)*H ≤ F S+(j.val+1 : ℕ) := by
      calc
        (C S : ℝ)*H = ∑ i ∈ Finset.Iic j, (C S : ℝ)/(2*(τ i).toReal) := by
          dsimp only [H]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i ∈ Finset.Iic j, ((V S i : ℝ)/(2*(τ i).toReal)+1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hc := hcapV S le_rfl i (hfinite i hi)
          apply (div_le_iff₀ (mul_pos (by norm_num) (hpositive i hi))).mpr
          have he : ((V S i : ℝ)/(2*(τ i).toReal)+1)*(2*(τ i).toReal) =
              (V S i : ℝ)+2*(τ i).toReal := by field_simp [(hpositive i hi).ne']
          rw [he]
          exact hc
        _ = F S+(j.val+1 : ℕ) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp
    have helapsed : ((C S : ℝ)-(start : ℝ))*H ≤ (S : ℝ)+(j.val+1 : ℕ) := by
      have hf := hFbound S le_rfl
      nlinarith only [hCbound,hf]
    let R : ℝ≥0∞ := ∑ i ∈ Finset.Iic j, (τ i)⁻¹
    have hRfinite : R ≠ ⊤ := by
      apply ENNReal.sum_ne_top.mpr
      intro i _
      exact ENNReal.inv_ne_top.mpr (hτpos i).ne'
    have hRreal : R.toReal = 2*H := by
      dsimp only [R,H]
      rw [ENNReal.toReal_sum (fun i _ => ENNReal.inv_ne_top.mpr (hτpos i).ne'),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.toReal_inv]
      ring
    have htimeR : (equilibriumTime τ S).toReal = ((S : ℝ)+(j.val+1 : ℕ))/(2*H) := by
      rw [hjeq,ENNReal.toReal_div,ENNReal.toReal_add (by simp) (by simp),
        ENNReal.toReal_natCast,ENNReal.toReal_natCast]
      change _/R.toReal = _
      rw [hRreal]
    have htwo : ((C S : ℝ)-(start : ℝ)) ≤ 2*(equilibriumTime τ S).toReal := by
      rw [htimeR]
      apply (mul_le_mul_iff_right₀ hH).mp
      have he : (2*(((S : ℝ)+(j.val+1 : ℕ))/(2*H)))*H = (S : ℝ)+(j.val+1 : ℕ) := by
        field_simp [hH.ne']
      nlinarith only [helapsed,he]
    have hfour : ((C S : ℝ)-(start : ℝ)) ≤ 4*(equilibriumTime τ S).toReal := by
      have ht := ENNReal.toReal_nonneg (a := equilibriumTime τ S)
      linarith only [htwo,ht]
    apply (ENNReal.toReal_le_toReal (by simp) (ENNReal.mul_ne_top (by simp) htfinite)).mp
    change (((C S-start : ℝ≥0) : ℝ≥0∞)).toReal ≤ _
    simpa only [ENNReal.coe_toReal,NNReal.coe_sub (hstart S le_rfl),ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] using hfour


open LongTails.Algorithms.FreyaPage

structure ScheduleState (n : ℕ) where
  jobs : Fin n → ℕ × ℝ≥0∞
  nextID : ℕ

noncomputable def scheduleWorker {n : ℕ} (γ : BatchSchedule n) (call : ℕ)
    (s : ScheduleState n) : Option (Fin n) := by
  classical
  let finish := fun i => (s.jobs i).2 + γ.duration i (s.jobs i).1
  exact (List.finRange n).foldl (fun best i =>
    match best with
    | none => some i
    | some b => if finish i < finish b ∨ (finish i = finish b ∧
        (γ.priority call i < γ.priority call b ∨
          (γ.priority call i = γ.priority call b ∧ i.val ≤ b.val))) then some i else some b) none

noncomputable def scheduleTrace {n : ℕ} (γ : BatchSchedule n) (firstID callStart : ℕ)
    (clock : ℝ≥0) : ℕ → ScheduleState n
  | 0 => ⟨fun i => (firstID + i.val, clock), firstID + n⟩
  | k + 1 =>
    let s := scheduleTrace γ firstID callStart clock k
    match scheduleWorker γ (callStart + k) s with
    | none => s
    | some i =>
      ⟨Function.update s.jobs i (s.nextID, (s.jobs i).2 + γ.duration i (s.jobs i).1), s.nextID + 1⟩

noncomputable def selectedJobID {n : ℕ} (γ : BatchSchedule n)
    (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) : ℕ :=
  let s := scheduleTrace γ firstID callStart clock k
  ((scheduleWorker γ (callStart + k) s).map fun i => (s.jobs i).1).getD 0

noncomputable def completedJob (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) (j : Fin q.S) :
    Option (Job q.d q.m) :=
  let call := (batchStartCall q O seed ω batch).getD 0 + j.val
  let s := trace q O seed ω call
  match (query q s).2, replyAt q O seed ω call (query q s) with
  | some r, some (i, id, _, _) => (r.pending i).bind fun job =>
      if job.id = id then some job else none
  | _, _ => none

noncomputable def completedLabels (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) :
    Fin q.S → Option (Fin q.m) :=
  fun j => (completedJob q O seed ω batch j).map fun job => job.component

noncomputable def batchResult (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Space q.d :=
  if q.S = 0 then 0 else
    let call := (batchStartCall q O seed ω batch).getD 0 + (q.S - 1)
    let s := trace q O seed ω call
    match s.phase with
    | .difference c => differenceResult (differenceUpdate c (replyAt q O seed ω call (query q s)))
    | _ => 0

noncomputable def batchInputs (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Space q.d × Space q.d :=
  ((invocation q O seed ω batch).map fun a => (a.2.1, a.2.2.1)).getD (0, 0)

noncomputable def executionLaw (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) :
    ProbabilityMeasure (Seed q.K × ((k : ℕ) → O.Seed k)) :=
  ⟨(seedLaw q.ρ q.K : Measure (Seed q.K)).prod
    (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩

theorem schedule_selection (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
    (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0, r)))
    (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
    (hinvoke : invocation q O seed ω batch = some (false, x, y, clock, firstID))
    (γ : BatchSchedule q.n) (hγ : ScheduleRealization q f τ O seed ω batch γ) :
    let callStart := (batchStartCall q O seed ω batch).getD 0
    Function.Injective (fun j : Fin q.S => selectedJobID γ firstID callStart clock j.val) ∧
      (∀ j : Fin q.S, (completedJob q O seed ω batch j).map (fun job => job.id) =
        some (selectedJobID γ firstID callStart clock j.val)) ∧
      ∀ j : Fin q.S, completedLabels q O seed ω batch j =
        batchLabels q seed batch (selectedJobID γ firstID callStart clock j.val) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Proofs.FreyaCollectors LongTails.Setups.FreyaIndependence in
    classical
    have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
      clear * - q s

      delta advance
      split <;> rfl
    have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
        (update q s reply).seed = s.seed := by
      clear * - q s reply freyaPageAdvanceSeed

      delta update
      cases hs : s.phase with
      | halted => rfl
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
    have freyaPageTraceSeed (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
        (trace q O seed ω k).seed = seed := by
      clear * - q O seed ω k freyaPageUpdateSeed

      induction k with
      | zero => rfl
      | succ k ih =>
        change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
        rw [freyaPageUpdateSeed,ih]
    have freyaPageHaltedUpdate (q : Raw) (s : State q) (reply : Reply q.d q.n)
        (h : active s = false) : update q s reply = s := by
      clear * - q s reply h

      cases hs : s.phase with
      | halted => delta update; rw [hs]
      | full first c =>
        delta active at h
        rw [hs] at h
        contradiction
      | difference c =>
        delta active at h
        rw [hs] at h
        contradiction
    have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
        (h : (List.range N).find? p = some k) :
        k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
      clear * - N p k h

      obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
      simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
      subst i
      refine ⟨hi,hp,?_⟩
      intro r hr htrue
      have hh := hprev r hr
      rw [htrue] at hh
      contradiction
    have freyaPageBatchStartFacts (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (h : batchStartCall q O seed ω batch = some call) :
        call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
          active (trace q O seed ω call) = true ∧
          ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
      clear * - q O seed ω batch call h freyaPageFirstMatch

      delta batchStartCall at h
      obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
      obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
      refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
      intro r hr hh
      apply hprev r hr
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
    have freyaPageDifferenceInvocation (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
        (x y : Space q.d) (clock : ℝ≥0)
        (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
        ∃ call c, batchStartCall q O seed ω batch = some call ∧
          (trace q O seed ω call).phase = Phase.difference c ∧
          c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
      clear * - q O seed ω batch firstID x y clock h

      delta invocation at h
      cases hs : batchStartCall q O seed ω batch with
      | none => rw [hs] at h; cases h
      | some call =>
        rw [hs] at h
        dsimp only [Option.bind] at h
        cases hp : (trace q O seed ω call).phase with
        | halted => rw [hp] at h; cases h
        | full first c => rw [hp] at h; cases h
        | difference c =>
          rw [hp] at h
          have heq := Option.some.inj h
          have hfields : c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
            simpa (config := { iota := false }) only [Prod.mk.injEq,true_and] using heq
          exact ⟨call,c,rfl,hp,hfields⟩
    have freyaPageDifferenceEntryAdvance (q : Raw) (s : State q) (reply : Reply q.d q.n)
        (c : DifferenceState q.d q.m q.n) (hphase : (update q s reply).phase = Phase.difference c)
        (hfresh : ¬(s.iteration = (update q s reply).iteration ∧ active s = true)) :
        ∃ t : State q, t.seed = s.seed ∧ advance q t = update q s reply := by
      clear * - q s reply c hphase hfresh

      delta update at hphase hfresh ⊢
      cases hs : s.phase with
      | halted =>
        rw [hs] at hphase
        change s.phase = Phase.difference c at hphase
        rw [hs] at hphase
        cases hphase
      | full first old =>
        rw [hs] at hphase hfresh
        dsimp only at hphase hfresh ⊢
        by_cases he : (fullUpdate old reply).remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact ⟨{s with
            g := fullResult (fullUpdate old reply)
            clock := (fullUpdate old reply).clock
            nextID := (fullUpdate old reply).nextID
            phase := Phase.full first (fullUpdate old reply)},rfl,rfl⟩
        · rw [ite_eq_right he] at hphase
          cases hphase
      | difference old =>
        rw [hs] at hphase hfresh
        dsimp only at hphase hfresh ⊢
        by_cases he : (differenceUpdate old reply).target ≤ (differenceUpdate old reply).count
        · rw [ite_eq_left he]
          exact ⟨{s with
            g := s.g+differenceResult (differenceUpdate old reply)
            clock := (differenceUpdate old reply).clock
            nextID := (differenceUpdate old reply).nextID
            phase := Phase.difference (differenceUpdate old reply)},rfl,rfl⟩
        · apply False.elim
          rw [ite_eq_right he] at hfresh
          apply hfresh
          constructor
          · rfl
          · delta active
            rw [hs]
    have freyaPageAdvanceDifference (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n)
        (h : (advance q s).phase = Phase.difference c) :
        (advance q s).iteration = s.iteration+1 ∧
          c = differenceInitial q.n q.S (s.x-q.η • s.g) s.x s.clock
            (s.seed.1 (s.iteration+1)) s.nextID := by
      clear * - q s c h

      delta advance at h ⊢
      split at h
      · contradiction
      · rename_i hn
        rw [ite_eq_right hn]
        dsimp only at h ⊢
        split at h
        · contradiction
        · exact ⟨rfl,(Phase.difference.inj h).symm⟩
    have freyaPageFreshDifference (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
        (x y : Space q.d) (clock : ℝ≥0)
        (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
        ∃ call, batchStartCall q O seed ω batch = some call ∧
          (trace q O seed ω call).phase = Phase.difference
            (differenceInitial q.n q.S x y clock (seed.1 batch) firstID) := by
      clear * - q O seed ω batch firstID x y clock h freyaPageTraceSeed freyaPageBatchStartFacts freyaPageDifferenceInvocation freyaPageDifferenceEntryAdvance freyaPageAdvanceDifference

      obtain ⟨call,c,hstart,hphase,hx,hy,hclock,hid⟩ :=
        freyaPageDifferenceInvocation q O seed ω batch firstID x y clock h
      have hfacts := freyaPageBatchStartFacts q O seed ω batch call hstart
      cases call with
      | zero =>
        change (initial q seed).phase = Phase.difference c at hphase
        delta initial at hphase
        dsimp only at hphase
        split at hphase <;> contradiction
      | succ k =>
        have hprev := hfacts.2.2.2 k (Nat.lt_succ_self k)
        rw [← hfacts.2.1] at hprev
        obtain ⟨t,htseed,ht⟩ := freyaPageDifferenceEntryAdvance q
          (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) c hphase hprev
        have httrace : advance q t = trace q O seed ω (k+1) := ht
        have htc : (advance q t).phase = Phase.difference c := by rw [httrace]; exact hphase
        obtain ⟨hit,hc⟩ := freyaPageAdvanceDifference q t c htc
        have hbatch : t.iteration+1 = batch := by rw [← hit,httrace]; exact hfacts.2.1
        have hseed : t.seed = seed := htseed.trans (freyaPageTraceSeed q O seed ω k)
        rw [hc] at hx hy hclock hid
        dsimp only [differenceInitial] at hx hy hclock hid
        have hfirst : t.nextID = firstID := by omega
        refine ⟨k+1,hstart,?_⟩
        rw [hphase,hc,hx,hy,hclock,hseed,hbatch,hfirst]
    have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
        (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
            r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
        (ha : s.count < s.target)
        (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
          (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
        ∃ i job c next,
          s.pending i = some job ∧
          differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
          reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
          s.clock ≤ c ∧
          next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
          labelAt (s.rows s.nextID) m = some next.component ∧
          differenceUpdate s (reply (differenceQuery s)) =
            {s with
              count := s.count+1
              sum := s.sum+jobValue f job
              pending := Function.update s.pending i (some next)
              clock := c
              nextID := s.nextID+1} ∧
          ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
            old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
      clear * - d m n hm hn s f τ reply hservice ha hp

      classical
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := by
        refine ⟨?_,?_⟩
        · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
          exact ⟨⟨0,hn⟩,job,hj⟩
        · intro i job hj
          obtain ⟨old,hold,hs,ht,_⟩ := hp i
          have heq : job=old := Option.some.inj (hj.symm.trans hold)
          subst old
          exact ⟨hs,ht⟩
      have hquery : differenceQuery s = some r := by
        delta differenceQuery
        rw [ite_eq_right (by omega)]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          change s.pending i=some job at hj
          exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
      change s.pending i=some job at hjob
      change s.clock≤c at hclock
      obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
        delta labelAt
        simp (config := { iota := false }) only [hm,dite_true]
        exact ⟨_,rfl⟩
      let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
      refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
      · rw [hquery]; exact hreply
      · rw [hquery,hreply]
        delta differenceUpdate
        rw [ite_eq_right (by omega)]
        dsimp only
        rw [hjob]
        dsimp only
        rw [ite_eq_left (And.intro rfl hclock)]
        delta dispatch
        rw [hb]
        rfl
      · intro k
        by_cases hk : k=i
        · subst k
          refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
          change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
          exact le_add_of_nonneg_right zero_le
        · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
          refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
          rw [Function.update_of_ne hk]
          exact hold
    have freyaPageDifferenceQuery (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
        query q s = (0,differenceQuery c) := by
      clear * - q s c h

      delta query
      rw [h]
      rfl
    have freyaPageDifferenceContinue (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n) (reply : Reply q.d q.n)
        (h : s.phase = Phase.difference c)
        (ha : (differenceUpdate c reply).count < (differenceUpdate c reply).target) :
        (update q s reply).phase = Phase.difference (differenceUpdate c reply) ∧
          (update q s reply).iteration = s.iteration := by
      clear * - q s c reply h ha

      delta update
      rw [h]
      dsimp only
      rw [ite_eq_right (by omega)]
      exact ⟨rfl,rfl⟩
    have freyaPageCompletedJobEq (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ) (j : Fin q.S)
        (hstart : batchStartCall q O seed ω batch = some call)
        (c : DifferenceState q.d q.m q.n)
        (hphase : (trace q O seed ω (call+j.val)).phase = Phase.difference c)
        (hq : differenceQuery c = some ⟨c.clock,c.pending⟩)
        (i : Fin q.n) (job : Job q.d q.m) (time : ℝ≥0) (value : Space q.d)
        (hj : c.pending i = some job)
        (hr : replyAt q O seed ω (call+j.val) (0,differenceQuery c) =
          some (i,job.id,time,value)) : completedJob q O seed ω batch j = some job := by
      clear * - q O seed ω batch call j hstart c hphase hq i job time value hj hr freyaPageDifferenceQuery

      have hquery := freyaPageDifferenceQuery q _ c hphase
      delta completedJob
      rw [hstart]
      dsimp only [Option.getD]
      rw [hquery]
      dsimp only
      rw [hr,hq]
      dsimp only
      rw [hj]
      dsimp only [Option.bind]
      rw [ite_eq_left rfl]
    have freyaPageBatchProgress (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
        (hS : 0 < q.S) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (batch firstID call : ℕ) (x y : Space q.d) (clock : ℝ≥0)
        (hstart : batchStartCall q O seed ω batch = some call)
        (hphase : (trace q O seed ω call).phase = Phase.difference
          (differenceInitial q.n q.S x y clock (seed.1 batch) firstID)) :
        let D := fun k : ℕ => if hk : k < q.S then
          (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
            (fun i => gradient (f i) x-gradient (f i) y) else 0
        ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
          (trace q O seed ω (call+a)).phase = Phase.difference c ∧
          (trace q O seed ω (call+a)).iteration = batch ∧
          c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
          c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
          ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
            batchLabels q seed batch job.id=some job.component := by
      clear * - q hm hn hS f τ O seed ω hservice batch firstID call x y clock hstart hphase freyaPageBatchStartFacts freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageDifferenceContinue freyaPageCompletedJobEq

      classical
      dsimp only
      let D := fun k : ℕ => if hk : k < q.S then
          (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
            (fun i => gradient (f i) x-gradient (f i) y) else 0
      change ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
          (trace q O seed ω (call+a)).phase = Phase.difference c ∧
          (trace q O seed ω (call+a)).iteration = batch ∧
          c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
          c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
          ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
            batchLabels q seed batch job.id=some job.component
      intro a
      induction a with
      | zero =>
        intro _
        refine ⟨differenceInitial q.n q.S x y clock (seed.1 batch) firstID,?_,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
        · simpa (config := { iota := false }) only [Nat.add_zero] using hphase
        · simpa (config := { iota := false }) only [Nat.add_zero] using (freyaPageBatchStartFacts q O seed ω batch call hstart).2.1
        · change firstID+q.n=firstID+q.n+0
          omega
        · exact (Finset.sum_range_zero D).symm
        · intro i
          obtain ⟨b,hb⟩ : ∃ b : Fin q.m, labelAt (seed.1 batch (firstID+i.val)) q.m=some b := by
            delta labelAt
            simp (config := { iota := false }) only [hm,dite_true]
            exact ⟨_,rfl⟩
          let job : Job q.d q.m := ⟨b,Sum.inr (x,y),clock,firstID+i.val⟩
          refine ⟨job,?_,le_rfl,?_,rfl,hb⟩
          · change (if q.S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
              (labelAt (seed.1 batch (firstID+i.val)) q.m))=some job
            rw [ite_eq_right (by omega),hb]
            rfl
          · exact le_add_of_nonneg_right zero_le
      | succ a ih =>
        intro ha
        have haS : a<q.S := by omega
        obtain ⟨c,hc,hit,htarget,hcount,hx,hy,hrows,hid,hsum,hpending⟩ := ih haS
        have hp : ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
          intro i
          obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
          rw [hx,hy]
          exact ⟨job,hj,hs,ht,hk⟩
        obtain ⟨i,job,time,next,hjob,hquery,hreply,hclock,hnid,hnkind,hnstart,hnlabel,hnext,hpnext⟩ :=
          freyaDifferenceLiveStep hm hn c f τ
            (fun r => replyAt q O seed ω (call+a) (0,r))
            (hservice (call+a)).2 (by omega) hp
        let t := differenceUpdate c (replyAt q O seed ω (call+a) (0,differenceQuery c))
        have ht := hnext
        change t = _ at ht
        have hqueryPage := freyaPageDifferenceQuery q _ c hc
        have hactive : t.count<t.target := by rw [ht]; dsimp only; omega
        have hcontinue := freyaPageDifferenceContinue q _ c
          (replyAt q O seed ω (call+a) (0,differenceQuery c)) hc hactive
        have hupdate : trace q O seed ω (call+(a+1)) =
            update q (trace q O seed ω (call+a))
              (replyAt q O seed ω (call+a) (0,differenceQuery c)) := by
          rw [← Nat.add_assoc]
          rw [trace_succ]
          rw [hqueryPage]
        obtain ⟨old,hold,_,_,hkind,hlabel⟩ := hpending i
        have heq : old=job := Option.some.inj (hold.symm.trans hjob)
        subst old
        have hcompleted := freyaPageCompletedJobEq q O seed ω batch call ⟨a,haS⟩ hstart
          c hc hquery i job time (jobValue f job) hjob hreply
        have hD : D a=jobValue f job := by
          dsimp only [D]
          rw [dite_eq_left haS]
          delta completedLabels
          rw [hcompleted]
          dsimp only [Option.map,Option.elim]
          delta jobValue
          rw [hkind]
        refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · rw [hupdate]; exact hcontinue.1
        · rw [hupdate,hcontinue.2]; exact hit
        · rw [ht]; exact htarget
        · rw [ht]; dsimp only; omega
        · rw [ht]; exact hx
        · rw [ht]; exact hy
        · rw [ht]; exact hrows
        · rw [ht]; dsimp only; omega
        · rw [ht]; dsimp only; rw [hsum,Finset.sum_range_succ,hD]
        · intro k
          obtain ⟨old,hold,hs,htime,hkind'⟩ := hpnext k
          refine ⟨old,?_,?_,?_,?_,?_⟩
          · rw [ht]; exact hold
          · rw [ht]; exact hs
          · rw [ht]; exact htime
          · simpa (config := { iota := false }) only [hx,hy] using hkind'
          · by_cases hk : k=i
            · subst k
              rw [Function.update_self] at hold
              have heq : next=old := Option.some.inj hold
              subst old
              change labelAt (seed.1 batch next.id) q.m=some next.component
              rw [hnid,← hrows]
              exact hnlabel
            · rw [Function.update_of_ne hk] at hold
              obtain ⟨old',hold',_,_,_,hl⟩ := hpending k
              have heq : old=old' := Option.some.inj (hold.symm.trans hold')
              subst old'
              exact hl
    have freyaFullPotentialDecrease {d m n : ℕ} (hn : 0<n)
        (labels : List (Fin m)) (s : FullState d m n)
        (horig : s.original=labels) (hne : s.remaining≠[])
        (hbound : ∀ b ∈ s.remaining,b<labels.length)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hr : legalRequest τ ⟨s.clock,s.pending⟩)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
          r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
        let good (s : FullState d m n) := Finset.univ.filter fun i =>
          ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
        let V (s : FullState d m n) :=
          if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
        V (fullUpdate s (reply (fullQuery s)))+1≤V s := by
      clear * - d m n hn labels s horig hne hbound f τ reply hr hservice

      classical
      dsimp only
      let good (s : FullState d m n) : Finset (Fin n) := Finset.univ.filter fun i =>
        ∃ job, s.pending i = some job ∧ ∃ b ∈ s.remaining, labels[b]? = some job.component
      let V (s : FullState d m n) : ℕ :=
        if s.remaining = [] then 0 else n * (s.remaining.length + 1) - (good s).card
      have hcard (s : FullState d m n) : (good s).card ≤ n := by
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
      have hselect (rem : List ℕ) (hne : rem ≠ [])
          (hbound : ∀ b ∈ rem, b < labels.length) (row : ChoiceRow) :
          ∃ b, b ∈ rem ∧ ∃ hb : b < labels.length,
            selectedLabel labels rem row = some labels[b] := by
        have hlen : rem.length ≠ 0 := by
          intro hz
          exact hne (List.length_eq_zero_iff.mp hz)
        let j : Fin rem.length := ⟨(row (rem.length-1)).val, by
          have hj := (row (rem.length-1)).isLt
          omega⟩
        have hb := hbound _ (List.get_mem rem j)
        refine ⟨rem.get j, List.get_mem rem j, hb, ?_⟩
        delta selectedLabel chooseRemaining
        rw [dite_eq_right hlen]
        dsimp only
        exact List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
      have hpositive (s : FullState d m n) (hne : s.remaining ≠ []) : 0 < V s := by
        have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
        have hc := hcard s
        have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
        dsimp only [V]
        rw [ite_eq_right hne, Nat.mul_add, Nat.mul_one]
        omega
      change V (fullUpdate s (reply (fullQuery s)))+1≤V s
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hisEmpty : s.remaining.isEmpty = false := by
        cases h : s.remaining with
        | nil => exact False.elim (hne h)
        | cons b bs => rfl
      have hquery : fullQuery s = some r := by
        delta fullQuery
        simp (config := { iota := false }) only [hisEmpty, Bool.false_eq_true, ite_false]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i, job, hj⟩ := hr.1
          change s.pending i = some job at hj
          exact ⟨i, by rw [hj]; simp (config := { iota := false })⟩
        rw [ite_eq_left hex]
      obtain ⟨i, job, c, hj, hreply, hc, _⟩ := hservice r hr
      change s.pending i = some job at hj
      change s.clock ≤ c at hc
      let found := s.remaining.find? fun b => decide (s.original[b]? = some job.component)
      let rem := found.elim s.remaining (fun b => s.remaining.erase b)
      let next := dispatch (Sum.inl s.point) c s.nextID
        (selectedLabel s.original rem (s.rows s.nextID))
      let t : FullState d m n :=
        { s with
          remaining := rem
          sum := if found.isSome then s.sum + jobValue f job else s.sum
          pending := Function.update s.pending i next
          clock := c
          nextID := s.nextID+1 }
      have hstep : fullUpdate s (reply (fullQuery s)) = t := by
        rw [hquery, hreply]
        delta fullUpdate
        rw [hisEmpty, ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hj]
        dsimp only
        rw [ite_eq_left (And.intro rfl hc)]
      rw [hstep]
      by_cases ht : rem = []
      · have hzero : V t = 0 := by
          dsimp only [V]
          exact ite_eq_left ht
        rw [hzero]
        exact hpositive s hne
      · have hrembound : ∀ b ∈ rem, b < labels.length := by
          cases hf : found with
          | none => simpa (config := { iota := false }) only [rem, hf, Option.elim_none] using hbound
          | some b =>
            intro k hk
            exact hbound k (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem, hf, Option.elim_some] using hk))
        have hgood : i ∈ good t := by
          obtain ⟨b, hb, hbl, hlabel⟩ := hselect rem ht hrembound (s.rows s.nextID)
          simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨labels[b], Sum.inl s.point, c, s.nextID⟩, ?_, b, hb, ?_⟩
          · change Function.update s.pending i next i = _
            rw [Function.update_self]
            change dispatch (Sum.inl s.point) c s.nextID
              (selectedLabel s.original rem (s.rows s.nextID)) = _
            rw [horig, hlabel]
            rfl
          · exact List.getElem?_eq_some_iff.mpr ⟨hbl, rfl⟩
        have hlow : 1 ≤ (good t).card := Finset.card_pos.mpr ⟨i, hgood⟩
        have hcs := hcard s
        have hct := hcard t
        change (if rem = [] then 0 else n*(rem.length+1)-(good t).card)+1 ≤ _
        rw [ite_eq_right ht]
        change n*(rem.length+1)-(good t).card+1 ≤
          if s.remaining = [] then 0 else n*(s.remaining.length+1)-(good s).card
        rw [ite_eq_right hne]
        cases hf : found with
        | some b =>
          have hb : b ∈ s.remaining := List.mem_of_find?_eq_some hf
          have hlen : rem.length+1 = s.remaining.length := by
            dsimp only [rem]
            rw [hf]
            change (s.remaining.erase b).length+1=s.remaining.length
            have hl := List.length_erase_of_mem hb
            have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
            omega
          have hp : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hmul : n ≤ n*s.remaining.length := Nat.le_mul_of_pos_right _ hp
          rw [hlen, Nat.mul_add, Nat.mul_one]
          have calcBound (n a b c : ℕ) (hn : 0<n) (hb : b≤n) (hc : 1≤c)
              (hc' : c≤n) (ha : n≤a) : a-c+1≤a+n-b := by omega
          exact calcBound n (n*s.remaining.length) (good s).card (good t).card hn hcs hlow hct hmul
        | none =>
          have hrem : rem = s.remaining := by simp (config := { iota := false }) only [rem, hf, Option.elim_none]
          have hbad : i ∉ good s := by
            intro hi
            obtain ⟨old, hold, b, hb, hlabel⟩ := (Finset.mem_filter.mp hi).2
            have heq : old = job := Option.some.inj (hold.symm.trans hj)
            subst old
            have hfind := List.find?_eq_none.mp hf b hb
            simp (config := { iota := false }) only [horig, hlabel, decide_true, not_true_eq_false] at hfind
          have hset : good t = insert i (good s) := by
            apply Finset.ext
            intro k
            by_cases hk : k = i
            · subst k
              exact iff_of_true hgood (Finset.mem_insert_self _ _)
            · simp (config := { iota := false }) only [Finset.mem_insert, hk, false_or]
              change (k ∈ Finset.univ.filter fun k =>
                ∃ old, Function.update s.pending i next k = some old ∧
                  ∃ b ∈ rem, labels[b]? = some old.component) ↔ _
              simp (config := { iota := false }) only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [Function.update_of_ne hk, hrem]
              simp (config := { iota := false }) only [good, Finset.mem_filter, Finset.mem_univ, true_and]
          have hcount : (good t).card = (good s).card+1 := by
            rw [hset, Finset.card_insert_of_notMem hbad]
          rw [hrem, hcount, Nat.mul_add, Nat.mul_one]
          have hlen : 0 < s.remaining.length := List.length_pos_iff.mpr hne
          have hmul : n ≤ n * s.remaining.length := Nat.le_mul_of_pos_right _ hlen
          have calcBound (n a b : ℕ) (hn : 0<n) (hb : b≤n) (ha : n≤a) :
              a+n-(b+1)+1≤a+n-b := by omega
          exact calcBound n (n*s.remaining.length) (good s).card hn hcs hmul
    have freyaFullSelect {m : ℕ} (labels : List (Fin m)) (rem : List ℕ)
        (hne : rem≠[]) (hbound : ∀ b ∈ rem,b<labels.length) (row : ChoiceRow) :
        ∃ b, b ∈ rem ∧ ∃ hb : b<labels.length, selectedLabel labels rem row=some labels[b] := by
      clear * - m labels rem hne hbound row

      have hlen : rem.length≠0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
      let j : Fin rem.length := ⟨(row (rem.length-1)).val,by
        have hj := (row (rem.length-1)).isLt
        omega⟩
      have hb := hbound _ (List.get_mem rem j)
      refine ⟨rem.get j,List.get_mem rem j,hb,?_⟩
      delta selectedLabel chooseRemaining
      rw [dite_eq_right hlen]
      dsimp only
      exact List.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩
    have freyaFullSafeUpdate {d m n : ℕ} (s : FullState d m n)
        (hne : s.remaining≠[]) (hbound : ∀ b ∈ s.remaining,b<s.original.length)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hr : legalRequest τ ⟨s.clock,s.pending⟩)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
          r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
        let t := fullUpdate s (reply (fullQuery s))
        t.original=s.original ∧ (∀ b ∈ t.remaining,b<t.original.length) ∧
          (t.remaining≠[] → legalRequest τ ⟨t.clock,t.pending⟩) := by
      clear * - d m n s hne hbound f τ reply hr hservice freyaFullSelect

      classical
      have hisEmpty : s.remaining.isEmpty=false := by
        cases h : s.remaining with
        | nil => exact False.elim (hne h)
        | cons b bs => rfl
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hquery : fullQuery s=some r := by
        delta fullQuery
        rw [hisEmpty,ite_eq_right Bool.false_ne_true]
        delta pendingRequest
        have hex : ∃ i,s.pending i≠none := by
          obtain ⟨i,job,hj⟩ := hr.1
          change s.pending i=some job at hj
          exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,time,hjob,hreply,hclock,hdeadline⟩ := hservice r hr
      change s.pending i=some job at hjob
      change s.clock≤time at hclock
      let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
      let rem := found.elim s.remaining (fun b => s.remaining.erase b)
      let next := dispatch (Sum.inl s.point) time s.nextID
        (selectedLabel s.original rem (s.rows s.nextID))
      let t : FullState d m n :=
        {s with
          remaining := rem
          sum := if found.isSome then s.sum+jobValue f job else s.sum
          pending := Function.update s.pending i next
          clock := time
          nextID := s.nextID+1}
      have ht : fullUpdate s (reply (fullQuery s))=t := by
        rw [hquery,hreply]
        delta fullUpdate
        rw [hisEmpty,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hjob]
        dsimp only
        rw [ite_eq_left (And.intro rfl hclock)]
      have hb : ∀ b ∈ rem,b<s.original.length := by
        cases hf : found with
        | none => simpa (config := { iota := false }) only [rem,hf,Option.elim_none] using hbound
        | some a =>
          intro b h
          exact hbound b (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem,hf,Option.elim_some] using h))
      dsimp only
      rw [ht]
      refine ⟨rfl,hb,?_⟩
      intro htne
      obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect s.original rem htne hb (s.rows s.nextID)
      let new : Job d m := ⟨s.original[b],Sum.inl s.point,time,s.nextID⟩
      have hnew : next=some new := by
        dsimp only [next]
        rw [hlabel]
        rfl
      refine ⟨⟨i,new,?_⟩,?_⟩
      · change Function.update s.pending i next i=some new
        rw [Function.update_self,hnew]
      · intro k old hold
        change Function.update s.pending i next k=some old at hold
        by_cases hk : k=i
        · subst k
          rw [Function.update_self,hnew] at hold
          have heq : new=old := Option.some.inj hold
          subst old
          refine ⟨le_rfl,?_⟩
          exact le_add_of_nonneg_right zero_le
        · rw [Function.update_of_ne hk] at hold
          exact ⟨((hr.2 k old hold).1).trans hclock,hdeadline k old hold⟩
    have freyaFullInitialSafe {d m n : ℕ} (hn : 0<n) (labels : List (Fin m))
        (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow)
        (firstID : ℕ) (τ : Fin n → ℝ≥0∞) :
        let s := fullInitial n labels x clock rows firstID
        s.remaining≠[] ∧ (∀ b ∈ s.remaining,b<s.original.length) ∧
          legalRequest τ ⟨s.clock,s.pending⟩ := by
      clear * - d m n hn labels hne x clock rows firstID τ freyaFullSelect

      classical
      let s := fullInitial n labels x clock rows firstID
      have hrem : (List.range labels.length)≠[] := by
        intro h
        have := congrArg List.length h
        simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
        exact hne (List.length_eq_zero_iff.mp this)
      have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
      refine ⟨hrem,hbound,?_,?_⟩
      · let i : Fin n := ⟨0,hn⟩
        obtain ⟨b,_,hb,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
        refine ⟨i,⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_⟩
        change dispatch (Sum.inl x) clock (firstID+i.val)
          (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
        rw [hlabel]
        rfl
      · intro i job hj
        change dispatch (Sum.inl x) clock (firstID+i.val)
          (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=some job at hj
        delta dispatch at hj
        obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
        cases heq
        exact ⟨le_rfl,le_add_of_nonneg_right zero_le⟩
    have freyaFullInitialPotential {d m n : ℕ} (labels : List (Fin m))
        (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
        let good (s : FullState d m n) := Finset.univ.filter fun i =>
          ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
        let V (s : FullState d m n) :=
          if s.remaining=[] then 0 else n*(s.remaining.length+1)-(good s).card
        V (fullInitial n labels x clock rows firstID) ≤ n*labels.length := by
      clear * - d m n labels hne x clock rows firstID freyaFullSelect

      classical
      let s := fullInitial n labels x clock rows firstID
      let good (s : FullState d m n) := Finset.univ.filter fun i =>
        ∃ job,s.pending i=some job ∧ ∃ b ∈ s.remaining,labels[b]?=some job.component
      have hrem : (List.range labels.length)≠[] := by
        intro h
        have := congrArg List.length h
        simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
        exact hne (List.length_eq_zero_iff.mp this)
      have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
      have hg : good s=Finset.univ := by
        apply Finset.ext
        intro i
        simp (config := { iota := false }) only [good,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
        obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
        refine ⟨⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_,b,hbr,?_⟩
        · change dispatch (Sum.inl x) clock (firstID+i.val)
            (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
          rw [hlabel]
          rfl
        · exact List.getElem?_eq_some_iff.mpr ⟨hbl,rfl⟩
      change (if List.range labels.length=[] then 0 else
        n*((List.range labels.length).length+1)-(good s).card)≤n*labels.length
      rw [ite_eq_right hrem,hg,Finset.card_fin,List.length_range,Nat.mul_add,Nat.mul_one]
      omega
    have freyaDifferenceInitialSafe {d m n : ℕ} (hm : 0<m) (S : ℕ) (hS : 0<S)
        (x y : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ)
        (τ : Fin n → ℝ≥0∞) :
        let c : DifferenceState d m n := differenceInitial n S x y clock rows firstID
        ∀ i, ∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
          (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
      clear * - d m n hm S hS x y clock rows firstID τ

      dsimp only
      intro i
      obtain ⟨b,hb⟩ : ∃ b : Fin m,labelAt (rows (firstID+i.val)) m=some b := by
        delta labelAt
        simp (config := { iota := false }) only [hm,dite_true]
        exact ⟨_,rfl⟩
      refine ⟨⟨b,Sum.inr (x,y),clock,firstID+i.val⟩,?_,le_rfl,?_,rfl⟩
      · change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
          (labelAt (rows (firstID+i.val)) m))=_
        rw [ite_eq_right (by omega),hb]
        rfl
      · exact le_add_of_nonneg_right zero_le
    have freyaPageFullQuery (q : Raw) (s : State q) (first : Bool)
        (c : FullState q.d q.m q.n) (h : s.phase=Phase.full first c) :
        query q s=(0,fullQuery c) := by
      clear * - q s first c h

      delta query
      rw [h]
      rfl
    have freyaPagePhaseSafety (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
        let Safe := fun s : State q =>
          (∀ first c,s.phase=Phase.full first c →
            c.original.length=q.m ∧ c.remaining≠[] ∧
            (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
          (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
            ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
          s.iteration≤rounds q
        ∀ k,Safe (trace q O seed ω k) := by
      clear * - q hm hn hS hK f τ O seed ω hservice freyaDifferenceLiveStep freyaPageDifferenceQuery freyaFullSafeUpdate freyaFullInitialSafe freyaDifferenceInitialSafe freyaPageFullQuery

      classical
      let Safe := fun s : State q =>
          (∀ first c,s.phase=Phase.full first c →
            c.original.length=q.m ∧ c.remaining≠[] ∧
            (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
          (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
            ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
          s.iteration≤rounds q
      change ∀ k,Safe (trace q O seed ω k)
      have hfull (s : State q) (first : Bool) (c : FullState q.d q.m q.n)
          (hp : s.phase=Phase.full first c) (h1 : c.original.length=q.m) (h2 : c.remaining≠[])
          (h3 : ∀ b ∈ c.remaining,b<c.original.length)
          (h4 : legalRequest τ ⟨c.clock,c.pending⟩) (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first' c' he
          rw [hp] at he
          cases he
          exact ⟨h1,h2,h3,h4⟩
        · intro c' he
          rw [hp] at he
          cases he
      have hdiff (s : State q) (c : DifferenceState q.d q.m q.n)
          (hp : s.phase=Phase.difference c) (h1 : c.target=q.S) (h2 : c.count<c.target)
          (h3 : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y))
          (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first c' he
          rw [hp] at he
          cases he
        · intro c' he
          rw [hp] at he
          cases he
          exact ⟨h1,h2,h3⟩
      have hhalt (s : State q) (hp : s.phase=Phase.halted) (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first c he; rw [hp] at he; cases he
        · intro c he; rw [hp] at he; cases he
      have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
        intro he
        have hh := congrArg List.length he
        simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
        omega
      have hadvance (s : State q) (hi : s.iteration≤rounds q) : Safe (advance q s) := by
        delta advance
        split
        · exact hhalt _ rfl hi
        · rename_i hlt
          dsimp only
          by_cases hrefresh : refreshAt s.seed s.iteration=true
          · rw [ite_eq_left hrefresh]
            have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels
              (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID τ
            apply hfull _ false _ rfl (List.length_ofFn) hf.1 hf.2.1 hf.2.2
            dsimp only
            omega
          · rw [ite_eq_right hrefresh]
            apply hdiff _ _ rfl rfl hS
              (freyaDifferenceInitialSafe hm q.S hS _ _ _ _ _ τ)
            dsimp only
            omega
      have hinit : Safe (initial q seed) := by
        have hp : (initial q seed).phase=Phase.full true
            (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
          delta initial
          dsimp only
          rw [ite_eq_right (by omega)]
        have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels q.x0 0 (seed.1 0) 0 τ
        exact hfull _ true _ hp (List.length_ofFn) hf.1 hf.2.1 hf.2.2 (Nat.zero_le _)
      intro k
      induction k with
      | zero => exact hinit
      | succ k ih =>
        let s := trace q O seed ω k
        change Safe s at ih
        change Safe (update q s (replyAt q O seed ω k (query q s)))
        cases hs : s.phase with
        | halted =>
          have hu : update q s (replyAt q O seed ω k (query q s))=s := by delta update; rw [hs]
          rw [hu]
          exact ih
        | full first c =>
          obtain ⟨hlen,hne,hb,hl⟩ := ih.1 first c hs
          have hquery := freyaPageFullQuery q s first c hs
          rw [hquery]
          let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
          have ht := freyaFullSafeUpdate c hne hb f τ (fun r => replyAt q O seed ω k (0,r)) hl (hservice k).2
          change t.original=c.original ∧ _ at ht
          delta update
          rw [hs]
          dsimp only
          change Safe (if t.remaining.isEmpty then advance q _ else _)
          by_cases he : t.remaining.isEmpty=true
          · rw [ite_eq_left he]
            apply hadvance
            exact ih.2.2
          · rw [ite_eq_right he]
            have htne : t.remaining≠[] := by intro hz; apply he; rw [hz]; rfl
            exact hfull _ first t rfl (ht.1 ▸ hlen) htne ht.2.1 (ht.2.2 htne) ih.2.2
        | difference c =>
          obtain ⟨htarget,hcount,hp⟩ := ih.2.1 c hs
          have hquery := freyaPageDifferenceQuery q s c hs
          rw [hquery]
          obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,hpn⟩ :=
            freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hp
          delta update
          rw [hs]
          dsimp only
          rw [ht]
          dsimp only
          by_cases he : c.target≤c.count+1
          · rw [ite_eq_left he]
            apply hadvance
            exact ih.2.2
          · rw [ite_eq_right he]
            refine hdiff _ _ rfl ?_ ?_ ?_ ?_
            · exact htarget
            · change c.count+1<c.target
              omega
            · exact hpn
            · exact ih.2.2
    have freyaPageRemainingEvents (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
        ∀ k c,(trace q O seed ω k).phase=Phase.difference c →
          k+(c.target-c.count)≤eventLimit q := by
      clear * - q hm hn hS hK f τ O seed ω hservice freyaPageHaltedUpdate freyaDifferenceLiveStep freyaPageDifferenceQuery freyaFullPotentialDecrease freyaFullSafeUpdate freyaFullInitialPotential freyaPageFullQuery freyaPagePhaseSafety

      classical
      let M := max (q.n*q.m) q.S
      let fullV := fun c : FullState q.d q.m q.n =>
        if c.remaining=[] then 0 else q.n*(c.remaining.length+1)-
          (Finset.univ.filter fun i => ∃ job,c.pending i=some job ∧
            ∃ b ∈ c.remaining,c.original[b]?=some job.component).card
      let R : State q → ℕ := fun s => s.phase.casesOn
        (fun _ c => (rounds q-s.iteration)*M+fullV c)
        (fun c => (rounds q-s.iteration)*M+(c.target-c.count)) 0
      have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
        intro he
        have hh := congrArg List.length he
        simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
        omega
      have hinitV (x : Space q.d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ) :
          fullV (fullInitial q.n (List.ofFn id) x clock rows firstID)≤q.n*q.m := by
        have hh := freyaFullInitialPotential (n:=q.n) (List.ofFn id) hlabels x clock rows firstID
        dsimp only [fullV,fullInitial] at hh ⊢
        simpa (config := { iota := false }) only [List.length_ofFn] using hh
      have hadvance (s : State q) (hi : s.iteration≤rounds q) :
          R (advance q s)≤(rounds q-s.iteration)*M := by
        delta advance
        split
        · exact Nat.zero_le _
        · rename_i hlt
          dsimp only
          by_cases hrefresh : refreshAt s.seed s.iteration=true
          · rw [ite_eq_left hrefresh]
            change (rounds q-(s.iteration+1))*M+
              fullV (fullInitial q.n (List.ofFn id) (s.x-q.η • s.g) s.clock
                (s.seed.1 (s.iteration+1)) s.nextID)≤(rounds q-s.iteration)*M
            have hb := (hinitV (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID).trans
              (le_max_left (q.n*q.m) q.S)
            have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
            rw [hsub,Nat.add_mul,Nat.one_mul]
            simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
          · rw [ite_eq_right hrefresh]
            change (rounds q-(s.iteration+1))*M+(q.S-0)≤(rounds q-s.iteration)*M
            have hb : q.S≤M := le_max_right _ _
            have hsub : rounds q-s.iteration=(rounds q-(s.iteration+1))+1 := by omega
            rw [hsub,Nat.add_mul,Nat.one_mul]
            simpa (config := { iota := false }) only [Nat.sub_zero] using Nat.add_le_add_left hb ((rounds q-(s.iteration+1))*M)
      have hsafe := freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice
      have hdec (k : ℕ) (ha : active (trace q O seed ω k)=true) :
          R (trace q O seed ω (k+1))+1≤R (trace q O seed ω k) := by
        let s := trace q O seed ω k
        have hi := hsafe k
        change R (update q s (replyAt q O seed ω k (query q s)))+1≤R s
        cases hs : s.phase with
        | halted =>
          change active s=true at ha
          delta active at ha
          rw [hs] at ha
          contradiction
        | full first c =>
          obtain ⟨_,hne,hbound,hlegal⟩ := hi.1 first c hs
          have hquery := freyaPageFullQuery q s first c hs
          rw [hquery]
          let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
          have ht := freyaFullSafeUpdate c hne hbound f τ
            (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
          change t.original=c.original ∧ _ at ht
          have hd := freyaFullPotentialDecrease hn c.original c rfl hne hbound f τ
            (fun r => replyAt q O seed ω k (0,r)) hlegal (hservice k).2
          have hV : fullV t+1≤fullV c := by
            dsimp only [fullV]
            rw [ht.1]
            exact hd
          delta update
          rw [hs]
          dsimp only
          change R (if t.remaining.isEmpty then advance q _ else _)+1≤R s
          by_cases he : t.remaining.isEmpty=true
          · rw [ite_eq_left he]
            have hb := hadvance
              {s with clock:=t.clock,nextID:=t.nextID,phase:=Phase.full first t,g:=fullResult t} hi.2.2
            change _≤(rounds q-s.iteration)*M at hb
            have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
            rw [hr]
            change R (advance q {s with
              clock:=t.clock
              nextID:=t.nextID
              phase:=Phase.full first t
              g:=fullResult t})+1≤(rounds q-s.iteration)*M+fullV c
            exact (Nat.add_le_add_right hb 1).trans
              (Nat.add_le_add_left ((Nat.succ_le_succ (Nat.zero_le _)).trans hV) _)
          · rw [ite_eq_right he]
            have hr : R s=(rounds q-s.iteration)*M+fullV c := by dsimp only [R]; rw [hs]
            rw [hr]
            change (rounds q-s.iteration)*M+fullV t+1≤_
            simpa (config := { iota := false }) only [Nat.add_assoc] using Nat.add_le_add_left hV ((rounds q-s.iteration)*M)
        | difference c =>
          obtain ⟨_,hcount,hpending⟩ := hi.2.1 c hs
          have hquery := freyaPageDifferenceQuery q s c hs
          rw [hquery]
          obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,_⟩ := freyaDifferenceLiveStep hm hn c f τ
            (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hpending
          have hr : R s=(rounds q-s.iteration)*M+(c.target-c.count) := by dsimp only [R]; rw [hs]
          rw [hr]
          delta update
          rw [hs]
          dsimp only
          rw [ht]
          dsimp only
          by_cases he : c.target≤c.count+1
          · rw [ite_eq_left he]
            let t : DifferenceState q.d q.m q.n :=
              {c with
                count:=c.count+1
                sum:=c.sum+jobValue f job
                pending:=Function.update c.pending i (some next)
                clock:=time
                nextID:=c.nextID+1}
            have hb := hadvance {s with
              clock:=time
              nextID:=c.nextID+1
              phase:=Phase.difference t
              g:=s.g+differenceResult t} hi.2.2
            change R (advance q {s with
              clock:=time
              nextID:=c.nextID+1
              phase:=Phase.difference t
              g:=s.g+differenceResult t})+1≤_
            apply (Nat.add_le_add_right hb 1).trans
            change (rounds q-s.iteration)*M+1≤_
            omega
          · rw [ite_eq_right he]
            change (rounds q-s.iteration)*M+(c.target-(c.count+1))+1≤_
            omega
      have hbound : ∀ k,active (trace q O seed ω k)=true →
          k+R (trace q O seed ω k)≤R (initial q seed) := by
        intro k
        induction k with
        | zero =>
          intro _
          have ht : trace q O seed ω 0=initial q seed := by rfl'
          rw [ht,Nat.zero_add]
        | succ k ih =>
          intro ha
          have hprev : active (trace q O seed ω k)=true := by
            by_contra he
            have hf : active (trace q O seed ω k)=false := Bool.eq_false_of_not_eq_true he
            have hh := freyaPageHaltedUpdate q (trace q O seed ω k)
              (replyAt q O seed ω k (query q (trace q O seed ω k))) hf
            change trace q O seed ω (k+1)=trace q O seed ω k at hh
            rw [hh,hf] at ha
            contradiction
          have hd := hdec k hprev
          have hb := ih hprev
          have calcBound (k next current total : ℕ) (hd : next+1≤current) (hb : k+current≤total) :
              k+1+next≤total := by omega
          exact calcBound k _ _ _ hd hb
      have hrounds : rounds q≤q.K := by delta rounds; split <;> omega
      have hinitBound : R (initial q seed)≤eventLimit q := by
        have hp : (initial q seed).phase=Phase.full true
            (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
          delta initial
          dsimp only
          rw [ite_eq_right (by omega)]
        dsimp only [R]
        rw [hp]
        change (rounds q-0)*M+fullV (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))≤_
        have hv := hinitV q.x0 0 (seed.1 0) 0
        have hm := Nat.mul_le_mul_right M hrounds
        change _≤q.n*q.m+q.K*M
        rw [Nat.sub_zero]
        omega
      intro k c hc
      have ha : active (trace q O seed ω k)=true := by delta active; rw [hc]
      have hb := (hbound k ha).trans hinitBound
      dsimp only [R] at hb
      rw [hc] at hb
      dsimp only at hb
      omega
    have freyaScheduleFoldSome {α β : Type} (step : Option β → α → Option β)
        (hstep : ∀ v a, ∃ b, step v a = some b) (l : List α) (hne : l ≠ []) :
        ∀ v, ∃ b, l.foldl step v = some b := by
      clear * - α β step hstep l hne

      induction l with
      | nil => exact (hne rfl).elim
      | cons a l ih =>
        intro v
        cases l with
        | nil => exact hstep v a
        | cons b l => exact ih (List.cons_ne_nil _ _) (step v a)
    have freyaScheduleWorkerExists {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (call : ℕ) (s : ScheduleState n) : ∃ i, scheduleWorker γ call s = some i := by
      clear * - n hn γ call s freyaScheduleFoldSome

      classical
      delta scheduleWorker
      apply freyaScheduleFoldSome
      · intro v i
        cases v with
        | none => exact ⟨i,rfl⟩
        | some b =>
          dsimp only
          split
          · exact ⟨i,rfl⟩
          · exact ⟨b,rfl⟩
      · intro he
        have hlen : (List.finRange n).length = n := List.length_finRange
        rw [he,List.length_nil] at hlen
        omega
    have freyaScheduleStep {n : ℕ} (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) :
        let s := scheduleTrace γ firstID callStart clock k
        scheduleTrace γ firstID callStart clock (k+1) =
          Option.casesOn (scheduleWorker γ (callStart+k) s) s (fun i =>
            ⟨Function.update s.jobs i (s.nextID,(s.jobs i).2+γ.duration i (s.jobs i).1),s.nextID+1⟩) := by
      clear * - n γ firstID callStart clock k

      cases k <;> rfl'
    have freyaScheduleNextID {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) :
        (scheduleTrace γ firstID callStart clock k).nextID = firstID+n+k := by
      clear * - n hn γ firstID callStart clock k freyaScheduleWorkerExists freyaScheduleStep

      induction k with
      | zero => change firstID+n=firstID+n+0; omega
      | succ k ih =>
        obtain ⟨i,hi⟩ := freyaScheduleWorkerExists hn γ (callStart+k) (scheduleTrace γ firstID callStart clock k)
        let s := scheduleTrace γ firstID callStart clock k
        change scheduleWorker γ (callStart+k) s = some i at hi
        rw [freyaScheduleStep]
        rw [hi]
        change (scheduleTrace γ firstID callStart clock k).nextID+1 = _
        rw [ih]
        omega
    have freyaScheduleIDs {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) :
        let s := scheduleTrace γ firstID callStart clock k
        (∀ i, (s.jobs i).1 < s.nextID) ∧
          Function.Injective (fun i => (s.jobs i).1) ∧
          (∀ r < k, selectedJobID γ firstID callStart clock r < s.nextID) ∧
          ∀ r < k, ∀ i, selectedJobID γ firstID callStart clock r ≠ (s.jobs i).1 := by
      clear * - n hn γ firstID callStart clock k freyaScheduleWorkerExists freyaScheduleStep

      classical
      induction k with
      | zero =>
        refine ⟨?_,?_,?_,?_⟩
        · intro i
          change firstID+i.val < firstID+n
          have h := i.isLt
          omega
        · intro i l h
          apply Fin.ext
          change firstID+i.val=firstID+l.val at h
          omega
        · intro r hr; omega
        · intro r hr; omega
      | succ k ih =>
        let s := scheduleTrace γ firstID callStart clock k
        obtain ⟨i,hi⟩ := freyaScheduleWorkerExists hn γ (callStart+k) s
        let t : ScheduleState n :=
          ⟨Function.update s.jobs i (s.nextID,(s.jobs i).2+γ.duration i (s.jobs i).1),s.nextID+1⟩
        have hstate : scheduleTrace γ firstID callStart clock (k+1) = t := by
          rw [freyaScheduleStep]
          rw [hi]
        have hselected : selectedJobID γ firstID callStart clock k = (s.jobs i).1 := by
          delta selectedJobID
          change ((scheduleWorker γ (callStart+k) s).map (fun i => (s.jobs i).1)).getD 0 = _
          rw [hi]
          rfl
        dsimp only at ih ⊢
        rw [hstate]
        change (∀ l, (t.jobs l).1<t.nextID) ∧ Function.Injective (fun l => (t.jobs l).1) ∧ _
        refine ⟨?_,?_,?_,?_⟩
        · intro l
          dsimp only [t]
          by_cases hl : l=i
          · subst l
            rw [Function.update_self]
            exact Nat.lt_succ_self _
          · rw [Function.update_of_ne hl]
            exact (ih.1 l).trans (Nat.lt_succ_self _)
        · intro l l' h
          dsimp only [t] at h
          by_cases hl : l=i
          · subst l
            rw [Function.update_self] at h
            by_cases hl' : l'=i
            · exact hl'.symm
            · rw [Function.update_of_ne hl'] at h
              have hb := ih.1 l'
              change (s.jobs l').1<s.nextID at hb
              change s.nextID=(s.jobs l').1 at h
              omega
          · rw [Function.update_of_ne hl] at h
            by_cases hl' : l'=i
            · subst l'
              rw [Function.update_self] at h
              have hb := ih.1 l
              change (s.jobs l).1<s.nextID at hb
              change (s.jobs l).1=s.nextID at h
              omega
            · rw [Function.update_of_ne hl'] at h
              exact ih.2.1 h
        · intro r hr
          change selectedJobID γ firstID callStart clock r < s.nextID+1
          by_cases hrk : r=k
          · subst r
            rw [hselected]
            exact (ih.1 i).trans (Nat.lt_succ_self _)
          · exact (ih.2.2.1 r (by omega)).trans (Nat.lt_succ_self _)
        · intro r hr l
          dsimp only [t]
          by_cases hl : l=i
          · subst l
            rw [Function.update_self]
            by_cases hrk : r=k
            · subst r
              rw [hselected]
              exact (ih.1 i).ne
            · exact (ih.2.2.1 r (by omega)).ne
          · rw [Function.update_of_ne hl]
            by_cases hrk : r=k
            · subst r
              rw [hselected]
              exact fun h => hl (ih.2.1 h).symm
            · exact ih.2.2.2 r (by omega) l
    have freyaScheduleInjective {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) :
        Function.Injective (selectedJobID γ firstID callStart clock) := by
      clear * - n hn γ firstID callStart clock freyaScheduleWorkerExists freyaScheduleIDs

      intro r s h
      have hne (a b : ℕ) (hab : a<b) :
          selectedJobID γ firstID callStart clock a ≠ selectedJobID γ firstID callStart clock b := by
        obtain ⟨i,hi⟩ := freyaScheduleWorkerExists hn γ (callStart+b) (scheduleTrace γ firstID callStart clock b)
        have hh := (freyaScheduleIDs hn γ firstID callStart clock b).2.2.2 a hab i
        delta selectedJobID
        dsimp only
        rw [hi]
        exact hh
      rcases lt_trichotomy r s with hrs | hrs | hrs
      · exact (hne r s hrs h).elim
      · exact hrs
      · exact (hne s r hrs h.symm).elim
    have freyaScheduleFoldWinner {α : Type} (step : Option α → α → Option α) (winner : α)
        (hkeep : ∀ a, step (some winner) a = some winner)
        (hselect : ∀ v, step v winner = some winner) (l : List α) :
        ∀ v, v = some winner ∨ winner ∈ l → l.foldl step v = some winner := by
      clear * - α step winner hkeep hselect l

      induction l with
      | nil => intro v hv; exact hv.resolve_right (List.not_mem_nil)
      | cons a l ih =>
        intro v hv
        change l.foldl step (step v a) = _
        apply ih
        rcases hv with hv | hv
        · rw [hv,hkeep]
          exact Or.inl rfl
        · rcases List.mem_cons.mp hv with ha | hl
          · subst a
            exact Or.inl (hselect v)
          · exact Or.inr hl
    have freyaScheduleWorkerCharacterization {n : ℕ} (γ : BatchSchedule n)
        (call : ℕ) (s : ScheduleState n) (winner : Fin n)
        (hmin : ∀ i, (s.jobs winner).2+γ.duration winner (s.jobs winner).1 ≤
          (s.jobs i).2+γ.duration i (s.jobs i).1)
        (htie : ∀ i, (s.jobs winner).2+γ.duration winner (s.jobs winner).1 =
            (s.jobs i).2+γ.duration i (s.jobs i).1 →
          γ.priority call winner < γ.priority call i ∨
            (γ.priority call winner = γ.priority call i ∧ winner.val ≤ i.val)) :
        scheduleWorker γ call s = some winner := by
      clear * - n γ call s winner hmin htie freyaScheduleFoldWinner

      classical
      let finish := fun i => (s.jobs i).2+γ.duration i (s.jobs i).1
      let wins := fun i b => finish i < finish b ∨ (finish i = finish b ∧
        (γ.priority call i < γ.priority call b ∨
          (γ.priority call i = γ.priority call b ∧ i.val ≤ b.val)))
      let step := fun (v : Option (Fin n)) (i : Fin n) =>
        v.elim (some i) (fun b => if wins i b then some i else some b)
      have hwin (i : Fin n) : wins winner i := by
        rcases lt_or_eq_of_le (hmin i) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h,htie i h⟩
      have hnot (i : Fin n) (hi : i ≠ winner) : ¬ wins i winner := by
        intro h
        rcases h with h | ⟨he,hp⟩
        · exact (not_lt_of_ge (hmin i)) h
        · have hw := htie i he.symm
          have hval : i.val ≠ winner.val := fun h => hi (Fin.ext h)
          rcases hp with hp | ⟨hp,hv⟩ <;> rcases hw with hw | ⟨hw,hvw⟩ <;> omega
      have hkeep (i : Fin n) : step (some winner) i = some winner := by
        dsimp only [step,Option.elim_some]
        by_cases hi : i=winner
        · subst i
          exact ite_self _
        · rw [ite_eq_right (hnot i hi)]
      have hselect (v : Option (Fin n)) : step v winner = some winner := by
        cases v with
        | none => rfl
        | some i =>
          dsimp only [step,Option.elim_some]
          rw [ite_eq_left (hwin i)]
      have hfold := freyaScheduleFoldWinner step winner hkeep hselect (List.finRange n) none
        (Or.inr (List.mem_finRange winner))
      delta scheduleWorker
      dsimp only
      convert hfold using 1
      apply congrArg (fun g => (List.finRange n).foldl g none)
      funext v i
      cases v <;> rfl
    have freyaPageScheduleWorker (q : Raw)
        (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (γ : BatchSchedule q.n) (hγ : ScheduleRealization q f τ O seed ω batch γ)
        (hc : call≤eventLimit q) (hi : (trace q O seed ω call).iteration=batch)
        (c : DifferenceState q.d q.m q.n)
        (hphase : (trace q O seed ω call).phase=Phase.difference c)
        (ss : ScheduleState q.n)
        (hpending : ∀ i,∃ job,c.pending i=some job)
        (hmap : ∀ i job,c.pending i=some job → ss.jobs i=(job.id,(job.started : ℝ≥0∞)))
        (hquery : differenceQuery c=some ⟨c.clock,c.pending⟩)
        (i : Fin q.n) (job : Job q.d q.m) (time : ℝ≥0)
        (hjob : c.pending i=some job)
        (hreply : replyAt q O seed ω call (0,differenceQuery c)=some (i,job.id,time,jobValue f job)) :
        scheduleWorker γ call ss=some i ∧
          (time : ℝ≥0∞)=(ss.jobs i).2+γ.duration i (ss.jobs i).1 := by
      clear * - q f τ O seed ω batch call γ hγ hc hi c hphase ss hpending hmap hquery i job time hjob hreply freyaPageDifferenceQuery freyaScheduleWorkerCharacterization

      have hqueryPage := freyaPageDifferenceQuery q _ c hphase
      have hrequest : (query q (trace q O seed ω call)).2=some ⟨c.clock,c.pending⟩ := by
        rw [hqueryPage]
        exact hquery
      obtain ⟨iw,jw,cw,hjw,hrw,_,htime,hall⟩ := (hγ call hc hi).2 _ hrequest
      rw [hqueryPage,hreply] at hrw
      have heq := Option.some.inj hrw
      simp (config := { iota := false }) only [Prod.mk.injEq] at heq
      obtain ⟨hei,_,het,_⟩ := heq
      subst iw
      subst cw
      change c.pending i=some jw at hjw
      have hej : jw=job := Option.some.inj (hjw.symm.trans hjob)
      subst jw
      refine ⟨?_,?_⟩
      · apply freyaScheduleWorkerCharacterization γ call ss i
        · intro k
          obtain ⟨old,hold⟩ := hpending k
          rw [hmap i job hjob,hmap k old hold]
          dsimp only
          rw [← htime]
          exact (hall k old hold).2.1
        · intro k he
          obtain ⟨old,hold⟩ := hpending k
          rw [hmap i job hjob,hmap k old hold] at he
          dsimp only at he
          apply (hall k old hold).2.2
          exact htime.trans he
      · rw [hmap i job hjob]
        exact htime
    have freyaPageScheduleCoupling (q : Raw) (hm : 0<q.m) (hn : 0<q.n) (hS : 0<q.S)
        (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (batch firstID call : ℕ) (x y : Space q.d) (clock : ℝ≥0)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hphase : (trace q O seed ω call).phase=Phase.difference
          (differenceInitial q.n q.S x y clock (seed.1 batch) firstID))
        (hlimit : call+q.S≤eventLimit q)
        (γ : BatchSchedule q.n) (hγ : ScheduleRealization q f τ O seed ω batch γ) :
        ∀ a,a<q.S → ∀ c,(trace q O seed ω (call+a)).phase=Phase.difference c →
          ∀ i job,c.pending i=some job →
            (scheduleTrace γ firstID call clock a).jobs i=(job.id,(job.started : ℝ≥0∞)) := by
      clear * - q hm hn hS f τ O seed ω hservice batch firstID call x y clock hstart hphase hlimit γ hγ freyaDifferenceLiveStep freyaPageDifferenceQuery freyaPageDifferenceContinue freyaPageBatchProgress freyaScheduleStep freyaScheduleNextID freyaPageScheduleWorker

      classical
      intro a
      induction a with
      | zero =>
        intro _ c hc i job hj
        rw [Nat.add_zero,hphase] at hc
        have heq := Phase.difference.inj hc
        subst c
        change (if q.S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
          (labelAt (seed.1 batch (firstID+i.val)) q.m))=some job at hj
        rw [ite_eq_right (by omega)] at hj
        delta dispatch at hj
        obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
        cases heq
        rfl'
      | succ a ih =>
        intro ha c' hc' k old hold
        have haS : a<q.S := by omega
        obtain ⟨c,hc,hit,htarget,hcount,hx,hy,_,hid,_,hpending⟩ :=
          freyaPageBatchProgress q hm hn hS f τ O seed ω hservice batch firstID call x y clock
            hstart hphase a haS
        have hp : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
          intro i
          obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
          rw [hx,hy]
          exact ⟨job,hj,hs,ht,hk⟩
        obtain ⟨i,job,time,next,hjob,hquery,hreply,_,hnid,_,hnstart,_,ht,_⟩ :=
          freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω (call+a) (0,r))
            (hservice (call+a)).2 (by omega) hp
        have hmap := ih haS c hc
        obtain ⟨hw,htime⟩ := freyaPageScheduleWorker q f τ O seed ω batch (call+a) γ hγ
          (by omega) hit c hc (scheduleTrace γ firstID call clock a)
          (fun i => by obtain ⟨job,hj,_⟩ := hpending i; exact ⟨job,hj⟩)
          hmap hquery i job time hjob hreply
        let t := differenceUpdate c (replyAt q O seed ω (call+a) (0,differenceQuery c))
        have hta : t.count<t.target := by dsimp only [t]; rw [ht]; dsimp only; omega
        have htphase : (trace q O seed ω (call+(a+1))).phase=Phase.difference t := by
          rw [← Nat.add_assoc]
          change (update q (trace q O seed ω (call+a)) (replyAt q O seed ω (call+a) (query q (trace q O seed ω (call+a))))).phase=_
          rw [freyaPageDifferenceQuery q _ c hc]
          exact (freyaPageDifferenceContinue q _ c _ hc hta).1
        have heq : c'=t := Phase.difference.inj (hc'.symm.trans htphase)
        subst c'
        change t.pending k=some old at hold
        change differenceUpdate c _ = _ at ht
        dsimp only [t] at hold
        rw [ht] at hold
        change Function.update c.pending i (some next) k=some old at hold
        rw [freyaScheduleStep,hw]
        dsimp only
        by_cases hk : k=i
        · subst k
          rw [Function.update_self] at hold ⊢
          have heq : next=old := Option.some.inj hold
          subst old
          apply Prod.ext
          · dsimp only
            rw [hnid,hid,freyaScheduleNextID hn]
          · dsimp only
            rw [hnstart]
            exact htime.symm
        · rw [Function.update_of_ne hk] at hold ⊢
          exact hmap k old hold
    have freyaPageScheduleSelectionActual (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
        (hinvoke : invocation q O seed ω batch=some (false,x,y,clock,firstID))
        (γ : BatchSchedule q.n) (hγ : ScheduleRealization q f τ O seed ω batch γ) :
        let callStart := (batchStartCall q O seed ω batch).getD 0
        Function.Injective (fun j : Fin q.S => selectedJobID γ firstID callStart clock j.val) ∧
          (∀ j : Fin q.S,(completedJob q O seed ω batch j).map (fun job => job.id)=
            some (selectedJobID γ firstID callStart clock j.val)) ∧
          ∀ j : Fin q.S,completedLabels q O seed ω batch j=
            batchLabels q seed batch (selectedJobID γ firstID callStart clock j.val) := by
      clear * - q hm hn hS hK f τ O seed ω hservice batch firstID x y clock hinvoke γ hγ freyaPageFreshDifference freyaDifferenceLiveStep freyaPageCompletedJobEq freyaPageBatchProgress freyaPageRemainingEvents freyaScheduleInjective freyaPageScheduleWorker freyaPageScheduleCoupling

      classical
      obtain ⟨call,hstart,hphase⟩ := freyaPageFreshDifference q O seed ω batch firstID x y clock hinvoke
      have hlimit := freyaPageRemainingEvents q hm hn hS hK f τ O seed ω hservice call _ hphase
      change call+(q.S-0)≤eventLimit q at hlimit
      rw [Nat.sub_zero] at hlimit
      dsimp only
      rw [hstart]
      dsimp only [Option.getD]
      have hclaims : ∀ j : Fin q.S,
          (completedJob q O seed ω batch j).map (fun job => job.id)=some (selectedJobID γ firstID call clock j.val) ∧
          completedLabels q O seed ω batch j=batchLabels q seed batch (selectedJobID γ firstID call clock j.val) := by
        intro j
        obtain ⟨c,hc,hit,htarget,hcount,hx,hy,_,_,_,hpending⟩ :=
          freyaPageBatchProgress q hm hn hS f τ O seed ω hservice batch firstID call x y clock
            hstart hphase j.val j.isLt
        have hp : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
          intro i
          obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
          rw [hx,hy]
          exact ⟨job,hj,hs,ht,hk⟩
        obtain ⟨i,job,time,next,hjob,hquery,hreply,_,_,_,_,_,_,_⟩ :=
          freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω (call+j.val) (0,r))
            (hservice (call+j.val)).2 (by omega) hp
        have hmap := freyaPageScheduleCoupling q hm hn hS f τ O seed ω hservice
          batch firstID call x y clock hstart hphase hlimit γ hγ j.val j.isLt c hc
        obtain ⟨hw,_⟩ := freyaPageScheduleWorker q f τ O seed ω batch (call+j.val) γ hγ
          (by omega) hit c hc (scheduleTrace γ firstID call clock j.val)
          (fun i => by obtain ⟨job,hj,_⟩ := hpending i; exact ⟨job,hj⟩)
          hmap hquery i job time hjob hreply
        have hselected : selectedJobID γ firstID call clock j.val=job.id := by
          delta selectedJobID
          dsimp only
          rw [hw]
          exact congrArg Prod.fst (hmap i job hjob)
        have hcompleted := freyaPageCompletedJobEq q O seed ω batch call j hstart c hc hquery
          i job time (jobValue f job) hjob hreply
        obtain ⟨old,hold,_,_,_,hlabel⟩ := hpending i
        have heq : old=job := Option.some.inj (hold.symm.trans hjob)
        subst old
        constructor
        · rw [hcompleted,hselected]
          rfl
        · delta completedLabels
          rw [hcompleted,hselected,hlabel]
          rfl
      refine ⟨?_,fun j => (hclaims j).1,fun j => (hclaims j).2⟩
      intro i j h
      apply Fin.ext
      exact freyaScheduleInjective hn γ firstID call clock h
    exact freyaPageScheduleSelectionActual q hm hn hS hK f τ O seed ω hservice batch firstID x y clock hinvoke γ hγ


theorem completed_labels_iid (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (batch : ℕ) :
    let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
    Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
      completedLabels q O z.1 z.2 batch) ∧
      (∀ᵐ z ∂P, isDifferenceBatch q O z batch →
        ∀ j : Fin q.S, (completedLabels q O z.1 z.2 batch j).isSome) ∧
      ∀ E, MeasurableSet[historyBefore q O batch] E →
        (∀ z ∈ E, isDifferenceBatch q O z batch) → ∀ v : Fin q.S → Fin q.m,
        P (E ∩ {z | completedLabels q O z.1 z.2 batch = fun j => some (v j)}) =
          P E * ((q.m : ℝ≥0∞) ^ q.S)⁻¹ := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Setups.FreyaIndependence in
    classical
    have _ := hρ
    have _ := hρone
    have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
      delta advance
      split <;> rfl
    have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
        (update q s reply).seed = s.seed := by
      delta update
      cases hs : s.phase with
      | halted => rfl
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
    have freyaPageTraceSeed (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
        (trace q O seed ω k).seed = seed := by
      induction k with
      | zero => rfl
      | succ k ih =>
        change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
        rw [freyaPageUpdateSeed,ih]
    have freyaPageAdvanceIteration (q : Raw) (s : State q) :
        (advance q s).iteration = s.iteration ∨ (advance q s).iteration = s.iteration+1 := by
      delta advance
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    have freyaPageUpdateIteration (q : Raw) (s : State q) (reply : Reply q.d q.n) :
        (update q s reply).iteration = s.iteration ∨
          (update q s reply).iteration = s.iteration+1 := by
      delta update
      cases hs : s.phase with
      | halted => exact Or.inl rfl
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceIteration q _
        · exact Or.inl rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceIteration q _
        · exact Or.inl rfl
    have freyaPageIterationMonotone (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
        Monotone (fun k => (trace q O seed ω k).iteration) := by
      apply monotone_nat_of_le_succ
      intro k
      have h := freyaPageUpdateIteration q (trace q O seed ω k)
        (replyAt q O seed ω k (query q (trace q O seed ω k)))
      change (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration ∨
        (trace q O seed ω (k+1)).iteration = (trace q O seed ω k).iteration+1 at h
      omega
    have freyaPageHaltedUpdate (q : Raw) (s : State q) (reply : Reply q.d q.n)
        (h : active s = false) : update q s reply = s := by
      cases hs : s.phase with
      | halted => delta update; rw [hs]
      | full first c =>
        delta active at h
        rw [hs] at h
        contradiction
      | difference c =>
        delta active at h
        rw [hs] at h
        contradiction
    have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
        (h : (List.range N).find? p = some k) :
        k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
      obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
      simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
      subst i
      refine ⟨hi,hp,?_⟩
      intro r hr htrue
      have hh := hprev r hr
      rw [htrue] at hh
      contradiction
    have freyaPageBatchStartFacts (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (h : batchStartCall q O seed ω batch = some call) :
        call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
          active (trace q O seed ω call) = true ∧
          ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
      delta batchStartCall at h
      obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
      obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
      refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
      intro r hr hh
      apply hprev r hr
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
    have freyaPageAdvanceSeedCongruence (q : Raw) (s : State q) (new : Seed q.K)
        (batch : ℕ) (hbits : new.2=s.seed.2)
        (hrows : ∀ i,i<batch → new.1 i=s.seed.1 i)
        (hbound : (advance q s).iteration<batch) :
        advance q {s with seed:=new}={advance q s with seed:=new} := by
      delta advance at hbound ⊢
      dsimp only
      by_cases hstop : rounds q≤s.iteration
      · simp (config := { iota := false }) only [ite_eq_left hstop]
      · simp (config := { iota := false }) only [ite_eq_right hstop] at hbound ⊢
        have hr : refreshAt new s.iteration=refreshAt s.seed s.iteration :=
          congrArg (fun t => t.1 s.iteration) hbits
        have ho : outputIndex new=outputIndex s.seed := congrArg Prod.snd hbits
        simp (config := { iota := false }) only [hr,ho,hrows (s.iteration+1) hbound]
    have freyaPageUpdateSeedCongruence (q : Raw) (s : State q) (new : Seed q.K)
        (reply : Reply q.d q.n) (batch : ℕ) (hbits : new.2=s.seed.2)
        (hrows : ∀ i,i<batch → new.1 i=s.seed.1 i)
        (hbound : (update q s reply).iteration<batch) :
        update q {s with seed:=new} reply={update q s reply with seed:=new} := by
      delta update at hbound ⊢
      cases hs : s.phase with
      | halted => dsimp only; simp (config := { iota := false }) only [hs]
      | full first c =>
        rw [hs] at hbound
        dsimp only at hbound ⊢
        by_cases he : (fullUpdate c reply).remaining.isEmpty=true
        · simp (config := { iota := false }) only [ite_eq_left he] at hbound ⊢
          exact freyaPageAdvanceSeedCongruence q {s with
            g:=fullResult (fullUpdate c reply)
            clock:=(fullUpdate c reply).clock
            nextID:=(fullUpdate c reply).nextID
            phase:=Phase.full first (fullUpdate c reply)} new batch hbits hrows hbound
        · simp (config := { iota := false }) only [ite_eq_right he]
      | difference c =>
        rw [hs] at hbound
        dsimp only at hbound ⊢
        by_cases he : (differenceUpdate c reply).target≤(differenceUpdate c reply).count
        · simp (config := { iota := false }) only [ite_eq_left he] at hbound ⊢
          exact freyaPageAdvanceSeedCongruence q {s with
            g:=s.g+differenceResult (differenceUpdate c reply)
            clock:=(differenceUpdate c reply).clock
            nextID:=(differenceUpdate c reply).nextID
            phase:=Phase.difference (differenceUpdate c reply)} new batch hbits hrows hbound
        · simp (config := { iota := false }) only [ite_eq_right he]
    have freyaPageInitialSeedCongruence (q : Raw) (seed new : Seed q.K)
        (hrows : new.1 0=seed.1 0) :
        initial q new={initial q seed with seed:=new} := by
      delta initial
      rw [hrows]
    have freyaPageSeedQuery (q : Raw) (s : State q) (new : Seed q.K) :
        query q {s with seed:=new}=query q s := by rfl
    have freyaPageSeedPendingAfter (q : Raw) (s : State q) (new : Seed q.K)
        (reply : Reply q.d q.n) :
        collectorPendingAfter q {s with seed:=new} reply=collectorPendingAfter q s reply := by rfl
    have freyaPageEarlierActive (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (a b : ℕ) (hab : a≤b)
        (hb : active (trace q O seed ω b)=true) : active (trace q O seed ω a)=true := by
      by_contra h
      have ha : active (trace q O seed ω a)=false := Bool.eq_false_of_not_eq_true h
      have hs : ∀ k,a≤k → trace q O seed ω k=trace q O seed ω a := by
        intro k hk
        induction k,hk using Nat.le_induction with
        | base => rfl
        | succ k hk ih =>
          change update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))=_
          rw [ih]
          exact freyaPageHaltedUpdate q _ _ ha
      rw [hs b hab,ha] at hb
      contradiction
    have freyaPagePreBatchIteration (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call) :
        ∀ k,k<call → (trace q O seed ω k).iteration<batch := by
      obtain ⟨_,hit,hactive,hprev⟩ := freyaPageBatchStartFacts q O seed ω batch call hstart
      intro k hk
      have hle := freyaPageIterationMonotone q O seed ω (Nat.le_of_lt hk)
      dsimp only at hle
      rw [hit] at hle
      have hka := freyaPageEarlierActive q O seed ω k call (Nat.le_of_lt hk) hactive
      have hne : (trace q O seed ω k).iteration≠batch := by
        intro he
        exact hprev k hk ⟨he,hka⟩
      omega
    have freyaPageRunBeforeBatch (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        ∀ k,k<call → trace q O new ω k={trace q O seed ω k with seed:=new} ∧
          (run q O new ω k).2=(run q O seed ω k).2 := by
      have hpre := freyaPagePreBatchIteration q O seed ω batch call hstart
      intro k
      induction k with
      | zero =>
        intro hk
        have hb : 0<batch := hpre 0 hk
        have hleft : trace q O new ω 0=initial q new := by rfl'
        have hright : trace q O seed ω 0=initial q seed := by rfl'
        rw [hleft,hright]
        exact ⟨freyaPageInitialSeedCongruence q seed new (hrows 0 hb),rfl⟩
      | succ k ih =>
        intro hk
        have hkcall : k<call := by omega
        obtain ⟨hs,hh⟩ := ih hkcall
        have hseed := freyaPageTraceSeed q O seed ω k
        have hquery : query q (trace q O new ω k)=query q (trace q O seed ω k) := by
          rw [hs,freyaPageSeedQuery]
        have hreply : replyAt q O new ω k (query q (trace q O new ω k))=
            replyAt q O seed ω k (query q (trace q O seed ω k)) := by
          rw [hquery]
          show O.answer (run q O new ω k).2 _ (ω (run q O new ω k).2.length)=
            O.answer (run q O seed ω k).2 _ (ω (run q O seed ω k).2.length)
          rw [hh]
        refine ⟨?_,?_⟩
        · change update q (trace q O new ω k) (replyAt q O new ω k (query q (trace q O new ω k)))=_
          rw [hreply,hs]
          exact freyaPageUpdateSeedCongruence q _ new _ batch
            (by rw [hseed]; exact hbits) (by rw [hseed]; exact hrows) (hpre (k+1) hk)
        · change (run q O new ω k).2++[(query q (trace q O new ω k),
              replyAt q O new ω k (query q (trace q O new ω k)))]=
            (run q O seed ω k).2++[(query q (trace q O seed ω k),
              replyAt q O seed ω k (query q (trace q O seed ω k)))]
          rw [hreply,hh,hquery]
    have freyaPageTraceBeforeBatch (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        ∀ k,k<call → trace q O new ω k={trace q O seed ω k with seed:=new} :=
      fun k hk => (freyaPageRunBeforeBatch q O seed new ω batch call hstart hbits hrows k hk).1
    have freyaPageReplyBeforeBatch (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        ∀ k,k<call → ∀ x,replyAt q O new ω k x=replyAt q O seed ω k x := by
      intro k hk x
      show O.answer (run q O new ω k).2 x (ω (run q O new ω k).2.length)=
        O.answer (run q O seed ω k).2 x (ω (run q O seed ω k).2.length)
      rw [(freyaPageRunBeforeBatch q O seed new ω batch call hstart hbits hrows k hk).2]
    let freyaEntryView (q : Raw) (s : State q) :
        ℕ × Bool × Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) :=
      (s.iteration, active s, s.phase.casesOn
        (fun _ c => some (true,c.point,c.point,c.clock,c.nextID-q.n))
        (fun c => some (false,c.x,c.y,c.clock,c.nextID-q.n)) none)
    have freyaPageAdvanceEntry (q : Raw) (s : State q) (new : Seed q.K)
        (hbits : new.2=s.seed.2) :
        freyaEntryView q (advance q {s with seed:=new})=freyaEntryView q (advance q s) := by
      have hr : refreshAt new s.iteration=refreshAt s.seed s.iteration :=
        congrArg (fun t => t.1 s.iteration) hbits
      delta advance
      dsimp only
      by_cases hstop : rounds q≤s.iteration
      · simp (config := { iota := false }) only [ite_eq_left hstop]; rfl
      · simp (config := { iota := false }) only [ite_eq_right hstop,hr]
        cases refreshAt s.seed s.iteration <;> rfl
    have freyaPageUpdateEntry (q : Raw) (s : State q) (new : Seed q.K)
        (reply : Reply q.d q.n) (hbits : new.2=s.seed.2) :
        freyaEntryView q (update q {s with seed:=new} reply)=freyaEntryView q (update q s reply) := by
      delta update
      cases hs : s.phase with
      | halted => dsimp only [freyaEntryView,active]; rw [hs]
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceEntry q {s with
            g:=fullResult (fullUpdate c reply)
            clock:=(fullUpdate c reply).clock
            nextID:=(fullUpdate c reply).nextID
            phase:=Phase.full first (fullUpdate c reply)} new hbits
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceEntry q {s with
            g:=s.g+differenceResult (differenceUpdate c reply)
            clock:=(differenceUpdate c reply).clock
            nextID:=(differenceUpdate c reply).nextID
            phase:=Phase.difference (differenceUpdate c reply)} new hbits
        · rfl
    have freyaPageInitialEntry (q : Raw) (seed new : Seed q.K) :
        freyaEntryView q (initial q new)=freyaEntryView q (initial q seed) := by
      dsimp only [initial,freyaEntryView]
      by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
      · simp (config := { iota := false }) only [ite_eq_left hbad]; rfl
      · simp (config := { iota := false }) only [ite_eq_right hbad]; rfl
    have freyaPageBoundaryEntry (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        freyaEntryView q (trace q O new ω call)=freyaEntryView q (trace q O seed ω call) := by
      cases call with
      | zero => exact freyaPageInitialEntry q seed new
      | succ k =>
        have hs := freyaPageTraceBeforeBatch q O seed new ω batch (k+1) hstart hbits hrows k (by omega)
        change freyaEntryView q (update q (trace q O new ω k)
          (replyAt q O new ω k (query q (trace q O new ω k))))=_
        rw [freyaPageReplyBeforeBatch q O seed new ω batch (k+1) hstart hbits hrows k (by omega),
          hs,freyaPageSeedQuery]
        exact freyaPageUpdateEntry q _ new _ (by rw [freyaPageTraceSeed]; exact hbits)
    have freyaPageFirstMatchConverse (N : ℕ) (p : ℕ → Bool) (k : ℕ)
        (hk : k<N) (hp : p k=true) (hprev : ∀ r<k,p r≠true) :
        (List.range N).find? p=some k := by
      apply List.find?_eq_some_iff_getElem.mpr
      refine ⟨hp,k,by simpa (config := { iota := false }) only [List.length_range] using hk,?_,?_⟩
      · simp (config := { iota := false }) only [List.getElem_range]
      · intro j hj
        simp (config := { iota := false }) only [List.getElem_range,Bool.eq_false_of_not_eq_true (hprev j hj),Bool.not_false]
    have freyaPageBatchStartTransport (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (hstart : batchStartCall q O seed ω batch=some call)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        batchStartCall q O new ω batch=some call := by
      obtain ⟨hcall,hit,ha,hprev⟩ := freyaPageBatchStartFacts q O seed ω batch call hstart
      have he := freyaPageBoundaryEntry q O seed new ω batch call hstart hbits hrows
      have hi : (trace q O new ω call).iteration=batch := (congrArg Prod.fst he).trans hit
      have haa : active (trace q O new ω call)=true :=
        (congrArg (fun v => v.2.1) he).trans ha
      delta batchStartCall
      apply freyaPageFirstMatchConverse _ _ call (by omega)
      · exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hi,haa⟩
      · intro r hr ht
        have hs := freyaPageTraceBeforeBatch q O seed new ω batch call hstart hbits hrows r hr
        obtain ⟨hti,hta⟩ := Bool.and_eq_true_iff.mp ht
        apply hprev r hr
        rw [hs] at hti hta
        exact ⟨of_decide_eq_true hti,hta⟩
    have freyaPageBatchStartInvariant (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        batchStartCall q O new ω batch=batchStartCall q O seed ω batch := by
      cases hs : batchStartCall q O seed ω batch with
      | some call => exact freyaPageBatchStartTransport q O seed new ω batch call hs hbits hrows
      | none =>
        cases hn : batchStartCall q O new ω batch with
        | none => rfl
        | some call =>
          have hh := freyaPageBatchStartTransport q O new seed ω batch call hn hbits.symm
            (fun i hi => (hrows i hi).symm)
          rw [hs] at hh
          contradiction
    have freyaPageInvocationInvariant (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        invocation q O new ω batch=invocation q O seed ω batch := by
      have he := freyaPageBatchStartInvariant q O seed new ω batch hbits hrows
      delta invocation
      rw [he]
      cases hs : batchStartCall q O seed ω batch with
      | none => rfl
      | some call =>
        have hh := congrArg (fun v => v.2.2)
          (freyaPageBoundaryEntry q O seed new ω batch call hs hbits hrows)
        dsimp only [Option.bind]
        dsimp only [freyaEntryView] at hh
        generalize (trace q O new ω call).phase = pn at hh ⊢
        generalize (trace q O seed ω call).phase = ps at hh ⊢
        cases pn <;> cases ps <;> exact hh
    let freyaHistoryView (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :=
      (invocation q O z.1 z.2 batch, fun k : ℕ =>
        if k < (batchStartCall q O z.1 z.2 batch).getD 0 then
          let s := trace q O z.1 z.2 k
          let reply := replyAt q O z.1 z.2 k (query q s)
          some (query q s,reply,collectorPendingAfter q s reply)
        else none)
    have freyaPageHistoryInvariant (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i) :
        freyaHistoryView q O batch (new,ω)=freyaHistoryView q O batch (seed,ω) := by
      apply Prod.ext
      · exact freyaPageInvocationInvariant q O seed new ω batch hbits hrows
      · funext k
        have he := freyaPageBatchStartInvariant q O seed new ω batch hbits hrows
        dsimp only [freyaHistoryView]
        rw [he]
        cases hs : batchStartCall q O seed ω batch with
        | none => simp (config := { iota := false }) only [Option.getD_none,Nat.not_lt_zero,ite_false]
        | some call =>
          dsimp only [Option.getD]
          by_cases hk : k<call
          · simp (config := { iota := false }) only [ite_eq_left hk]
            have ht := freyaPageTraceBeforeBatch q O seed new ω batch call hs hbits hrows k hk
            rw [freyaPageReplyBeforeBatch q O seed new ω batch call hs hbits hrows k hk,
              ht,freyaPageSeedQuery,freyaPageSeedPendingAfter]
          · simp (config := { iota := false }) only [ite_eq_right hk]
    have freyaPageHistoryEventInvariant (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed new : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
        (hbits : new.2=seed.2) (hrows : ∀ i,i<batch → new.1 i=seed.1 i)
        (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
        (hE : MeasurableSet[historyBefore q O batch] E) :
        (new,ω)∈E ↔ (seed,ω)∈E := by
      change MeasurableSet[MeasurableSpace.comap (freyaHistoryView q O batch) inferInstance] E at hE
      obtain ⟨U,_,hU⟩ := hE
      rw [← hU]
      change freyaHistoryView q O batch (new,ω)∈U ↔ freyaHistoryView q O batch (seed,ω)∈U
      rw [freyaPageHistoryInvariant q O seed new ω batch hbits hrows]
    have freyaInfiniteResample {α : Type} [MeasurableSpace α]
        (μ : Measure α) [IsProbabilityMeasure μ] (i : ℕ) :
        MeasurePreserving (fun z : (ℕ → α) × α => Function.update z.1 i z.2)
          ((Measure.infinitePi fun _ : ℕ => μ).prod μ) (Measure.infinitePi fun _ : ℕ => μ) := by
      classical
      have hm : Measurable (fun z : (ℕ → α) × α => Function.update z.1 i z.2) := by
        apply Measurable.of_eval
        intro j
        by_cases hj : j=i
        · subst j
          simpa (config := { iota := false }) only [Function.update_self] using
            (measurable_snd : Measurable (fun z : (ℕ → α) × α => z.2))
        · simpa (config := { iota := false }) only [Function.update_of_ne hj,Function.comp_def] using
            ((measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (ℕ → α) × α => z.1)))
      refine ⟨hm,Measure.eq_infinitePi _ (fun s t ht => ?_)⟩
      rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
      by_cases hi : i∈s
      · have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
            (Set.pi (↑(s.erase i)) t) ×ˢ t i := by
          ext z
          simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Finset.mem_erase]
          constructor
          · intro h
            exact ⟨fun j hj => by simpa (config := { iota := false }) only [Function.update_of_ne hj.1] using h j hj.2,
              by simpa (config := { iota := false }) only [Function.update_self] using h i hi⟩
          · rintro ⟨h,hv⟩ j hj
            by_cases hji : j=i
            · subst j; simpa (config := { iota := false }) only [Function.update_self] using hv
            · simpa (config := { iota := false }) only [Function.update_of_ne hji] using h j ⟨hji,hj⟩
        rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun j _ => ht j)]
        exact Finset.prod_erase_mul s (fun j => μ (t j)) hi
      · have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹' Set.pi (↑s) t =
            (Set.pi (↑s) t) ×ˢ Set.univ := by
          ext z
          simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,and_true]
          apply forall_congr'
          intro j
          apply forall_congr'
          intro hj
          rw [Function.update_of_ne (show j≠i from fun he => hi (he ▸ hj))]
        rw [he,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi _ (fun j _ => ht j)]
    have freyaFreshTapeEvent {α : Type} [MeasurableSpace α]
        (μ : Measure α) [IsProbabilityMeasure μ] (i : ℕ)
        (E : Set (ℕ → α)) (hE : MeasurableSet E)
        (hinvariant : ∀ t a, Function.update t i a∈E ↔ t∈E)
        (U : Set α) (hU : MeasurableSet U) :
        (Measure.infinitePi fun _ : ℕ => μ) (E∩{t | t i∈U})=
          (Measure.infinitePi fun _ : ℕ => μ) E*μ U := by
      have hr := freyaInfiniteResample μ i
      have hm : MeasurableSet (E∩{t : ℕ → α | t i∈U}) :=
        hE.inter ((measurable_pi_apply i) hU)
      have he : (fun z : (ℕ → α) × α => Function.update z.1 i z.2) ⁻¹'
          (E∩{t | t i∈U})=E×ˢU := by
        ext z
        simp (config := { iota := false }) only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq,
          Set.mem_prod,Function.update_self,hinvariant]
      conv_lhs => rw [← hr.map_eq]
      rw [Measure.map_apply hr.measurable hm,he,Measure.prod_prod]
    have freyaFreshTapeEventProd {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
        (i : ℕ) (E : Set ((ℕ → α) × β)) (hE : MeasurableSet E)
        (hinvariant : ∀ t b a, (Function.update t i a,b)∈E ↔ (t,b)∈E)
        (U : Set α) (hU : MeasurableSet U) :
        ((Measure.infinitePi fun _ : ℕ => μ).prod ν) (E∩{z | z.1 i∈U})=
          ((Measure.infinitePi fun _ : ℕ => μ).prod ν) E*μ U := by
      have hm : MeasurableSet (E∩{z : (ℕ → α) × β | z.1 i∈U}) :=
        hE.inter (((measurable_pi_apply i).comp measurable_fst) hU)
      rw [Measure.prod_apply_symm hm]
      have he (b : β) : (Measure.infinitePi fun _ : ℕ => μ)
          ((fun t => (t,b)) ⁻¹' (E∩{z | z.1 i∈U}))=
          (Measure.infinitePi fun _ : ℕ => μ) ((fun t => (t,b)) ⁻¹' E)*μ U :=
        freyaFreshTapeEvent μ i ((fun t => (t,b)) ⁻¹' E)
          (hE.preimage (measurable_id.prodMk measurable_const))
          (fun t a => hinvariant t b a) U hU
      simp_rw [he]
      rw [lintegral_mul_const' _ _ (measure_ne_top μ U),← Measure.prod_apply_symm hE]
    have freyaFreshTapeEventProdProd {α β γ : Type}
        [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
        (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
        (ξ : Measure γ) [IsProbabilityMeasure ξ]
        (i : ℕ) (E : Set (((ℕ → α) × β) × γ)) (hE : MeasurableSet E)
        (hinvariant : ∀ t b c a, ((Function.update t i a,b),c)∈E ↔ ((t,b),c)∈E)
        (U : Set α) (hU : MeasurableSet U) :
        (((Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ) (E∩{z | z.1.1 i∈U})=
          (((Measure.infinitePi fun _ : ℕ => μ).prod ν).prod ξ) E*μ U := by
      let e : (((ℕ → α) × β) × γ) ≃ᵐ ((ℕ → α) × β × γ) := MeasurableEquiv.prodAssoc
      have hp := measurePreserving_prodAssoc (Measure.infinitePi fun _ : ℕ => μ) ν ξ
      have h := freyaFreshTapeEventProd μ (ν.prod ξ) i (e.symm ⁻¹' E)
        (hE.preimage e.symm.measurable)
        (fun t b a => hinvariant t b.1 b.2 a) U hU
      have hm : MeasurableSet ((e.symm ⁻¹' E)∩{z : (ℕ → α) × β × γ | z.1 i∈U}) :=
        (hE.preimage e.symm.measurable).inter (((measurable_pi_apply i).comp measurable_fst) hU)
      rw [← hp.map_eq,Measure.map_apply hp.measurable hm,
        Measure.map_apply hp.measurable (hE.preimage e.symm.measurable)] at h
      exact h
    have freyaSelectedUniformRows (m S : ℕ) (I : Fin S → ℕ) (hI : Function.Injective I) :
        MeasurePreserving (fun rows : ℕ → ChoiceRow => fun j => rows (I j) m)
          (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow))
          (Measure.pi fun _ : Fin S => (PMF.uniformOfFintype (Fin (m+1))).toMeasure) := by
      have he := measurePreserving_eval_infinitePi
        (fun k : ℕ => (PMF.uniformOfFintype (Fin (k+1))).toMeasure) m
      have hind := (iIndepFun_infinitePi (P:=fun _ : ℕ => (rowLaw : Measure ChoiceRow))
        (fun _ => he.measurable)).precomp hI
      have hlaw (j : Fin S) : HasLaw (fun rows : ℕ → ChoiceRow => rows (I j) m)
          (PMF.uniformOfFintype (Fin (m+1))).toMeasure
          (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow)) := by
        have h := he.comp (measurePreserving_eval_infinitePi
          (fun _ : ℕ => (rowLaw : Measure ChoiceRow)) (I j))
        exact ⟨h.measurable.aemeasurable,h.map_eq⟩
      exact ⟨Measurable.of_eval (fun j => he.measurable.comp (measurable_pi_apply (I j))),
        (iIndepFun.hasLaw_pi hlaw hind).map_eq⟩
    have freyaUniformRowCylinder (m S : ℕ) (I : Fin S → ℕ) (hI : Function.Injective I)
        (v : Fin S → Fin (m+1)) :
        (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow))
          {rows | (fun j => rows (I j) m)=v}=(((m+1 : ℕ) : ℝ≥0∞)^S)⁻¹ := by
      have h := freyaSelectedUniformRows m S I hI
      have hm := congrArg (fun μ => μ {v}) h.map_eq
      rw [Measure.map_apply h.measurable (measurableSet_singleton v)] at hm
      change (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow))
        {rows | (fun j => rows (I j) m)=v}=_ at hm
      rw [hm]
      simp (config := { iota := false }) [Measure.pi_singleton,PMF.uniformOfFintype_apply,ENNReal.inv_pow]
    have freyaUniformLabelCylinder (m S : ℕ) (hm : 0<m)
        (I : Fin S → ℕ) (hI : Function.Injective I) (v : Fin S → Fin m) :
        MeasurableSet {rows : ℕ → ChoiceRow | (fun j => labelAt (rows (I j)) m)=fun j => some (v j)} ∧
        (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow))
          {rows | (fun j => labelAt (rows (I j)) m)=fun j => some (v j)}=((m : ℝ≥0∞)^S)⁻¹ := by
      cases m with
      | zero => omega
      | succ m =>
        have he (row : ChoiceRow) : labelAt row (m+1)=some (row m) := by
          delta labelAt
          rw [dite_eq_left (Nat.succ_pos m)]
          apply congrArg some
          apply Fin.ext
          exact congrArg (fun j : ℕ => (row j).val) (Nat.add_sub_cancel m 1)
        have hs : {rows : ℕ → ChoiceRow | (fun j => labelAt (rows (I j)) (m+1))=fun j => some (v j)}=
            {rows | (fun j => rows (I j) m)=v} := by
          ext rows
          simp (config := { iota := false }) only [Set.mem_ofPred_eq,he]
          constructor
          · intro h
            funext j
            exact Option.some.inj (congrFun h j)
          · intro h
            funext j
            exact congrArg some (congrFun h j)
        rw [hs]
        refine ⟨?_,freyaUniformRowCylinder m S I hI v⟩
        exact (freyaSelectedUniformRows m S I hI).measurable (measurableSet_singleton v)
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
        MeasurableSingletonClass (Option α) := by
      constructor
      intro x
      let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
      have he : {x}=encode ⁻¹' {encode x} := by
        ext y
        cases x <;> cases y <;> simp (config := { iota := false }) [encode]
      have hsingleton : MeasurableSet {encode x} := by
        rw [measurableSet_sum_iff]
        cases x <;> constructor <;> simp (config := { iota := false }) [encode]
        · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
          rw [he]
          exact MeasurableSet.empty
        · rename_i b
          have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
          rw [he]
          exact measurableSet_singleton _
      rw [he]
      exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
        hsingleton
    have freyaOptionSomeMeas {α : Type} [MeasurableSpace α] :
        Measurable (some : α → Option α) := by
      delta instMeasurableSpaceOption
      rw [measurable_comap_iff]
      exact measurable_inr
    have freyaLabelAtMeas (m : ℕ) : Measurable (fun row : ChoiceRow => labelAt row m) := by
      let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
      by_cases hm : 0<m
      · let g : Fin (m-1+1) → Option (Fin m) := fun i => some ⟨i.val,by have := i.isLt; omega⟩
        have hg : Measurable g := measurable_of_countable g
        have he : Measurable (fun row : ChoiceRow => row (m-1)) := measurable_pi_apply (m-1)
        convert hg.comp he using 1
        funext row
        delta labelAt
        rw [dite_eq_left hm]
        rfl
      · delta labelAt
        simp (config := { iota := false }) only [hm,dite_false]
        exact measurable_const
    have freyaBatchLabelsMeas (q : Raw) (batch slot : ℕ) :
        Measurable (fun seed : Seed q.K => batchLabels q seed batch slot) := by
      exact (freyaLabelAtMeas q.m).comp
        ((measurable_pi_apply slot).comp ((measurable_pi_apply batch).comp measurable_fst))
    have freyaCondExpIndicatorFromLaw {Ω : Type} [mΩ : MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hH : H≤mΩ)
        (C : Set Ω) (hC : MeasurableSet[mΩ] C) (c : ℝ≥0∞)
        (hlaw : ∀ E,MeasurableSet[H] E → P (E∩C)=P E*c) :
        P[C.indicator (fun _ => (1 : ℝ)) | H]=ᵐ[P] (fun _ => c.toReal) := by
      let : MeasurableSpace Ω := mΩ
      have hf : Integrable (C.indicator (fun _ => (1 : ℝ))) P :=
        (integrable_const (1 : ℝ)).indicator hC
      apply Filter.EventuallyEq.symm
      apply ae_eq_condExp_of_forall_setIntegral_eq hH hf
      · intro E _ _
        exact integrable_const _
      · intro E hE _
        rw [setIntegral_indicator hC,integral_const,integral_const]
        simp (config := { iota := false }) only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
        rw [hlaw E hE,ENNReal.toReal_mul,mul_one]
      · exact stronglyMeasurable_const.aestronglyMeasurable
    have freyaConditionalRectangle {Ω : Type} [mΩ : MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hH : H≤mΩ)
        (A C B : Set Ω) (hA : MeasurableSet[mΩ] A) (hC : MeasurableSet[mΩ] C)
        (c : ℝ≥0∞) (hc : c≠⊤)
        (hconstant : P[C.indicator (fun _ => (1 : ℝ)) | H]=ᵐ[P] (fun _ => c.toReal))
        (hfactor : ∀ᵐ z ∂P,z∈B →
          (P[(A∩C).indicator (fun _ => (1 : ℝ)) | H]) z=
            (P[A.indicator (fun _ => (1 : ℝ)) | H]) z*
              (P[C.indicator (fun _ => (1 : ℝ)) | H]) z)
        (E : Set Ω) (hE : MeasurableSet[H] E) (hEB : E⊆B) :
        P (E∩(A∩C))=P (E∩A)*c := by
      let : MeasurableSpace Ω := mΩ
      have hAC : MeasurableSet[mΩ] (A∩C) := hA.inter hC
      have hceq : (∫ z in E,(P[(A∩C).indicator (fun _ => (1 : ℝ)) | H]) z ∂P)=
          (∫ z in E,(P[A.indicator (fun _ => (1 : ℝ)) | H]) z ∂P)*c.toReal := by
        calc
          _ = ∫ z in E,(P[A.indicator (fun _ => (1 : ℝ)) | H]) z*c.toReal ∂P := by
            apply setIntegral_congr_ae (hH _ hE)
            filter_upwards [hfactor,hconstant] with z hf hconst hz
            rw [hf (hEB hz),hconst]
          _ = _ := integral_mul_const _ _
      rw [setIntegral_condExp hH ((integrable_const (1 : ℝ)).indicator hAC) hE,
        setIntegral_condExp hH ((integrable_const (1 : ℝ)).indicator hA) hE,
        setIntegral_indicator hAC,setIntegral_indicator hA,integral_const,integral_const] at hceq
      simp (config := { iota := false }) only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hceq
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (ENNReal.mul_ne_top (measure_ne_top P _) hc)).mp
      rw [ENNReal.toReal_mul]
      exact hceq
    have freyaJointEventExtension {Ω : Type} [mΩ : MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (H G : MeasurableSpace Ω) (hH : H≤mΩ) (hG : G≤mΩ)
        (B C : Set Ω) (c : ℝ≥0∞)
        (hrect : ∀ A,MeasurableSet[H] A → ∀ D,MeasurableSet[G] D →
          P ((B∩A∩D)∩C)=P (B∩A∩D)*c)
        (E : Set Ω) (hE : MeasurableSet[H⊔G] E) :
        P ((B∩E)∩C)=P (B∩E)*c := by
      let : MeasurableSpace Ω := mΩ
      let R : Set (Set Ω) := {D | ∃ A,MeasurableSet[H] A ∧ ∃ T,MeasurableSet[G] T ∧ D=A∩T}
      have hgen : H⊔G=MeasurableSpace.generateFrom R := by
        apply le_antisymm
        · apply sup_le
          · intro A hA
            have hh : A∩Set.univ∈R := ⟨A,hA,Set.univ,MeasurableSet.univ,rfl⟩
            simpa (config := { iota := false }) only [Set.inter_univ] using MeasurableSpace.measurableSet_generateFrom hh
          · intro D hD
            have hh : Set.univ∩D∈R := ⟨Set.univ,MeasurableSet.univ,D,hD,rfl⟩
            simpa (config := { iota := false }) only [Set.univ_inter] using MeasurableSpace.measurableSet_generateFrom hh
        · apply MeasurableSpace.generateFrom_le
          rintro D ⟨A,hA,T,hT,rfl⟩
          exact ((show H≤H⊔G from le_sup_left) _ hA).inter
            ((show G≤H⊔G from le_sup_right) _ hT)
      have hpi : IsPiSystem R := by
        rintro D ⟨A,hA,T,hT,rfl⟩ F ⟨A',hA',T',hT',rfl⟩ _
        refine ⟨A∩A',hA.inter hA',T∩T',hT.inter hT',?_⟩
        ext z
        simp (config := { iota := false }) only [Set.mem_inter_iff]
        tauto
      let μ := P.restrict (B∩C)
      let ν := c • P.restrict B
      have hbase (D : Set Ω) (hD : D∈R) : μ D=ν D := by
        obtain ⟨A,hA,T,hT,rfl⟩ := hD
        have hAT : MeasurableSet[mΩ] (A∩T) := (hH _ hA).inter (hG _ hT)
        simpa (config := { iota := false }) only [μ,ν,Measure.restrict_apply hAT,Measure.smul_apply,smul_eq_mul,
          Set.inter_assoc,Set.inter_left_comm,Set.inter_comm,mul_comm] using hrect A hA T hT
      have huniv : μ Set.univ=ν Set.univ :=
        hbase Set.univ ⟨Set.univ,MeasurableSet.univ,Set.univ,MeasurableSet.univ,(Set.inter_self _).symm⟩
      have he := ext_on_measurableSpace_of_generate_finite mΩ R hbase
        (sup_le hH hG) hgen hpi huniv hE
      have hEm : MeasurableSet[mΩ] E := (sup_le hH hG) _ hE
      simpa (config := { iota := false }) only [μ,ν,Measure.restrict_apply hEm,Measure.smul_apply,smul_eq_mul,
        Set.inter_assoc,Set.inter_left_comm,Set.inter_comm,mul_comm] using he
    have freyaPageHistoryFreshEvent (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (batch : ℕ) (hH : historyBefore q O batch ≤
          (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))))
        (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
        (hE : MeasurableSet[historyBefore q O batch] E)
        (U : Set (ℕ → ChoiceRow)) (hU : MeasurableSet U) :
        (executionLaw q O : Measure _) (E∩{z | z.1.1 batch∈U})=
          (executionLaw q O : Measure _) E*
            (Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow)) U := by
      classical
      have : NeZero (max 1 q.K) := ⟨by omega⟩
      let μ := Measure.infinitePi fun _ : ℕ => (rowLaw : Measure ChoiceRow)
      let ν := (refreshLaw q.ρ : Measure (ℕ → Bool)).prod
        (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure
      have hν : IsProbabilityMeasure ν := by
        dsimp only [ν]
        infer_instance
      have hi (t : ℕ → ℕ → ChoiceRow) (b : (ℕ → Bool) × Fin (max 1 q.K))
          (ω : (k : ℕ) → O.Seed k) (a : ℕ → ChoiceRow) :
          ((Function.update t batch a,b),ω)∈E ↔ ((t,b),ω)∈E := by
        apply freyaPageHistoryEventInvariant q O (t,b) (Function.update t batch a,b) ω batch rfl
          (fun j hj => Function.update_of_ne (by omega : j≠batch) a t) E hE
      exact freyaFreshTapeEventProdProd μ ν (O.law : Measure _) batch E (hH _ hE) hi U hU
    have freyaPageHistoryLabelLaw (q : Raw) (hm : 0<q.m)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (batch : ℕ) (hH : historyBefore q O batch ≤
          (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))))
        (E : Set (Seed q.K × ((k : ℕ) → O.Seed k)))
        (hE : MeasurableSet[historyBefore q O batch] E)
        (I : Fin q.S → ℕ) (hI : Function.Injective I) (v : Fin q.S → Fin q.m) :
        (executionLaw q O : Measure _) (E∩{z | (fun j => batchLabels q z.1 batch (I j))=fun j => some (v j)})=
          (executionLaw q O : Measure _) E*((q.m : ℝ≥0∞)^q.S)⁻¹ := by
      have hc := freyaUniformLabelCylinder q.m q.S hm I hI v
      have h := freyaPageHistoryFreshEvent q O batch hH E hE _ hc.1
      rw [hc.2] at h
      exact h
    have freyaFixedVectorCylinder {α : Type} (S : ℕ) (I : Fin S → ℕ)
        (hI : Function.Injective I) (v : Fin S → α) (default : α) :
        ∃ F : Finset ℕ,∃ labels : ℕ → α,∀ X : ℕ → α,
          ((fun j => X (I j))=v) ↔ ∀ j∈F,X j=labels j := by
      classical
      refine ⟨Finset.univ.image I,Function.extend I v (fun _ => default),?_⟩
      intro X
      constructor
      · intro h j hj
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
        rw [hI.extend_apply]
        exact congrFun h a
      · intro h
        funext j
        have hh := h (I j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)
        simpa (config := { iota := false }) only [hI.extend_apply] using hh
    have freyaPageScheduleVectorFactor (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (batch : ℕ) (Γ : Seed q.K × ((k : ℕ) → O.Seed k) →
          LongTails.Setups.FreyaIndependence.BatchSchedule q.n)
        (hfactor : ∀ U : Set (LongTails.Setups.FreyaIndependence.BatchSchedule q.n),MeasurableSet U →
          ∀ F : Finset ℕ,∀ labels : ℕ → Option (Fin q.m),
          ∀ᵐ z ∂(executionLaw q O : Measure _),
            LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch →
            ((executionLaw q O : Measure _)[fun w =>
              if Γ w∈U ∧ (∀ j∈F,batchLabels q w.1 batch j=labels j) then (1 : ℝ) else 0
              | historyBefore q O batch]) z=
            ((executionLaw q O : Measure _)[fun w => if Γ w∈U then (1 : ℝ) else 0
              | historyBefore q O batch]) z*
            ((executionLaw q O : Measure _)[fun w =>
              if ∀ j∈F,batchLabels q w.1 batch j=labels j then (1 : ℝ) else 0
              | historyBefore q O batch]) z)
        (I : Fin q.S → ℕ) (hI : Function.Injective I) (v : Fin q.S → Fin q.m)
        (U : Set (LongTails.Setups.FreyaIndependence.BatchSchedule q.n)) (hU : MeasurableSet U) :
        let P := (executionLaw q O : Measure _)
        let C := {z : Seed q.K × ((k : ℕ) → O.Seed k) |
          (fun j => batchLabels q z.1 batch (I j))=fun j => some (v j)}
        ∀ᵐ z ∂P,LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch →
          (P[((Γ ⁻¹' U)∩C).indicator (fun _ => (1 : ℝ)) | historyBefore q O batch]) z=
            (P[(Γ ⁻¹' U).indicator (fun _ => (1 : ℝ)) | historyBefore q O batch]) z*
              (P[C.indicator (fun _ => (1 : ℝ)) | historyBefore q O batch]) z := by
      classical
      obtain ⟨F,labels,he⟩ := freyaFixedVectorCylinder q.S I hI (fun j => some (v j)) none
      have h := hfactor U hU F labels
      have hi (D : Set (Seed q.K × ((k : ℕ) → O.Seed k))) :
          D.indicator (fun _ => (1 : ℝ))=(fun w => if w∈D then (1 : ℝ) else 0) := by rfl
      simp (config := { iota := false }) only [hi,Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,he]
      convert h using 1
      congr! 12
    have freyaPageInvocationHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        Measurable[historyBefore q O batch]
          (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => invocation q O z.1 z.2 batch) := by
      exact measurable_fst.comp (show Measurable[historyBefore q O batch]
        (freyaHistoryView q O batch) from Measurable.of_comap_le le_rfl)
    have freyaPageDifferenceHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        MeasurableSet[historyBefore q O batch]
          {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch} := by
      let tag := fun a : Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) =>
        a.elim false (fun t => !t.1)
      have ht : Measurable tag := freyaDevelopmentOptionElimMeas false _
        ((measurable_of_countable (fun b : Bool => !b)).comp measurable_fst)
      have hi := ht.comp (freyaPageInvocationHistoryMeas q O batch)
      have he : {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch}=
          {z : Seed q.K × ((k : ℕ) → O.Seed k) | tag (invocation q O z.1 z.2 batch)=true} := by
        ext z
        dsimp only [LongTails.Setups.FreyaIndependence.isDifferenceBatch,Set.mem_ofPred_eq]
        cases h : invocation q O z.1 z.2 batch with
        | none => simp (config := { iota := false }) [tag]
        | some a =>
          obtain ⟨b,x,y,t,id⟩ := a
          cases b <;> simp (config := { iota := false }) [tag]
      rw [he]
      exact hi (measurableSet_singleton true)
    have freyaPageScheduleFixedLabelLaw (q : Raw) (hm : 0<q.m)
        (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hind : batchScheduleIndependent q f τ O) (batch : ℕ) :
        ∃ Γ : Seed q.K × ((k : ℕ) → O.Seed k) → BatchSchedule q.n,
          Measurable Γ ∧
          (∀ᵐ z ∂(executionLaw q O : Measure _),ScheduleRealization q f τ O z.1 z.2 batch (Γ z)) ∧
          ∀ I : Fin q.S → ℕ,Function.Injective I → ∀ v : Fin q.S → Fin q.m,
            ∀ E,MeasurableSet[historyBefore q O batch ⊔ MeasurableSpace.comap Γ inferInstance] E →
              (∀ z∈E,isDifferenceBatch q O z batch) →
              (executionLaw q O : Measure _) (E∩{z | (fun j => batchLabels q z.1 batch (I j))=fun j => some (v j)})=
                (executionLaw q O : Measure _) E*((q.m : ℝ≥0∞)^q.S)⁻¹ := by
      classical
      let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
      let mΩ : MeasurableSpace Ω := inferInstance
      let P := (executionLaw q O : Measure Ω)
      obtain ⟨hH,hlabels,Γ,hΓ,hreal,hfactor⟩ := hind batch
      refine ⟨Γ,hΓ,hreal,?_⟩
      intro I hI v E hE hEB
      let : MeasurableSingletonClass (Option (Fin q.m)) := freyaOptionSingleton
      let H := historyBefore q O batch
      let G := MeasurableSpace.comap Γ (inferInstance : MeasurableSpace (BatchSchedule q.n))
      let : MeasurableSpace Ω := mΩ
      let B : Set Ω := {z | isDifferenceBatch q O z batch}
      let C : Set Ω := {z | (fun j => batchLabels q z.1 batch (I j))=fun j => some (v j)}
      let c : ℝ≥0∞ := ((q.m : ℝ≥0∞)^q.S)⁻¹
      have hc : c≠⊤ := ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by exact_mod_cast hm.ne'))
      have hC : MeasurableSet[mΩ] C :=
        (Measurable.of_eval (fun j => hlabels (I j))) (measurableSet_singleton (fun j => some (v j)))
      have hB : MeasurableSet[H] B := freyaPageDifferenceHistoryMeas q O batch
      have hG : G≤mΩ := hΓ.comap_le
      have hconstant := freyaCondExpIndicatorFromLaw P H hH C hC c
        (fun A hA => freyaPageHistoryLabelLaw q hm O batch hH A hA I hI v)
      have hrect : ∀ A,MeasurableSet[H] A → ∀ D,MeasurableSet[G] D →
          P ((B∩A∩D)∩C)=P (B∩A∩D)*c := by
        intro A hA D hD
        obtain ⟨U,hU,rfl⟩ := hD
        have hf := freyaPageScheduleVectorFactor q O batch Γ hfactor I hI v U hU
        have hr := freyaConditionalRectangle P H hH (Γ ⁻¹' U) C B (hΓ hU) hC c hc
          hconstant hf (B∩A) (hB.inter hA) Set.inter_subset_left
        simpa (config := { iota := false }) only [Set.inter_assoc] using hr
      have hh := freyaJointEventExtension P H G hH hG B C c hrect E hE
      have he : B∩E=E := Set.inter_eq_right.mpr hEB
      rw [he] at hh
      exact hh
    have freyaCountInitialSegment (N c : ℕ) (hc : c≤N) :
        (∑ k∈Finset.range N,if k<c then (1 : ℕ) else 0)=c := by
      rw [← Finset.sum_filter]
      have he : (Finset.range N).filter (fun k => k<c)=Finset.range c := by
        ext k
        simp (config := { iota := false }) only [Finset.mem_filter,Finset.mem_range]
        omega
      rw [he]
      simp (config := { iota := false }) only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    have freyaPageCallHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        Measurable[historyBefore q O batch]
          (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => (batchStartCall q O z.1 z.2 batch).getD 0) := by
      classical
      let mark := fun o : Option ((Fin 1 × Option (Request q.d q.m q.n)) ×
          Reply q.d q.n × (Fin q.n → Option (Job q.d q.m))) => o.elim (0 : ℕ) (fun _ => 1)
      have hmark : Measurable mark := freyaDevelopmentOptionElimMeas 0 _ measurable_const
      have hh : Measurable[historyBefore q O batch] (freyaHistoryView q O batch) :=
        Measurable.of_comap_le le_rfl
      have hm : Measurable[historyBefore q O batch]
          (fun z => ∑ k∈Finset.range (eventLimit q+1),mark ((freyaHistoryView q O batch z).2 k)) :=
        Finset.measurable_sum _ (fun k _ => hmark.comp ((measurable_pi_apply k).comp (measurable_snd.comp hh)))
      have he (z : Seed q.K × ((k : ℕ) → O.Seed k)) :
          (∑ k∈Finset.range (eventLimit q+1),mark ((freyaHistoryView q O batch z).2 k))=
            (batchStartCall q O z.1 z.2 batch).getD 0 := by
        have hc : (batchStartCall q O z.1 z.2 batch).getD 0≤eventLimit q+1 := by
          cases h : batchStartCall q O z.1 z.2 batch with
          | none => simp (config := { iota := false }) only [Option.getD_none]; omega
          | some call =>
            have hb := (freyaPageBatchStartFacts q O z.1 z.2 batch call h).1
            simpa (config := { iota := false }) only [Option.getD_some] using (show call≤eventLimit q+1 by omega)
        have hsum : (∑ k∈Finset.range (eventLimit q+1),mark ((freyaHistoryView q O batch z).2 k))=
            ∑ k∈Finset.range (eventLimit q+1),if k<(batchStartCall q O z.1 z.2 batch).getD 0 then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          dsimp only [freyaHistoryView]
          split <;> rfl
        rw [hsum]
        exact freyaCountInitialSegment _ _ hc
      have hfun := funext he
      rw [hfun] at hm
      exact hm
    have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
        [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
        (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
        Measurable (fun z => f (g z) z) :=
      (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
        (measurable_id.prodMk hg)
    have freyaScheduleWorkerMeas {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
        (γ : Ω → BatchSchedule n) (hγ : Measurable γ)
        (call : Ω → ℕ) (hcall : Measurable call) (s : Ω → ScheduleState n)
        (hjobs : ∀ i,Measurable (fun z => (s z).jobs i)) :
        Measurable (fun z => scheduleWorker (γ z) (call z) (s z)) := by
      classical
      let : MeasurableSingletonClass (Option (Fin n)) := freyaOptionSingleton
      have hfields : Measurable (fun z => ((γ z).duration,(γ z).priority)) :=
        (show Measurable (fun a : BatchSchedule n => (a.duration,a.priority)) from
          Measurable.of_comap_le le_rfl).comp hγ
      let finish := fun z i => ((s z).jobs i).2+(γ z).duration i ((s z).jobs i).1
      let priority := fun z i => (γ z).priority (call z) i
      have hf (i : Fin n) : Measurable (fun z => finish z i) :=
        (hjobs i).snd.add (freyaMeasurableSelect _ (hjobs i).fst _
          (fun k => (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hfields.fst)))
      have hp (i : Fin n) : Measurable (fun z => priority z i) :=
        freyaMeasurableSelect call hcall _
          (fun k => (measurable_pi_apply i).comp ((measurable_pi_apply k).comp hfields.snd))
      let step := fun z (best : Option (Fin n)) i => best.elim (some i) (fun b =>
        if finish z i<finish z b ∨ (finish z i=finish z b ∧
          (priority z i<priority z b ∨ (priority z i=priority z b ∧ i.val≤b.val)))
        then some i else some b)
      have hs (i : Fin n) (best : Ω → Option (Fin n)) (hb : Measurable best) :
          Measurable (fun z => step z (best z) i) := by
        apply freyaMeasurableSelect best hb (fun b z => step z b i)
        intro b
        cases b with
        | none => exact measurable_const
        | some b =>
          have hconst : MeasurableSet {z : Ω | i.val≤b.val} := by
            by_cases h : i.val≤b.val
            · convert (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω)) using 1
              ext z; simp (config := { iota := false }) [h]
            · convert (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) using 1
              ext z; simp (config := { iota := false }) [h]
          apply Measurable.ite _ measurable_const measurable_const
          exact (measurableSet_lt (hf i) (hf b)).union
            ((measurableSet_eq_fun (hf i) (hf b)).inter
              ((measurableSet_lt (hp i) (hp b)).union
                ((measurableSet_eq_fun (hp i) (hp b)).inter hconst)))
      have hfold (l : List (Fin n)) : ∀ best : Ω → Option (Fin n),Measurable best →
          Measurable (fun z => l.foldl (step z) (best z)) := by
        induction l with
        | nil => intro best hb; exact hb
        | cons i l ih =>
          intro best hb
          exact ih (fun z => step z (best z) i) (hs i best hb)
      have h := hfold (List.finRange n) (fun _ => none) measurable_const
      convert h using 1
      funext z
      delta scheduleWorker
      apply congrArg (fun step => (List.finRange n).foldl step none)
      funext best i
      cases best <;> rfl
    have freyaScheduleTraceMeas {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
        (γ : Ω → BatchSchedule n) (hγ : Measurable γ)
        (first call : Ω → ℕ) (hfirst : Measurable first) (hcall : Measurable call)
        (clock : Ω → ℝ≥0) (hclock : Measurable clock) (a : ℕ) :
        Measurable (fun z => ((scheduleTrace (γ z) (first z) (call z) (clock z) a).jobs,
          (scheduleTrace (γ z) (first z) (call z) (clock z) a).nextID)) := by
      classical
      let : MeasurableSingletonClass (Option (Fin n)) := freyaOptionSingleton
      induction a with
      | zero =>
        change Measurable (fun z => ((fun i : Fin n => (first z+i.val,(clock z : ℝ≥0∞))),first z+n))
        have hc : Measurable (fun z => (clock z : ℝ≥0∞)) := by fun_prop
        exact (Measurable.of_eval (fun i : Fin n => (hfirst.add_const i.val).prodMk hc)).prodMk (hfirst.add_const n)
      | succ a ih =>
        let s := fun z => scheduleTrace (γ z) (first z) (call z) (clock z) a
        have hj (i : Fin n) : Measurable (fun z => (s z).jobs i) := (measurable_pi_apply i).comp ih.fst
        have hn : Measurable (fun z => (s z).nextID) := ih.snd
        have hw := freyaScheduleWorkerMeas γ hγ (fun z => call z+a) (hcall.add_const a) s hj
        have hfields : Measurable (fun z => ((γ z).duration,(γ z).priority)) :=
          (show Measurable (fun g : BatchSchedule n => (g.duration,g.priority)) from
            Measurable.of_comap_le le_rfl).comp hγ
        let upd := fun (b : Option (Fin n)) z => b.elim ((s z).jobs,(s z).nextID) (fun i =>
          (Function.update (s z).jobs i ((s z).nextID,((s z).jobs i).2+(γ z).duration i ((s z).jobs i).1),
            (s z).nextID+1))
        have hu (b : Option (Fin n)) : Measurable (upd b) := by
          cases b with
          | none => exact ih
          | some i =>
            have ht : Measurable (fun z => ((s z).jobs i).2+(γ z).duration i ((s z).jobs i).1) :=
              (hj i).snd.add (freyaMeasurableSelect _ (hj i).fst _
                (fun k => (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hfields.fst)))
            exact ((measurable_update').comp (ih.fst.prodMk (hn.prodMk ht))).prodMk (hn.add_const 1)
        have hm := freyaMeasurableSelect _ hw upd hu
        convert hm using 1
        funext z
        have hs : scheduleTrace (γ z) (first z) (call z) (clock z) (a+1)=
            Option.casesOn (scheduleWorker (γ z) (call z+a) (s z)) (s z) (fun i =>
              ⟨Function.update (s z).jobs i ((s z).nextID,((s z).jobs i).2+(γ z).duration i ((s z).jobs i).1),
                (s z).nextID+1⟩) := by cases a <;> rfl'
        rw [hs]
        cases scheduleWorker (γ z) (call z+a) (s z) <;> rfl
    have freyaSelectedJobMeas {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
        (γ : Ω → BatchSchedule n) (hγ : Measurable γ)
        (first call : Ω → ℕ) (hfirst : Measurable first) (hcall : Measurable call)
        (clock : Ω → ℝ≥0) (hclock : Measurable clock) (a : ℕ) :
        Measurable (fun z => selectedJobID (γ z) (first z) (call z) (clock z) a) := by
      let : MeasurableSingletonClass (Option (Fin n)) := freyaOptionSingleton
      let s := fun z => scheduleTrace (γ z) (first z) (call z) (clock z) a
      have hs := freyaScheduleTraceMeas γ hγ first call hfirst hcall clock hclock a
      have hj (i : Fin n) : Measurable (fun z => (s z).jobs i) := (measurable_pi_apply i).comp hs.fst
      have hw := freyaScheduleWorkerMeas γ hγ (fun z => call z+a) (hcall.add_const a) s hj
      have hm := freyaMeasurableSelect _ hw
        (fun b z => b.elim (0 : ℕ) (fun i => ((s z).jobs i).1)) (by
          intro b
          cases b with
          | none => exact measurable_const
          | some i => exact (hj i).fst)
      convert hm using 1
      funext z
      delta selectedJobID
      change ((scheduleWorker (γ z) (call z+a) (s z)).map (fun i => ((s z).jobs i).1)).getD 0=_
      cases scheduleWorker (γ z) (call z+a) (s z) <;> rfl
    have freyaScheduleFoldSome {α β : Type} (step : Option β → α → Option β)
        (hstep : ∀ v a, ∃ b, step v a = some b) (l : List α) (hne : l ≠ []) :
        ∀ v, ∃ b, l.foldl step v = some b := by
      induction l with
      | nil => exact (hne rfl).elim
      | cons a l ih =>
        intro v
        cases l with
        | nil => exact hstep v a
        | cons b l => exact ih (List.cons_ne_nil _ _) (step v a)
    have freyaScheduleWorkerExists {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (call : ℕ) (s : ScheduleState n) : ∃ i, scheduleWorker γ call s = some i := by
      classical
      delta scheduleWorker
      apply freyaScheduleFoldSome
      · intro v i
        cases v with
        | none => exact ⟨i,rfl⟩
        | some b =>
          dsimp only
          split
          · exact ⟨i,rfl⟩
          · exact ⟨b,rfl⟩
      · intro he
        have hlen : (List.finRange n).length = n := List.length_finRange
        rw [he,List.length_nil] at hlen
        omega
    have freyaScheduleStep {n : ℕ} (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) :
        let s := scheduleTrace γ firstID callStart clock k
        scheduleTrace γ firstID callStart clock (k+1) =
          Option.casesOn (scheduleWorker γ (callStart+k) s) s (fun i =>
            ⟨Function.update s.jobs i (s.nextID,(s.jobs i).2+γ.duration i (s.jobs i).1),s.nextID+1⟩) := by
      cases k <;> rfl'
    have freyaScheduleIDs {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) (k : ℕ) :
        let s := scheduleTrace γ firstID callStart clock k
        (∀ i, (s.jobs i).1 < s.nextID) ∧
          Function.Injective (fun i => (s.jobs i).1) ∧
          (∀ r < k, selectedJobID γ firstID callStart clock r < s.nextID) ∧
          ∀ r < k, ∀ i, selectedJobID γ firstID callStart clock r ≠ (s.jobs i).1 := by
      classical
      induction k with
      | zero =>
        refine ⟨?_,?_,?_,?_⟩
        · intro i
          change firstID+i.val < firstID+n
          have h := i.isLt
          omega
        · intro i l h
          apply Fin.ext
          change firstID+i.val=firstID+l.val at h
          omega
        · intro r hr; omega
        · intro r hr; omega
      | succ k ih =>
        let s := scheduleTrace γ firstID callStart clock k
        obtain ⟨i,hi⟩ := freyaScheduleWorkerExists hn γ (callStart+k) s
        let t : ScheduleState n :=
          ⟨Function.update s.jobs i (s.nextID,(s.jobs i).2+γ.duration i (s.jobs i).1),s.nextID+1⟩
        have hstate : scheduleTrace γ firstID callStart clock (k+1) = t := by
          rw [freyaScheduleStep]
          rw [hi]
        have hselected : selectedJobID γ firstID callStart clock k = (s.jobs i).1 := by
          delta selectedJobID
          change ((scheduleWorker γ (callStart+k) s).map (fun i => (s.jobs i).1)).getD 0 = _
          rw [hi]
          rfl
        dsimp only at ih ⊢
        rw [hstate]
        change (∀ l, (t.jobs l).1<t.nextID) ∧ Function.Injective (fun l => (t.jobs l).1) ∧ _
        refine ⟨?_,?_,?_,?_⟩
        · intro l
          dsimp only [t]
          by_cases hl : l=i
          · subst l
            rw [Function.update_self]
            exact Nat.lt_succ_self _
          · rw [Function.update_of_ne hl]
            exact (ih.1 l).trans (Nat.lt_succ_self _)
        · intro l l' h
          dsimp only [t] at h
          by_cases hl : l=i
          · subst l
            rw [Function.update_self] at h
            by_cases hl' : l'=i
            · exact hl'.symm
            · rw [Function.update_of_ne hl'] at h
              have hb := ih.1 l'
              change (s.jobs l').1<s.nextID at hb
              change s.nextID=(s.jobs l').1 at h
              omega
          · rw [Function.update_of_ne hl] at h
            by_cases hl' : l'=i
            · subst l'
              rw [Function.update_self] at h
              have hb := ih.1 l
              change (s.jobs l).1<s.nextID at hb
              change (s.jobs l).1=s.nextID at h
              omega
            · rw [Function.update_of_ne hl'] at h
              exact ih.2.1 h
        · intro r hr
          change selectedJobID γ firstID callStart clock r < s.nextID+1
          by_cases hrk : r=k
          · subst r
            rw [hselected]
            exact (ih.1 i).trans (Nat.lt_succ_self _)
          · exact (ih.2.2.1 r (by omega)).trans (Nat.lt_succ_self _)
        · intro r hr l
          dsimp only [t]
          by_cases hl : l=i
          · subst l
            rw [Function.update_self]
            by_cases hrk : r=k
            · subst r
              rw [hselected]
              exact (ih.1 i).ne
            · exact (ih.2.2.1 r (by omega)).ne
          · rw [Function.update_of_ne hl]
            by_cases hrk : r=k
            · subst r
              rw [hselected]
              exact fun h => hl (ih.2.1 h).symm
            · exact ih.2.2.2 r (by omega) l
    have freyaScheduleInjective {n : ℕ} (hn : 0 < n) (γ : BatchSchedule n)
        (firstID callStart : ℕ) (clock : ℝ≥0) :
        Function.Injective (selectedJobID γ firstID callStart clock) := by
      intro r s h
      have hne (a b : ℕ) (hab : a<b) :
          selectedJobID γ firstID callStart clock a ≠ selectedJobID γ firstID callStart clock b := by
        obtain ⟨i,hi⟩ := freyaScheduleWorkerExists hn γ (callStart+b) (scheduleTrace γ firstID callStart clock b)
        have hh := (freyaScheduleIDs hn γ firstID callStart clock b).2.2.2 a hab i
        delta selectedJobID
        dsimp only
        rw [hi]
        exact hh
      rcases lt_trichotomy r s with hrs | hrs | hrs
      · exact (hne r s hrs h).elim
      · exact hrs
      · exact (hne s r hrs h.symm).elim
    have freyaAdaptiveLabelPartition {Ω α : Type} [mΩ : MeasurableSpace Ω]
        [MeasurableSpace α] [MeasurableSingletonClass α]
        (P : Measure Ω) (H : MeasurableSpace Ω) (hH : H≤mΩ)
        (S : ℕ) (labels : ℕ → Ω → α) (hl : ∀ i,Measurable[mΩ] (labels i))
        (I : Ω → Fin S → ℕ) (hI : Measurable[H] I)
        (B : Set Ω) (hinj : ∀ ω ∈ B,Function.Injective (I ω))
        (v : Fin S → α) (mass : ℝ≥0∞)
        (hfixed : ∀ i : Fin S → ℕ,Function.Injective i →
          ∀ E,MeasurableSet[H] E → E⊆B →
            P (E∩{ω | (fun j => labels (i j) ω)=v})=P E*mass)
        (E : Set Ω) (hE : MeasurableSet[H] E) (hEB : E⊆B) :
        P (E∩{ω | (fun j => labels (I ω j) ω)=v})=P E*mass := by
      classical
      let : MeasurableSpace Ω := mΩ
      let A := fun i : Fin S → ℕ => E∩{ω | I ω=i}
      let C := fun i : Fin S → ℕ => A i∩{ω | (fun j => labels (i j) ω)=v}
      have hA0 (i : Fin S → ℕ) : MeasurableSet[H] (A i) :=
        hE.inter (hI (measurableSet_singleton i))
      have hA (i : Fin S → ℕ) : MeasurableSet[mΩ] (A i) := hH _ (hA0 i)
      have hC (i : Fin S → ℕ) : MeasurableSet[mΩ] (C i) :=
        (hA i).inter ((Measurable.of_eval fun j => hl (i j)) (measurableSet_singleton v))
      have hAd : Pairwise (fun i j : Fin S → ℕ => Disjoint (A i) (A j)) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro ω hi hj
        exact hij (hi.2.symm.trans hj.2)
      have hCd : Pairwise (fun i j : Fin S → ℕ => Disjoint (C i) (C j)) := by
        intro i j hij
        exact (hAd hij).mono Set.inter_subset_left Set.inter_subset_left
      have hAc : E=⋃ i,A i := by
        ext ω
        simp (config := { iota := false }) only [A,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
        constructor
        · intro h; exact ⟨I ω,h,rfl⟩
        · rintro ⟨i,h,_⟩; exact h
      have hCc : E∩{ω | (fun j => labels (I ω j) ω)=v}=⋃ i,C i := by
        ext ω
        simp (config := { iota := false }) only [C,A,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hE,hv⟩; exact ⟨I ω,⟨hE,rfl⟩,hv⟩
        · rintro ⟨i,⟨hE,hi⟩,hv⟩
          exact ⟨hE,by rw [hi]; exact hv⟩
      have hmass (i : Fin S → ℕ) : P (C i)=P (A i)*mass := by
        by_cases hi : Function.Injective i
        · exact hfixed i hi (A i) (hA0 i) (fun ω h => hEB h.1)
        · have he : A i=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro ω hω
            apply hi
            rw [← hω.2]
            exact hinj ω (hEB hω.1)
          simp (config := { iota := false }) only [C,he,Set.empty_inter,measure_empty,zero_mul]
      rw [hCc,measure_iUnion (μ:=P) hCd hC]
      conv_rhs => rw [hAc,measure_iUnion (μ:=P) hAd hA]
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr hmass
    have freyaPageCompletedLabelLaw (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O) (batch : ℕ) :
        let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
        (∀ᵐ z ∂P,isDifferenceBatch q O z batch →
          ∀ j : Fin q.S,(completedLabels q O z.1 z.2 batch j).isSome) ∧
        ∀ E,MeasurableSet[historyBefore q O batch] E →
          (∀ z∈E,isDifferenceBatch q O z batch) → ∀ v : Fin q.S → Fin q.m,
            P (E∩{z | completedLabels q O z.1 z.2 batch=fun j => some (v j)})=
              P E*((q.m : ℝ≥0∞)^q.S)⁻¹ := by
      classical
      let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
      let mΩ : MeasurableSpace Ω := inferInstance
      let P := (executionLaw q O : Measure Ω)
      let : MeasurableSingletonClass (Option (Fin q.m)) := freyaOptionSingleton
      obtain ⟨Γ,hΓ,hreal,hfixed⟩ := freyaPageScheduleFixedLabelLaw q hm f τ O hind batch
      have hH := (hind batch).1
      let H := historyBefore q O batch
      let G := MeasurableSpace.comap Γ (inferInstance : MeasurableSpace (BatchSchedule q.n))
      let : MeasurableSpace Ω := mΩ
      have hG : G≤mΩ := hΓ.comap_le
      let B : Set Ω := {z | isDifferenceBatch q O z batch}
      let first := fun z : Ω => (invocation q O z.1 z.2 batch).elim 0 (fun a => a.2.2.2.2)
      let start := fun z : Ω => (invocation q O z.1 z.2 batch).elim (0 : ℝ≥0) (fun a => a.2.2.2.1)
      let call := fun z : Ω => (batchStartCall q O z.1 z.2 batch).getD 0
      let I := fun z : Ω => fun j : Fin q.S => selectedJobID (Γ z) (first z) (call z) (start z) j.val
      have hfirst : Measurable[H] first :=
        (freyaDevelopmentOptionElimMeas 0 _ (by fun_prop)).comp (freyaPageInvocationHistoryMeas q O batch)
      have hstart : Measurable[H] start :=
        (freyaDevelopmentOptionElimMeas 0 _ (by fun_prop)).comp (freyaPageInvocationHistoryMeas q O batch)
      have hcall : Measurable[H] call := freyaPageCallHistoryMeas q O batch
      have hγjoint : Measurable[H⊔G] Γ :=
        (show Measurable[G] Γ from Measurable.of_comap_le le_rfl).mono le_sup_right le_rfl
      have hI : Measurable[H⊔G] I := by
        let : MeasurableSpace Ω := H⊔G
        exact Measurable.of_eval (fun j =>
          freyaSelectedJobMeas Γ hγjoint first call (hfirst.mono le_sup_left le_rfl)
            (hcall.mono le_sup_left le_rfl) start (hstart.mono le_sup_left le_rfl) j.val)
      have hinj (z : Ω) : Function.Injective (I z) :=
        (freyaScheduleInjective hn (Γ z) (first z) (call z) (start z)).comp Fin.val_injective
      have hs : ∀ᵐ z : Ω ∂P,servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
        (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
      have hactual : ∀ᵐ z : Ω ∂P,z∈B → completedLabels q O z.1 z.2 batch=
          (fun j => batchLabels q z.1 batch (I z j)) := by
        filter_upwards [hs,hreal] with z hz hr hB
        obtain ⟨x,y,c,id,hi⟩ := hB
        have h := schedule_selection q hm hn hS hK f τ O z.1 z.2 hz batch id x y c hi (Γ z) hr
        funext j
        simpa (config := { iota := false }) only [I,first,start,call,hi,Option.elim_some] using h.2.2 j
      constructor
      · filter_upwards [hactual] with z hz hB
        intro j
        rw [congrFun (hz hB) j]
        delta batchLabels labelAt
        rw [dite_eq_left hm]
        rfl
      · intro E hE hEB v
        have hlabel (k : ℕ) : Measurable[mΩ] (fun z : Ω => batchLabels q z.1 batch k) :=
          (freyaBatchLabelsMeas q batch k).comp measurable_fst
        have hp := freyaAdaptiveLabelPartition P (H⊔G) (sup_le hH hG) q.S
          (fun k z => batchLabels q z.1 batch k) hlabel I hI B (fun z _ => hinj z)
          (fun j => some (v j)) (((q.m : ℝ≥0∞)^q.S)⁻¹)
          (fun i hi A hA hAB => hfixed i hi v A hA hAB) E
          ((show H≤H⊔G from le_sup_left) _ hE) hEB
        rw [← hp]
        apply measure_congr
        filter_upwards [hactual] with z hz
        by_cases he : z∈E
        · simp (config := { iota := false }) only [Set.mem_inter_iff,Set.mem_ofPred_eq,he,true_and,hz (hEB z he)]
        · simp (config := { iota := false }) only [Set.mem_inter_iff,he,false_and]
    have freyaOptionParamMeas {Ω α β : Type} [MeasurableSpace Ω]
        [MeasurableSpace α] [MeasurableSpace β]
        (o : Ω → Option α) (ho : Measurable o) (b : Ω → β) (hb : Measurable b)
        (f : Ω × α → β) (hf : Measurable f) :
        Measurable (fun z => (o z).elim (b z) (fun a => f (z,a))) := by
      have he := (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr).comp ho
      have hs := ((hb.comp measurable_fst).sumElim hf).comp
        ((MeasurableEquiv.prodSumDistrib Ω Unit α).measurable.comp (measurable_id.prodMk he))
      convert hs using 1
      funext z
      dsimp only [Function.comp_def,id_eq]
      cases o z <;> rfl'
    let freyaListMeasSpace (α : Type) : MeasurableSpace (List α) := ⊤
    let freyaFullCode {d m n : ℕ} (s : FullState d m n) :=
      (s.original,s.remaining,s.point,s.sum,s.pending,s.clock,s.rows,s.nextID)
    let freyaDifferenceCode {d m n : ℕ} (s : DifferenceState d m n) :=
      (s.target,s.count,s.x,s.y,s.sum,s.pending,s.clock,s.rows,s.nextID)
    let freyaFullMeasSpace (d m n : ℕ) : MeasurableSpace (FullState d m n) :=
      MeasurableSpace.comap freyaFullCode inferInstance
    let freyaDifferenceMeasSpace (d m n : ℕ) : MeasurableSpace (DifferenceState d m n) :=
      MeasurableSpace.comap freyaDifferenceCode inferInstance
    have freyaFullCodeMeas {d m n : ℕ} : Measurable (@freyaFullCode d m n) :=
      Measurable.of_comap_le le_rfl
    have freyaDifferenceCodeMeas {d m n : ℕ} : Measurable (@freyaDifferenceCode d m n) :=
      Measurable.of_comap_le le_rfl
    have freyaJobCodeMeas {d m : ℕ} :
        Measurable (fun j : Job d m => (j.component,j.kind,j.started,j.id)) :=
      Measurable.of_comap_le le_rfl
    have freyaDispatchMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
        (kind : Ω → JobKind d) (clock : Ω → ℝ≥0) (id : Ω → ℕ)
        (label : Ω → Option (Fin m)) (hk : Measurable kind) (hc : Measurable clock)
        (hi : Measurable id) (hl : Measurable label) :
        Measurable (fun z => dispatch (kind z) (clock z) (id z) (label z)) := by
      have hb : Measurable (fun z : Ω × Fin m =>
          some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) := by
        apply freyaOptionSomeMeas.comp
        change Measurable[_,MeasurableSpace.comap
          (fun j : Job d m => (j.component,j.kind,j.started,j.id)) inferInstance]
          (fun z : Ω × Fin m => (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m))
        rw [measurable_comap_iff]
        exact (measurable_snd.prodMk ((hk.comp measurable_fst).prodMk
          ((hc.comp measurable_fst).prodMk (hi.comp measurable_fst))))
      have h := freyaOptionParamMeas label hl (fun _ => none) measurable_const
        (fun z : Ω × Fin m => some (⟨z.2,kind z.1,clock z.1,id z.1⟩ : Job d m)) hb
      convert h using 1
      funext z
      delta dispatch
      cases label z <;> rfl
    have freyaSelectedLabelFixedMeas {m : ℕ} (labels : List (Fin m)) (rem : List ℕ) :
        Measurable (fun row : ChoiceRow => selectedLabel labels rem row) := by
      let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
      cases rem with
      | nil => exact measurable_const
      | cons a rem =>
        let g := fun i : Fin (rem.length+1) => labels[(a::rem).get i]?
        have he : Measurable (fun row : ChoiceRow => row rem.length) := measurable_pi_apply rem.length
        have h := (measurable_of_countable g).comp he
        convert h using 1
        funext row
        delta selectedLabel chooseRemaining
        simp (config := { iota := false }) only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,dite_false,
          Option.bind_some]
        rfl
    have freyaFullInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
        (n : ℕ) (labels : List (Fin m)) (x : Ω → Space d) (clock : Ω → ℝ≥0)
        (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
        (hx : Measurable x) (hc : Measurable clock) (hr : Measurable rows) (hf : Measurable first) :
        Measurable (fun z => fullInitial n labels (x z) (clock z) (rows z) (first z)) := by
      have hp (i : Fin n) : Measurable (fun z =>
          dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
            (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))) :=
        freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hc (hf.add_const i.val)
          ((freyaSelectedLabelFixedMeas labels (List.range labels.length)).comp
            (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
      change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
      rw [measurable_comap_iff]
      change Measurable (fun z => (labels,List.range labels.length,x z,(0 : Space d),
        (fun i : Fin n => dispatch (Sum.inl (x z)) (clock z) (first z+i.val)
          (selectedLabel labels (List.range labels.length) (rows z (first z+i.val)))),
        clock z,rows z,first z+n))
      exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk
        (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n)))))))
    have freyaDifferenceInitialMeas {Ω : Type} [MeasurableSpace Ω] {d m : ℕ}
        (n S : ℕ) (x y : Ω → Space d) (clock : Ω → ℝ≥0)
        (rows : Ω → ℕ → ChoiceRow) (first : Ω → ℕ)
        (hx : Measurable x) (hy : Measurable y) (hc : Measurable clock)
        (hr : Measurable rows) (hf : Measurable first) :
        Measurable (fun z => differenceInitial (m:=m) n S (x z) (y z) (clock z) (rows z) (first z)) := by
      have hp (i : Fin n) : Measurable (fun z => if S=0 then none else
          dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
            (labelAt (rows z (first z+i.val)) m)) := by
        by_cases hS : S=0
        · simp (config := { iota := false }) only [hS,ite_true]; exact measurable_const
        · simp (config := { iota := false }) only [hS,ite_false]
          exact freyaDispatchMeas _ _ _ _ (measurable_inr.comp (hx.prodMk hy)) hc (hf.add_const i.val)
            ((freyaLabelAtMeas m).comp
              (freyaMeasurableSelect _ (hf.add_const i.val) _ (fun k => (measurable_pi_apply k).comp hr)))
      change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
      rw [measurable_comap_iff]
      change Measurable (fun z => (S,(0 : ℕ),x z,y z,(0 : Space d),
        (fun i : Fin n => if S=0 then none else dispatch (Sum.inr (x z,y z)) (clock z) (first z+i.val)
          (labelAt (rows z (first z+i.val)) m)),clock z,rows z,first z+n))
      exact measurable_const.prodMk (measurable_const.prodMk (hx.prodMk (hy.prodMk
        (measurable_const.prodMk ((Measurable.of_eval hp).prodMk (hc.prodMk (hr.prodMk (hf.add_const n))))))))
    let freyaFullReplyJob {d m n : ℕ} (s : FullState d m n)
        (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : FullState d m n := by
      classical
      exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
        let found := s.remaining.find? fun a => decide (s.original[a]?=some job.component)
        let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
        let sum := if found.isSome then s.sum+r.2.2.2 else s.sum
        let next := dispatch (Sum.inl s.point) r.2.2.1 s.nextID
          (selectedLabel s.original remaining (s.rows s.nextID))
        {s with
          remaining:=remaining
          sum:=sum
          pending:=Function.update s.pending r.1 next
          clock:=r.2.2.1
          nextID:=s.nextID+1}
      else s
    have freyaFullReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
        (s : Ω → FullState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
        (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
        Measurable (fun z => freyaFullReplyJob (s z) (r z) (job z)) := by
      classical
      let : MeasurableSingletonClass (Option ℕ) := freyaOptionSingleton
      let : MeasurableSingletonClass (Option (Fin m)) := freyaOptionSingleton
      have hcode := freyaFullCodeMeas.comp hs
      have hjcode := freyaJobCodeMeas.comp hj
      have ho : Measurable (fun z => (s z).original) := hcode.fst
      have hrem : Measurable (fun z => (s z).remaining) := hcode.snd.fst
      have hx : Measurable (fun z => (s z).point) := hcode.snd.snd.fst
      have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.fst
      have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.fst
      have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.fst
      have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.fst
      have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd
      let found := fun z => (s z).remaining.find? fun a => decide ((s z).original[a]?=some (job z).component)
      let rem := fun z => (found z).elim (s z).remaining (fun a => (s z).remaining.erase a)
      let sum := fun z => if (found z).isSome then (s z).sum+(r z).2.2.2 else (s z).sum
      let next := fun z => dispatch (Sum.inl (s z).point) (r z).2.2.1 (s z).nextID
        (selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID))
      have hf : Measurable found :=
        (measurable_of_countable (fun p : List (Fin m) × List ℕ × Fin m =>
          p.2.1.find? fun a => decide (p.1[a]?=some p.2.2))).comp (ho.prodMk (hrem.prodMk hjcode.fst))
      have hrem' : Measurable rem :=
        (measurable_of_countable (fun p : List ℕ × Option ℕ => p.2.elim p.1 (fun a => p.1.erase a))).comp
          (hrem.prodMk hf)
      have hsum' : Measurable sum := (hsum.add hr.snd.snd.snd).ite
        (((measurable_of_countable (fun o : Option ℕ => o.isSome)).comp hf) (measurableSet_singleton true)) hsum
      have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
        freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
      have hlabel : Measurable (fun z => selectedLabel (s z).original (rem z) ((s z).rows (s z).nextID)) :=
        freyaMeasurableSelect _ (ho.prodMk hrem') _
          (fun p => (freyaSelectedLabelFixedMeas p.1 p.2).comp hrow)
      have hnext : Measurable next := freyaDispatchMeas _ _ _ _ (measurable_inl.comp hx) hr.snd.snd.fst hid hlabel
      have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
        freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
      have hnew : Measurable (fun z => {s z with
          remaining:=rem z
          sum:=sum z
          pending:=Function.update (s z).pending (r z).1 (next z)
          clock:=(r z).2.2.1
          nextID:=(s z).nextID+1}) := by
        change Measurable[_,MeasurableSpace.comap freyaFullCode inferInstance] _
        rw [measurable_comap_iff]
        exact ho.prodMk (hrem'.prodMk (hx.prodMk (hsum'.prodMk
          (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1)))))))
      exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
        (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
    have freyaFullUpdateMeas {d m n : ℕ} :
        Measurable (fun z : FullState d m n × Reply d n => fullUpdate z.1 z.2) := by
      classical
      have hc := freyaFullCodeMeas (d:=d) (m:=m) (n:=n)
      have hsome : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
          ((z.1).pending z.2.1).elim z.1 (fun job => freyaFullReplyJob z.1 z.2 job)) := by
        have hp : Measurable (fun z : FullState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            z.1.pending z.2.1) :=
          freyaMeasurableSelect _ measurable_snd.fst _
            (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.fst.comp measurable_fst))
        exact freyaOptionParamMeas _ hp _ measurable_fst _
          (freyaFullReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
      have hoption : Measurable (fun z : FullState d m n × Reply d n =>
          z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
        freyaOptionParamMeas _ measurable_snd _ measurable_fst _
          (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
      have he : MeasurableSet {z : FullState d m n × Reply d n | z.1.remaining.isEmpty=true} :=
        ((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp
          (hc.snd.fst.comp measurable_fst)) (measurableSet_singleton true)
      have hh : Measurable (fun z : FullState d m n × Reply d n =>
          if z.1.remaining.isEmpty then z.1 else
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaFullReplyJob z.1 r job))) :=
        measurable_fst.ite he hoption
      convert hh using 1
      funext z
      delta fullUpdate
      dsimp only
      by_cases hempty : z.1.remaining.isEmpty=true
      · simp (config := { iota := false }) only [ite_eq_left hempty]
      · simp (config := { iota := false }) only [ite_eq_right hempty]
        cases hr : z.2 with
        | none => rfl
        | some r =>
          obtain ⟨i,id,t,value⟩ := r
          dsimp only [Option.elim_some]
          cases hp : z.1.pending i <;> rfl
    let freyaDifferenceReplyJob {d m n : ℕ} (s : DifferenceState d m n)
        (r : Fin n × ℕ × ℝ≥0 × Space d) (job : Job d m) : DifferenceState d m n := by
      classical
      exact if r.2.1=job.id ∧ s.clock≤r.2.2.1 then
        let next := dispatch (Sum.inr (s.x,s.y)) r.2.2.1 s.nextID (labelAt (s.rows s.nextID) m)
        {s with
          count:=s.count+1
          sum:=s.sum+r.2.2.2
          pending:=Function.update s.pending r.1 next
          clock:=r.2.2.1
          nextID:=s.nextID+1}
      else s
    have freyaDifferenceReplyJobMeas {Ω : Type} [MeasurableSpace Ω] {d m n : ℕ}
        (s : Ω → DifferenceState d m n) (r : Ω → Fin n × ℕ × ℝ≥0 × Space d) (job : Ω → Job d m)
        (hs : Measurable s) (hr : Measurable r) (hj : Measurable job) :
        Measurable (fun z => freyaDifferenceReplyJob (s z) (r z) (job z)) := by
      classical
      have hcode := freyaDifferenceCodeMeas.comp hs
      have hjcode := freyaJobCodeMeas.comp hj
      have ht : Measurable (fun z => (s z).target) := hcode.fst
      have hcount : Measurable (fun z => (s z).count) := hcode.snd.fst
      have hx : Measurable (fun z => (s z).x) := hcode.snd.snd.fst
      have hy : Measurable (fun z => (s z).y) := hcode.snd.snd.snd.fst
      have hsum : Measurable (fun z => (s z).sum) := hcode.snd.snd.snd.snd.fst
      have hpend : Measurable (fun z => (s z).pending) := hcode.snd.snd.snd.snd.snd.fst
      have hclock : Measurable (fun z => (s z).clock) := hcode.snd.snd.snd.snd.snd.snd.fst
      have hrows : Measurable (fun z => (s z).rows) := hcode.snd.snd.snd.snd.snd.snd.snd.fst
      have hid : Measurable (fun z => (s z).nextID) := hcode.snd.snd.snd.snd.snd.snd.snd.snd
      let next := fun z => dispatch (Sum.inr ((s z).x,(s z).y)) (r z).2.2.1 (s z).nextID
        (labelAt ((s z).rows (s z).nextID) m)
      have hrow : Measurable (fun z => (s z).rows (s z).nextID) :=
        freyaMeasurableSelect _ hid _ (fun k => (measurable_pi_apply k).comp hrows)
      have hnext : Measurable next := freyaDispatchMeas _ _ _ _
        (measurable_inr.comp (hx.prodMk hy)) hr.snd.snd.fst hid ((freyaLabelAtMeas m).comp hrow)
      have hpending : Measurable (fun z => Function.update (s z).pending (r z).1 (next z)) :=
        freyaMeasurableSelect _ hr.fst _ (fun i => (measurable_update' (a:=i)).comp (hpend.prodMk hnext))
      have hnew : Measurable (fun z => {s z with
          count:=(s z).count+1
          sum:=(s z).sum+(r z).2.2.2
          pending:=Function.update (s z).pending (r z).1 (next z)
          clock:=(r z).2.2.1
          nextID:=(s z).nextID+1}) := by
        change Measurable[_,MeasurableSpace.comap freyaDifferenceCode inferInstance] _
        rw [measurable_comap_iff]
        exact ht.prodMk ((hcount.add_const 1).prodMk (hx.prodMk (hy.prodMk ((hsum.add hr.snd.snd.snd).prodMk
          (hpending.prodMk (hr.snd.snd.fst.prodMk (hrows.prodMk (hid.add_const 1))))))))
      exact hnew.ite ((measurableSet_eq_fun hr.snd.fst hjcode.snd.snd.snd).inter
        (measurableSet_le (α:=ℝ≥0) hclock hr.snd.snd.fst)) hs
    have freyaDifferenceUpdateMeas {d m n : ℕ} :
        Measurable (fun z : DifferenceState d m n × Reply d n => differenceUpdate z.1 z.2) := by
      classical
      have hc := freyaDifferenceCodeMeas (d:=d) (m:=m) (n:=n)
      have hsome : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
          ((z.1).pending z.2.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 z.2 job)) := by
        have hp : Measurable (fun z : DifferenceState d m n × (Fin n × ℕ × ℝ≥0 × Space d) =>
            z.1.pending z.2.1) :=
          freyaMeasurableSelect _ measurable_snd.fst _
            (fun i => (measurable_pi_apply i).comp (hc.snd.snd.snd.snd.snd.fst.comp measurable_fst))
        exact freyaOptionParamMeas _ hp _ measurable_fst _
          (freyaDifferenceReplyJobMeas _ _ _ measurable_fst.fst measurable_fst.snd measurable_snd)
      have hoption : Measurable (fun z : DifferenceState d m n × Reply d n =>
          z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
        freyaOptionParamMeas _ measurable_snd _ measurable_fst _
          (hsome.comp (measurable_fst.fst.prodMk measurable_snd))
      have he : MeasurableSet {z : DifferenceState d m n × Reply d n | z.1.target≤z.1.count} :=
        measurableSet_le (hc.fst.comp measurable_fst) (hc.snd.fst.comp measurable_fst)
      have hh : Measurable (fun z : DifferenceState d m n × Reply d n =>
          if z.1.target≤z.1.count then z.1 else
            z.2.elim z.1 (fun r => (z.1.pending r.1).elim z.1 (fun job => freyaDifferenceReplyJob z.1 r job))) :=
        measurable_fst.ite he hoption
      convert hh using 1
      funext z
      delta differenceUpdate
      dsimp only
      by_cases hstop : z.1.target≤z.1.count
      · simp (config := { iota := false }) only [ite_eq_left hstop]
      · simp (config := { iota := false }) only [ite_eq_right hstop]
        cases hr : z.2 with
        | none => rfl
        | some r =>
          obtain ⟨i,id,t,value⟩ := r
          dsimp only [Option.elim_some]
          cases hp : z.1.pending i <;> rfl
    let freyaPhaseCode {d m n : ℕ} (p : Phase d m n) :
        Unit ⊕ ((Bool × FullState d m n) ⊕ DifferenceState d m n) :=
      p.casesOn (fun b c => Sum.inr (Sum.inl (b,c))) (fun c => Sum.inr (Sum.inr c)) (Sum.inl ())
    let freyaPhaseMeasSpace (d m n : ℕ) : MeasurableSpace (Phase d m n) :=
      MeasurableSpace.comap freyaPhaseCode inferInstance
    let freyaStateCode {q : Raw} (s : State q) :=
      (s.seed,s.iteration,s.x,s.g,s.selected,s.clock,s.nextID,s.phase)
    let freyaStateMeasSpace (q : Raw) : MeasurableSpace (State q) :=
      MeasurableSpace.comap freyaStateCode inferInstance
    have freyaPhaseCodeMeas {d m n : ℕ} : Measurable (@freyaPhaseCode d m n) :=
      Measurable.of_comap_le le_rfl
    have freyaStateCodeMeas (q : Raw) : Measurable (@freyaStateCode q) :=
      Measurable.of_comap_le le_rfl
    have freyaPhaseFullMeas {d m n : ℕ} :
        Measurable (fun z : Bool × FullState d m n => Phase.full z.1 z.2) := by
      change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
      rw [measurable_comap_iff]
      exact measurable_inr.comp measurable_inl
    have freyaPhaseDifferenceMeas {d m n : ℕ} :
        Measurable (Phase.difference : DifferenceState d m n → Phase d m n) := by
      change Measurable[_,MeasurableSpace.comap freyaPhaseCode inferInstance] _
      rw [measurable_comap_iff]
      exact measurable_inr.comp measurable_inr
    have freyaPhaseParamMeas {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {d m n : ℕ}
        (p : Ω → Phase d m n) (hp : Measurable p) (b : Ω → β) (hb : Measurable b)
        (full : Ω × (Bool × FullState d m n) → β) (hfull : Measurable full)
        (diff : Ω × DifferenceState d m n → β) (hdiff : Measurable diff) :
        Measurable (fun z => (p z).casesOn (motive := fun _ => β) (fun first c => full (z,first,c))
          (fun c => diff (z,c)) (b z)) := by
      have hi := (hfull.sumElim hdiff).comp
        (MeasurableEquiv.prodSumDistrib Ω (Bool × FullState d m n) (DifferenceState d m n)).measurable
      have ho := ((hb.comp measurable_fst).sumElim hi).comp
        (MeasurableEquiv.prodSumDistrib Ω Unit ((Bool × FullState d m n) ⊕ DifferenceState d m n)).measurable
      have h := ho.comp (measurable_id.prodMk (freyaPhaseCodeMeas.comp hp))
      convert h using 1
      funext z
      dsimp only [Function.comp_def,id_eq]
      cases p z <;> rfl'
    have freyaStateConstructMeas {Ω : Type} [MeasurableSpace Ω] (q : Raw)
        (seed : Ω → Seed q.K) (it : Ω → ℕ) (x g selected : Ω → Space q.d)
        (clock : Ω → ℝ≥0) (id : Ω → ℕ) (phase : Ω → Phase q.d q.m q.n)
        (hseed : Measurable seed) (hit : Measurable it) (hx : Measurable x) (hg : Measurable g)
        (hselected : Measurable selected) (hc : Measurable clock) (hid : Measurable id) (hp : Measurable phase) :
        Measurable (fun z => (⟨seed z,it z,x z,g z,selected z,clock z,id z,phase z⟩ : State q)) := by
      change Measurable[_,MeasurableSpace.comap freyaStateCode inferInstance] _
      rw [measurable_comap_iff]
      exact hseed.prodMk (hit.prodMk (hx.prodMk (hg.prodMk (hselected.prodMk (hc.prodMk (hid.prodMk hp))))))
    have freyaPageInitialMeas (q : Raw) : Measurable (initial q) := by
      have hp : Measurable (fun seed : Seed q.K =>
          if q.m=0 ∨ q.n=0 ∨ q.K=0 then (Phase.halted : Phase q.d q.m q.n) else
            Phase.full true (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))) := by
        by_cases hbad : q.m=0 ∨ q.n=0 ∨ q.K=0
        · simp (config := { iota := false }) only [hbad,ite_true]; exact measurable_const
        · simp (config := { iota := false }) only [hbad,ite_false]
          exact freyaPhaseFullMeas.comp (measurable_const.prodMk
            (freyaFullInitialMeas q.n (List.ofFn id) (fun _ => q.x0) (fun _ => 0)
              (fun seed : Seed q.K => seed.1 0) (fun _ => 0) measurable_const measurable_const
              ((measurable_pi_apply 0).comp measurable_fst) measurable_const))
      exact freyaStateConstructMeas q id (fun _ => 0) (fun _ => q.x0) (fun _ => 0) (fun _ => q.x0)
        (fun _ => 0) (fun _ => q.n) _ measurable_id measurable_const measurable_const measurable_const
          measurable_const measurable_const measurable_const hp
    have freyaPageAdvanceMeas (q : Raw) : Measurable (advance q) := by
      classical
      have hc := freyaStateCodeMeas q
      have hseed : Measurable (fun s : State q => s.seed) := hc.fst
      have hit : Measurable (fun s : State q => s.iteration) := hc.snd.fst
      have hx : Measurable (fun s : State q => s.x) := hc.snd.snd.fst
      have hg : Measurable (fun s : State q => s.g) := hc.snd.snd.snd.fst
      have hsel : Measurable (fun s : State q => s.selected) := hc.snd.snd.snd.snd.fst
      have hclock : Measurable (fun s : State q => s.clock) := hc.snd.snd.snd.snd.snd.fst
      have hid : Measurable (fun s : State q => s.nextID) := hc.snd.snd.snd.snd.snd.snd.fst
      let x := fun s : State q => s.x-q.η • s.g
      let batch := fun s : State q => s.iteration+1
      have hnewx : Measurable x := hx.sub (hg.const_smul q.η)
      have hbatch : Measurable batch := hit.add_const 1
      have hrows : Measurable (fun s : State q => s.seed.1 (batch s)) :=
        freyaMeasurableSelect _ hbatch _ (fun k => (measurable_pi_apply k).comp hseed.fst)
      have hrefresh : Measurable (fun s : State q => refreshAt s.seed s.iteration) :=
        freyaMeasurableSelect _ hit _ (fun k => (measurable_pi_apply k).comp hseed.snd.fst)
      have hfull := (freyaPhaseFullMeas (m:=q.m)).comp ((measurable_const (a:=false)).prodMk
        (freyaFullInitialMeas (m:=q.m) q.n (List.ofFn id) x (fun s => s.clock) _ (fun s => s.nextID)
          hnewx hclock hrows hid))
      have hdiff := freyaPhaseDifferenceMeas.comp
        (freyaDifferenceInitialMeas (m:=q.m) q.n q.S x (fun s => s.x) (fun s => s.clock) _
          (fun s => s.nextID) hnewx hx hclock hrows hid)
      have hphase : Measurable (fun s : State q => if refreshAt s.seed s.iteration then
          Phase.full false (fullInitial q.n (List.ofFn id) (x s) s.clock (s.seed.1 (batch s)) s.nextID)
        else Phase.difference (differenceInitial q.n q.S (x s) s.x s.clock (s.seed.1 (batch s)) s.nextID)) :=
        hfull.ite (hrefresh (measurableSet_singleton true)) hdiff
      have hindex : Measurable (fun s : State q => (outputIndex s.seed).val) :=
        (measurable_of_countable (fun i : Fin (max 1 q.K) => i.val)).comp hseed.snd.snd
      have hselected : Measurable (fun s : State q =>
          if (outputIndex s.seed).val=batch s then x s else s.selected) :=
        hnewx.ite (measurableSet_eq_fun hindex hbatch) hsel
      have hnext := freyaStateConstructMeas q _ batch x _ _ _ _ _
        hseed hbatch hnewx hg hselected hclock (hid.add_const q.n) hphase
      have hstop := freyaStateConstructMeas q _ _ _ _ _ _ _ (fun _ => Phase.halted)
        hseed hit hx hg hsel hclock hid measurable_const
      exact hstop.ite (measurableSet_le measurable_const hit) hnext
    have freyaPageUpdateMeas (q : Raw) :
        Measurable (fun z : State q × Reply q.d q.n => update q z.1 z.2) := by
      classical
      have hfull : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
          let c := fullUpdate z.2.2 z.1.2
          let s := {z.1.1 with
            clock:=c.clock
            nextID:=c.nextID
            phase:=Phase.full z.2.1 c}
          if c.remaining.isEmpty then advance q {s with g:=fullResult c} else s) := by
        have hs : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
        have hu : Measurable (fun z : (State q × Reply q.d q.n) × (Bool × FullState q.d q.m q.n) =>
            fullUpdate z.2.2 z.1.2) := freyaFullUpdateMeas.comp (measurable_snd.snd.prodMk measurable_fst.snd)
        have hc := freyaFullCodeMeas.comp hu
        have hp := freyaPhaseFullMeas.comp (measurable_snd.fst.prodMk hu)
        have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
          hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
          hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp
        have hg := ((measurable_of_countable (fun l : List (Fin q.m) => (l.length : ℝ)⁻¹)).comp hc.fst).smul
          hc.snd.snd.snd.fst
        have hnext := (freyaPageAdvanceMeas q).comp
          (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd hp)
        exact hnext.ite (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst)
          (measurableSet_singleton true)) hbase
      have hdiff : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
          let c := differenceUpdate z.2 z.1.2
          let s := {z.1.1 with
            clock:=c.clock
            nextID:=c.nextID
            phase:=Phase.difference c}
          if c.target≤c.count then advance q {s with g:=s.g+differenceResult c} else s) := by
        have hs : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            freyaStateCode z.1.1) := (freyaStateCodeMeas q).comp measurable_fst.fst
        have hu : Measurable (fun z : (State q × Reply q.d q.n) × DifferenceState q.d q.m q.n =>
            differenceUpdate z.2 z.1.2) := freyaDifferenceUpdateMeas.comp (measurable_snd.prodMk measurable_fst.snd)
        have hc := freyaDifferenceCodeMeas.comp hu
        have hp := freyaPhaseDifferenceMeas.comp hu
        have hbase := freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
          hs.snd.snd.fst hs.snd.snd.snd.fst hs.snd.snd.snd.snd.fst
          hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp
        have hg := hs.snd.snd.snd.fst.add
          (((measurable_of_countable (fun a : ℕ => (a : ℝ)⁻¹)).comp hc.fst).smul hc.snd.snd.snd.snd.fst)
        have hnext := (freyaPageAdvanceMeas q).comp
          (freyaStateConstructMeas q _ _ _ _ _ _ _ _ hs.fst hs.snd.fst
            hs.snd.snd.fst hg hs.snd.snd.snd.snd.fst
            hc.snd.snd.snd.snd.snd.snd.fst hc.snd.snd.snd.snd.snd.snd.snd.snd hp)
        exact hnext.ite (measurableSet_le hc.fst hc.snd.fst) hbase
      have h := freyaPhaseParamMeas (fun z : State q × Reply q.d q.n => z.1.phase)
        (((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd).comp measurable_fst)
        Prod.fst measurable_fst _ hfull _ hdiff
      convert h using 1
      funext z
      delta update
      cases z.1.phase <;> rfl
    have freyaPendingRequestMeas {d m n : ℕ} :
        Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) => pendingRequest z.1 z.2) := by
      classical
      have hc : Measurable (fun z : ℝ≥0 × (Fin n → Option (Job d m)) =>
          (⟨z.1,z.2⟩ : Request d m n)) := by
        change Measurable[_,MeasurableSpace.comap (fun r : Request d m n => (r.clock,r.pending)) inferInstance] _
        rw [measurable_comap_iff]
        exact measurable_id
      have hsome := freyaOptionSomeMeas.comp hc
      have hn : MeasurableSet {o : Option (Job d m) | o ≠ none} := by
        have hi := freyaDevelopmentOptionElimMeas false (fun _ : Job d m => true) measurable_const
        convert hi (measurableSet_singleton true) using 1
        ext o
        cases o <;> simp (config := { iota := false })
      have he : MeasurableSet {z : ℝ≥0 × (Fin n → Option (Job d m)) | ∃ i, z.2 i ≠ none} := by
        convert MeasurableSet.iUnion (fun i : Fin n => hn.preimage ((measurable_pi_apply i).comp measurable_snd)) using 1
        ext z
        simp (config := { iota := false })
      exact hsome.ite he measurable_const
    have freyaPageQueryMeas (q : Raw) : Measurable (query q) := by
      classical
      have hfull : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) =>
          if z.2.2.remaining.isEmpty then none else pendingRequest z.2.2.clock z.2.2.pending) := by
        have hc : Measurable (fun z : State q × (Bool × FullState q.d q.m q.n) => freyaFullCode z.2.2) :=
          freyaFullCodeMeas.comp measurable_snd.snd
        exact measurable_const.ite
          (((measurable_of_countable (fun l : List ℕ => l.isEmpty)).comp hc.snd.fst) (measurableSet_singleton true))
          (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.fst))
      have hdiff : Measurable (fun z : State q × DifferenceState q.d q.m q.n =>
          if z.2.target≤z.2.count then none else pendingRequest z.2.clock z.2.pending) := by
        have hc : Measurable (fun z : State q × DifferenceState q.d q.m q.n => freyaDifferenceCode z.2) :=
          freyaDifferenceCodeMeas.comp measurable_snd
        exact measurable_const.ite (measurableSet_le hc.fst hc.snd.fst)
          (freyaPendingRequestMeas.comp (hc.snd.snd.snd.snd.snd.snd.fst.prodMk hc.snd.snd.snd.snd.snd.fst))
      have hp := freyaPhaseParamMeas (fun s : State q => s.phase)
        ((freyaStateCodeMeas q).snd.snd.snd.snd.snd.snd.snd)
        (fun _ => (none : Option (Request q.d q.m q.n))) measurable_const _ hfull _ hdiff
      have h : Measurable (fun s : State q => ((0 : Fin 1), s.phase.casesOn
          (motive:=fun _ => Option (Request q.d q.m q.n))
          (fun _ c => if c.remaining.isEmpty then none else pendingRequest c.clock c.pending)
          (fun c => if c.target≤c.count then none else pendingRequest c.clock c.pending) none)) :=
        measurable_const.prodMk hp
      convert h using 1
      funext s
      delta query
      cases s.phase <;> rfl
    have freyaPageTraceMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (k : ℕ) :
        Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => trace q O z.1 z.2 k) := by
      exact (measurable_trajectory q O hservice.1.2 (freyaPageInitialMeas q)
        (freyaPageUpdateMeas q) (freyaPageQueryMeas q) k).1
    have freyaCompletedFromMeas {d m n : ℕ} :
        Measurable (fun z : Option (Request d m n) × Reply d n =>
          z.1.elim none (fun r => z.2.elim none (fun a =>
            (r.pending a.1).bind fun job => if job.id=a.2.1 then some job else none))) := by
      classical
      let Ω := Option (Request d m n) × Reply d n
      have hj : Measurable (fun z : ((Ω × Request d m n) × (Fin n × ℕ × ℝ≥0 × Space d)) × Job d m =>
          if z.2.id=z.1.2.2.1 then some z.2 else none) :=
        (freyaOptionSomeMeas.comp measurable_snd).ite
          (measurableSet_eq_fun (freyaJobCodeMeas.snd.snd.snd.comp measurable_snd) measurable_fst.snd.snd.fst)
          measurable_const
      have hr : Measurable (fun r : Request d m n => (r.clock,r.pending)) :=
        Measurable.of_comap_le le_rfl
      have hp : Measurable (fun z : (Ω × Request d m n) × (Fin n × ℕ × ℝ≥0 × Space d) => z.1.2.pending z.2.1) :=
        freyaMeasurableSelect _ measurable_snd.fst _
          (fun i => (measurable_pi_apply i).comp (hr.snd.comp measurable_fst.snd))
      have hi := freyaOptionParamMeas _ hp (fun _ => (none : Option (Job d m))) measurable_const _ hj
      have hm := freyaOptionParamMeas (fun z : Ω × Request d m n => z.1.2) measurable_fst.snd
        (fun _ => (none : Option (Job d m))) measurable_const _ hi
      have ho := freyaOptionParamMeas (fun z : Ω => z.1) measurable_fst
        (fun _ => (none : Option (Job d m))) measurable_const _ hm
      convert ho using 1
      funext z
      obtain ⟨o,r⟩ := z
      dsimp only
      cases o with
      | none => cases r <;> rfl
      | some req =>
        cases r with
        | none => rfl
        | some a =>
          obtain ⟨i,id,t,v⟩ := a
          dsimp only [Option.elim_some]
          cases req.pending i <;> rfl
    have freyaPageCompletedLabelsMeas (q : Raw) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ)
        (hcall : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
          (batchStartCall q O z.1 z.2 batch).getD 0)) :
        Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => completedLabels q O z.1 z.2 batch) := by
      classical
      apply Measurable.of_eval
      intro j
      let call := fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
        (batchStartCall q O z.1 z.2 batch).getD 0+j.val
      have hcallj : Measurable call := hcall.add_const j.val
      have htrace := freyaMeasurableSelect call hcallj _ (freyaPageTraceMeas q f τ O hservice)
      have hquery := (freyaPageQueryMeas q).comp htrace
      have hreply : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
          replyAt q O z.1 z.2 (call z) (query q (trace q O z.1 z.2 (call z)))) :=
        freyaMeasurableSelect call hcallj _ (fun k => measurable_replyAt q O hservice.1.2 (freyaPageInitialMeas q) (freyaPageUpdateMeas q)
            (freyaPageQueryMeas q) k measurable_id hquery)
      have hjob := freyaCompletedFromMeas.comp (hquery.snd.prodMk hreply)
      have hactual : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => completedJob q O z.1 z.2 batch j) := by
        convert hjob using 1
        funext z
        dsimp only [Function.comp_def,completedJob,call]
        generalize (query q (trace q O z.1 z.2 (call z))).2 = req
        generalize replyAt q O z.1 z.2 (call z) (query q (trace q O z.1 z.2 (call z))) = rep
        cases req <;> cases rep <;> rfl
      have hlabel := freyaDevelopmentOptionElimMeas (none : Option (Fin q.m))
        (fun job : Job q.d q.m => some job.component) (freyaOptionSomeMeas.comp freyaJobCodeMeas.fst)
      have h := hlabel.comp hactual
      convert h using 1
      funext z
      change (completedJob q O z.1 z.2 batch j).map (fun job => job.component) =
        (completedJob q O z.1 z.2 batch j).elim none (fun job => some job.component)
      cases completedJob q O z.1 z.2 batch j <;> rfl
    exact ⟨freyaPageCompletedLabelsMeas q f τ O hservice batch
      ((freyaPageCallHistoryMeas q O batch).mono ((hind batch).1) le_rfl),
      freyaPageCompletedLabelLaw q hm hn hS hK f τ O hservice hind batch⟩


theorem difference_average (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
    (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0, r)))
    (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
    (hinvoke : invocation q O seed ω batch = some (false, x, y, clock, firstID)) :
    batchResult q O seed ω batch = (q.S : ℝ)⁻¹ •
      (∑ j : Fin q.S, (completedLabels q O seed ω batch j).elim 0
        (fun i => gradient (f i) x - gradient (f i) y)) := by
  have _hK := hK
  set_option maxHeartbeats 1600000 in
  open scoped BigOperators ENNReal NNReal in
  open LongTails.Algorithms.FreyaPage in
    have freyaPageAdvanceSeed (q : Raw) (s : State q) : (advance q s).seed = s.seed := by
      delta advance
      split <;> rfl
    have freyaPageUpdateSeed (q : Raw) (s : State q) (reply : Reply q.d q.n) :
        (update q s reply).seed = s.seed := by
      delta update
      cases hs : s.phase with
      | halted => rfl
      | full first c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
      | difference c =>
        dsimp only
        split
        · exact freyaPageAdvanceSeed q _
        · rfl
    have freyaPageTraceSeed (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) :
        (trace q O seed ω k).seed = seed := by
      induction k with
      | zero => rfl
      | succ k ih =>
        change (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k)))).seed = seed
        rw [freyaPageUpdateSeed,ih]
    have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
        (h : (List.range N).find? p = some k) :
        k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
      obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
      simp only [List.length_range,List.getElem_range] at hi hik hprev
      subst i
      refine ⟨hi,hp,?_⟩
      intro r hr htrue
      have hh := hprev r hr
      rw [htrue] at hh
      contradiction
    have freyaPageBatchStartFacts (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (h : batchStartCall q O seed ω batch = some call) :
        call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
          active (trace q O seed ω call) = true ∧
          ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
      delta batchStartCall at h
      obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
      obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
      refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
      intro r hr hh
      apply hprev r hr
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
    have freyaPageDifferenceInvocation (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
        (x y : Space q.d) (clock : ℝ≥0)
        (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
        ∃ call c, batchStartCall q O seed ω batch = some call ∧
          (trace q O seed ω call).phase = Phase.difference c ∧
          c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
      delta invocation at h
      cases hs : batchStartCall q O seed ω batch with
      | none => rw [hs] at h; cases h
      | some call =>
        rw [hs] at h
        dsimp only [Option.bind] at h
        cases hp : (trace q O seed ω call).phase with
        | halted => rw [hp] at h; cases h
        | full first c => rw [hp] at h; cases h
        | difference c =>
          rw [hp] at h
          have heq := Option.some.inj h
          have hfields : c.x=x ∧ c.y=y ∧ c.clock=clock ∧ c.nextID-q.n=firstID := by
            simpa only [Prod.mk.injEq,true_and] using heq
          exact ⟨call,c,rfl,hp,hfields⟩
    have freyaPageDifferenceEntryAdvance (q : Raw) (s : State q) (reply : Reply q.d q.n)
        (c : DifferenceState q.d q.m q.n) (hphase : (update q s reply).phase = Phase.difference c)
        (hfresh : ¬(s.iteration = (update q s reply).iteration ∧ active s = true)) :
        ∃ t : State q, t.seed = s.seed ∧ advance q t = update q s reply := by
      delta update at hphase hfresh ⊢
      cases hs : s.phase with
      | halted =>
        rw [hs] at hphase
        change s.phase = Phase.difference c at hphase
        rw [hs] at hphase
        cases hphase
      | full first old =>
        rw [hs] at hphase hfresh
        dsimp only at hphase hfresh ⊢
        by_cases he : (fullUpdate old reply).remaining.isEmpty = true
        · rw [ite_eq_left he]
          exact ⟨{s with
            g := fullResult (fullUpdate old reply)
            clock := (fullUpdate old reply).clock
            nextID := (fullUpdate old reply).nextID
            phase := Phase.full first (fullUpdate old reply)},rfl,rfl⟩
        · rw [ite_eq_right he] at hphase
          cases hphase
      | difference old =>
        rw [hs] at hphase hfresh
        dsimp only at hphase hfresh ⊢
        by_cases he : (differenceUpdate old reply).target ≤ (differenceUpdate old reply).count
        · rw [ite_eq_left he]
          exact ⟨{s with
            g := s.g+differenceResult (differenceUpdate old reply)
            clock := (differenceUpdate old reply).clock
            nextID := (differenceUpdate old reply).nextID
            phase := Phase.difference (differenceUpdate old reply)},rfl,rfl⟩
        · apply False.elim
          rw [ite_eq_right he] at hfresh
          apply hfresh
          constructor
          · rfl
          · delta active
            rw [hs]
    have freyaPageAdvanceDifference (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n)
        (h : (advance q s).phase = Phase.difference c) :
        (advance q s).iteration = s.iteration+1 ∧
          c = differenceInitial q.n q.S (s.x-q.η • s.g) s.x s.clock
            (s.seed.1 (s.iteration+1)) s.nextID := by
      delta advance at h ⊢
      split at h
      · contradiction
      · rename_i hn
        rw [ite_eq_right hn]
        dsimp only at h ⊢
        split at h
        · contradiction
        · exact ⟨rfl,(Phase.difference.inj h).symm⟩
    have freyaPageFreshDifference (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch firstID : ℕ)
        (x y : Space q.d) (clock : ℝ≥0)
        (h : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
        ∃ call, batchStartCall q O seed ω batch = some call ∧
          (trace q O seed ω call).phase = Phase.difference
            (differenceInitial q.n q.S x y clock (seed.1 batch) firstID) := by
      obtain ⟨call,c,hstart,hphase,hx,hy,hclock,hid⟩ :=
        freyaPageDifferenceInvocation q O seed ω batch firstID x y clock h
      have hfacts := freyaPageBatchStartFacts q O seed ω batch call hstart
      cases call with
      | zero =>
        change (initial q seed).phase = Phase.difference c at hphase
        delta initial at hphase
        dsimp only at hphase
        split at hphase <;> contradiction
      | succ k =>
        have hprev := hfacts.2.2.2 k (Nat.lt_succ_self k)
        rw [← hfacts.2.1] at hprev
        obtain ⟨t,htseed,ht⟩ := freyaPageDifferenceEntryAdvance q
          (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))) c hphase hprev
        have httrace : advance q t = trace q O seed ω (k+1) := ht
        have htc : (advance q t).phase = Phase.difference c := by rw [httrace]; exact hphase
        obtain ⟨hit,hc⟩ := freyaPageAdvanceDifference q t c htc
        have hbatch : t.iteration+1 = batch := by rw [← hit,httrace]; exact hfacts.2.1
        have hseed : t.seed = seed := htseed.trans (freyaPageTraceSeed q O seed ω k)
        rw [hc] at hx hy hclock hid
        dsimp only [differenceInitial] at hx hy hclock hid
        have hfirst : t.nextID = firstID := by omega
        refine ⟨k+1,hstart,?_⟩
        rw [hphase,hc,hx,hy,hclock,hseed,hbatch,hfirst]
    have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
        (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
            r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
        (ha : s.count < s.target)
        (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
          (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
        ∃ i job c next,
          s.pending i = some job ∧
          differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
          reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
          s.clock ≤ c ∧
          next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
          labelAt (s.rows s.nextID) m = some next.component ∧
          differenceUpdate s (reply (differenceQuery s)) =
            {s with
              count := s.count+1
              sum := s.sum+jobValue f job
              pending := Function.update s.pending i (some next)
              clock := c
              nextID := s.nextID+1} ∧
          ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
            old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
      classical
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := by
        refine ⟨?_,?_⟩
        · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
          exact ⟨⟨0,hn⟩,job,hj⟩
        · intro i job hj
          obtain ⟨old,hold,hs,ht,_⟩ := hp i
          have heq : job=old := Option.some.inj (hj.symm.trans hold)
          subst old
          exact ⟨hs,ht⟩
      have hquery : differenceQuery s = some r := by
        delta differenceQuery
        rw [ite_eq_right (by omega)]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          change s.pending i=some job at hj
          exact ⟨i,by rw [hj]; simp⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
      change s.pending i=some job at hjob
      change s.clock≤c at hclock
      obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
        delta labelAt
        simp only [hm,dite_true]
        exact ⟨_,rfl⟩
      let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
      refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
      · rw [hquery]; exact hreply
      · rw [hquery,hreply]
        delta differenceUpdate
        rw [ite_eq_right (by omega)]
        dsimp only
        rw [hjob]
        dsimp only
        rw [ite_eq_left (And.intro rfl hclock)]
        delta dispatch
        rw [hb]
        rfl
      · intro k
        by_cases hk : k=i
        · subst k
          refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
          change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
          exact le_add_of_nonneg_right zero_le
        · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
          refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
          rw [Function.update_of_ne hk]
          exact hold
    have freyaPageDifferenceQuery (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
        query q s = (0,differenceQuery c) := by
      delta query
      rw [h]
      rfl
    have freyaPageDifferenceContinue (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n) (reply : Reply q.d q.n)
        (h : s.phase = Phase.difference c)
        (ha : (differenceUpdate c reply).count < (differenceUpdate c reply).target) :
        (update q s reply).phase = Phase.difference (differenceUpdate c reply) ∧
          (update q s reply).iteration = s.iteration := by
      delta update
      rw [h]
      dsimp only
      rw [ite_eq_right (by omega)]
      exact ⟨rfl,rfl⟩
    have freyaPageCompletedJobEq (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ) (j : Fin q.S)
        (hstart : batchStartCall q O seed ω batch = some call)
        (c : DifferenceState q.d q.m q.n)
        (hphase : (trace q O seed ω (call+j.val)).phase = Phase.difference c)
        (hq : differenceQuery c = some ⟨c.clock,c.pending⟩)
        (i : Fin q.n) (job : Job q.d q.m) (time : ℝ≥0) (value : Space q.d)
        (hj : c.pending i = some job)
        (hr : replyAt q O seed ω (call+j.val) (0,differenceQuery c) =
          some (i,job.id,time,value)) : completedJob q O seed ω batch j = some job := by
      have hquery := freyaPageDifferenceQuery q _ c hphase
      delta completedJob
      rw [hstart]
      dsimp only [Option.getD]
      rw [hquery]
      dsimp only
      rw [hr,hq]
      dsimp only
      rw [hj]
      dsimp only [Option.bind]
      rw [ite_eq_left rfl]
    have freyaPageBatchProgress (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
        (hS : 0 < q.S) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (batch firstID call : ℕ) (x y : Space q.d) (clock : ℝ≥0)
        (hstart : batchStartCall q O seed ω batch = some call)
        (hphase : (trace q O seed ω call).phase = Phase.difference
          (differenceInitial q.n q.S x y clock (seed.1 batch) firstID)) :
        let D := fun k : ℕ => if hk : k < q.S then
          (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
            (fun i => gradient (f i) x-gradient (f i) y) else 0
        ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
          (trace q O seed ω (call+a)).phase = Phase.difference c ∧
          (trace q O seed ω (call+a)).iteration = batch ∧
          c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
          c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
          ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
            batchLabels q seed batch job.id=some job.component := by
      classical
      dsimp only
      let D := fun k : ℕ => if hk : k < q.S then
          (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
            (fun i => gradient (f i) x-gradient (f i) y) else 0
      change ∀ a, a < q.S → ∃ c : DifferenceState q.d q.m q.n,
          (trace q O seed ω (call+a)).phase = Phase.difference c ∧
          (trace q O seed ω (call+a)).iteration = batch ∧
          c.target=q.S ∧ c.count=a ∧ c.x=x ∧ c.y=y ∧ c.rows=seed.1 batch ∧
          c.nextID=firstID+q.n+a ∧ c.sum=∑ k ∈ Finset.range a, D k ∧
          ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (x,y) ∧
            batchLabels q seed batch job.id=some job.component
      intro a
      induction a with
      | zero =>
        intro _
        refine ⟨differenceInitial q.n q.S x y clock (seed.1 batch) firstID,?_,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
        · simpa only [Nat.add_zero] using hphase
        · simpa only [Nat.add_zero] using (freyaPageBatchStartFacts q O seed ω batch call hstart).2.1
        · change firstID+q.n=firstID+q.n+0
          omega
        · exact (Finset.sum_range_zero D).symm
        · intro i
          obtain ⟨b,hb⟩ : ∃ b : Fin q.m, labelAt (seed.1 batch (firstID+i.val)) q.m=some b := by
            delta labelAt
            simp only [hm,dite_true]
            exact ⟨_,rfl⟩
          let job : Job q.d q.m := ⟨b,Sum.inr (x,y),clock,firstID+i.val⟩
          refine ⟨job,?_,le_rfl,?_,rfl,hb⟩
          · change (if q.S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
              (labelAt (seed.1 batch (firstID+i.val)) q.m))=some job
            rw [ite_eq_right (by omega),hb]
            rfl
          · exact le_add_of_nonneg_right zero_le
      | succ a ih =>
        intro ha
        have haS : a<q.S := by omega
        obtain ⟨c,hc,hit,htarget,hcount,hx,hy,hrows,hid,hsum,hpending⟩ := ih haS
        have hp : ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
          intro i
          obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
          rw [hx,hy]
          exact ⟨job,hj,hs,ht,hk⟩
        obtain ⟨i,job,time,next,hjob,hquery,hreply,hclock,hnid,hnkind,hnstart,hnlabel,hnext,hpnext⟩ :=
          freyaDifferenceLiveStep hm hn c f τ
            (fun r => replyAt q O seed ω (call+a) (0,r))
            (hservice (call+a)).2 (by omega) hp
        let t := differenceUpdate c (replyAt q O seed ω (call+a) (0,differenceQuery c))
        have ht := hnext
        change t = _ at ht
        have hqueryPage := freyaPageDifferenceQuery q _ c hc
        have hactive : t.count<t.target := by rw [ht]; dsimp only; omega
        have hcontinue := freyaPageDifferenceContinue q _ c
          (replyAt q O seed ω (call+a) (0,differenceQuery c)) hc hactive
        have hupdate : trace q O seed ω (call+(a+1)) =
            update q (trace q O seed ω (call+a))
              (replyAt q O seed ω (call+a) (0,differenceQuery c)) := by
          rw [← Nat.add_assoc]
          rw [trace_succ]
          rw [hqueryPage]
        obtain ⟨old,hold,_,_,hkind,hlabel⟩ := hpending i
        have heq : old=job := Option.some.inj (hold.symm.trans hjob)
        subst old
        have hcompleted := freyaPageCompletedJobEq q O seed ω batch call ⟨a,haS⟩ hstart
          c hc hquery i job time (jobValue f job) hjob hreply
        have hD : D a=jobValue f job := by
          dsimp only [D]
          rw [dite_eq_left haS]
          delta completedLabels
          rw [hcompleted]
          dsimp only [Option.map,Option.elim]
          delta jobValue
          rw [hkind]
        refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · rw [hupdate]; exact hcontinue.1
        · rw [hupdate,hcontinue.2]; exact hit
        · rw [ht]; exact htarget
        · rw [ht]; dsimp only; omega
        · rw [ht]; exact hx
        · rw [ht]; exact hy
        · rw [ht]; exact hrows
        · rw [ht]; dsimp only; omega
        · rw [ht]; dsimp only; rw [hsum,Finset.sum_range_succ,hD]
        · intro k
          obtain ⟨old,hold,hs,htime,hkind'⟩ := hpnext k
          refine ⟨old,?_,?_,?_,?_,?_⟩
          · rw [ht]; exact hold
          · rw [ht]; exact hs
          · rw [ht]; exact htime
          · simpa only [hx,hy] using hkind'
          · by_cases hk : k=i
            · subst k
              rw [Function.update_self] at hold
              have heq : next=old := Option.some.inj hold
              subst old
              change labelAt (seed.1 batch next.id) q.m=some next.component
              rw [hnid,← hrows]
              exact hnlabel
            · rw [Function.update_of_ne hk] at hold
              obtain ⟨old',hold',_,_,_,hl⟩ := hpending k
              have heq : old=old' := Option.some.inj (hold.symm.trans hold')
              subst old'
              exact hl
    have freyaPageDifferenceAverage (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
        (hS : 0 < q.S) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (batch firstID : ℕ) (x y : Space q.d) (clock : ℝ≥0)
        (hinvoke : invocation q O seed ω batch = some (false,x,y,clock,firstID)) :
        batchResult q O seed ω batch = (q.S : ℝ)⁻¹ •
          (∑ j : Fin q.S, (completedLabels q O seed ω batch j).elim 0
            (fun i => gradient (f i) x-gradient (f i) y)) := by
      classical
      obtain ⟨call,hstart,hphase⟩ := freyaPageFreshDifference q O seed ω batch firstID x y clock hinvoke
      let D := fun k : ℕ => if hk : k < q.S then
          (completedLabels q O seed ω batch ⟨k,hk⟩).elim 0
            (fun i => gradient (f i) x-gradient (f i) y) else 0
      have ha : q.S-1<q.S := by omega
      obtain ⟨c,hc,_,htarget,hcount,hx,hy,_,_,hsum,hpending⟩ :=
        freyaPageBatchProgress q hm hn hS f τ O seed ω hservice batch firstID call x y clock
          hstart hphase (q.S-1) ha
      change c.sum=∑ k ∈ Finset.range (q.S-1),D k at hsum
      have hp : ∀ i, ∃ job, c.pending i=some job ∧ job.started≤c.clock ∧
          (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
        intro i
        obtain ⟨job,hj,hs,ht,hk,_⟩ := hpending i
        rw [hx,hy]
        exact ⟨job,hj,hs,ht,hk⟩
      obtain ⟨i,job,time,next,hjob,hquery,hreply,_,_,_,_,_,hnext,_⟩ :=
        freyaDifferenceLiveStep hm hn c f τ
          (fun r => replyAt q O seed ω (call+(q.S-1)) (0,r))
          (hservice (call+(q.S-1))).2 (by omega) hp
      obtain ⟨old,hold,_,_,hkind,_⟩ := hpending i
      have heq : old=job := Option.some.inj (hold.symm.trans hjob)
      subst old
      have hcompleted := freyaPageCompletedJobEq q O seed ω batch call ⟨q.S-1,ha⟩ hstart
        c hc hquery i job time (jobValue f job) hjob hreply
      have hD : D (q.S-1)=jobValue f job := by
        dsimp only [D]
        rw [dite_eq_left ha]
        delta completedLabels
        rw [hcompleted]
        dsimp only [Option.map,Option.elim]
        delta jobValue
        rw [hkind]
      have hsumD : (∑ k ∈ Finset.range q.S,D k) = c.sum+jobValue f job := by
        have hSS : q.S-1+1=q.S := by omega
        conv_lhs => rw [← hSS]
        rw [Finset.sum_range_succ,← hsum,hD]
      have hfin : (∑ j : Fin q.S, (completedLabels q O seed ω batch j).elim 0
          (fun i => gradient (f i) x-gradient (f i) y)) = ∑ k ∈ Finset.range q.S,D k := by
        rw [← Fin.sum_univ_eq_sum_range D q.S]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [D]
        rw [dite_eq_left j.isLt]
      delta batchResult
      rw [ite_eq_right (by omega),hstart]
      dsimp only [Option.getD]
      rw [hc]
      dsimp only
      rw [freyaPageDifferenceQuery q _ c hc,hnext]
      change (c.target : ℝ)⁻¹ • (c.sum+jobValue f job) = _
      rw [htarget,hfin,hsumD]
    exact freyaPageDifferenceAverage q hm hn hS f τ O seed ω hservice batch firstID x y clock hinvoke


noncomputable def batchError (q : Raw) (f : Fin q.m → Space q.d → ℝ)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) : Space q.d := by
  classical
  let xy := batchInputs q O z.1 z.2 batch
  exact if isDifferenceBatch q O z batch then
    batchResult q O z.1 z.2 batch - (gradient (objective f) xy.1 - gradient (objective f) xy.2)
  else 0

theorem difference_moments (q : Raw) (hm : 0 < q.m) (hn : 0 < q.n)
    (hS : 0 < q.S) (hK : 0 < q.K) (hρ : 0 < q.ρ) (hρone : q.ρ ≤ 1)
    (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
    (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
    (batch : ℕ) :
    let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
    let error := batchError q f O batch
    Integrable error P ∧ Integrable (fun z => ‖error z‖ ^ 2) P ∧
      ∀ E, MeasurableSet[historyBefore q O batch] E →
        (∀ z ∈ E, isDifferenceBatch q O z batch) →
        (∫ z in E, error z ∂P) = 0 ∧
          (∫ z in E, ‖error z‖ ^ 2 ∂P) ≤ Lpm ^ 2 / q.S *
            (∫ z in E, ‖(batchInputs q O z.1 z.2 batch).1 -
              (batchInputs q O z.1 z.2 batch).2‖ ^ 2 ∂P) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 4096 in
  open scoped BigOperators ENNReal NNReal in
  open MeasureTheory ProbabilityTheory OracleTemplate in
  open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs in
  open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors in
  open LongTails.Algorithms.FreyaPage LongTails.Setups.FreyaIndependence in
    classical
    have freyaDevelopmentOptionElimMeas {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (b : β) (f : α → β) (hf : Measurable f) :
        Measurable (fun o : Option α => o.elim b f) := by
      have he : Measurable (fun o : Option α => o.elim (Sum.inl ()) Sum.inr) := by
        apply Measurable.of_comap_le
        delta instMeasurableSpaceOption
        apply le_of_eq
        congr 1
        funext o
        cases o <;> rfl
      have hs : Measurable (Sum.elim (fun _ : Unit => b) f) := measurable_const.sumElim hf
      convert hs.comp he using 1
      funext o
      cases o <;> rfl
    have freyaOptionSingleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] :
        MeasurableSingletonClass (Option α) := by
      constructor
      intro x
      let encode := fun o : Option α => o.elim (Sum.inl ()) Sum.inr
      have he : {x}=encode ⁻¹' {encode x} := by
        ext y
        cases x <;> cases y <;> simp (config := { iota := false }) [encode]
      have hsingleton : MeasurableSet {encode x} := by
        rw [measurableSet_sum_iff]
        cases x <;> constructor <;> simp (config := { iota := false }) [encode]
        · have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inl ()}=∅ := by ext a; simp (config := { iota := false })
          rw [he]
          exact MeasurableSet.empty
        · rename_i b
          have he : (Sum.inr : α → Unit ⊕ α) ⁻¹' {Sum.inr b}={b} := by ext a; simp (config := { iota := false })
          rw [he]
          exact measurableSet_singleton _
      rw [he]
      exact (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr)
        hsingleton
    have freyaOptionParamMeas {Ω α β : Type} [MeasurableSpace Ω]
        [MeasurableSpace α] [MeasurableSpace β]
        (o : Ω → Option α) (ho : Measurable o) (b : Ω → β) (hb : Measurable b)
        (f : Ω × α → β) (hf : Measurable f) :
        Measurable (fun z => (o z).elim (b z) (fun a => f (z,a))) := by
      have he := (freyaDevelopmentOptionElimMeas (Sum.inl ()) Sum.inr measurable_inr).comp ho
      have hs := ((hb.comp measurable_fst).sumElim hf).comp
        ((MeasurableEquiv.prodSumDistrib Ω Unit α).measurable.comp (measurable_id.prodMk he))
      convert hs using 1
      funext z
      dsimp only [Function.comp_def,id_eq]
      cases o z <;> rfl'
    have freyaMeasurableSelect {Ω α β : Type} [MeasurableSpace Ω] [MeasurableSpace α]
        [MeasurableSpace β] [Countable α] [MeasurableSingletonClass α]
        (g : Ω → α) (hg : Measurable g) (f : α → Ω → β) (hf : ∀ a,Measurable (f a)) :
        Measurable (fun z => f (g z) z) :=
      (measurable_from_prod_countable_left (f:=fun p : Ω × α => f p.2 p.1) hf).comp
        (measurable_id.prodMk hg)
    let freyaHistoryView (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (batch : ℕ) (z : Seed q.K × ((k : ℕ) → O.Seed k)) :=
      (invocation q O z.1 z.2 batch, fun k : ℕ =>
        if k < (batchStartCall q O z.1 z.2 batch).getD 0 then
          let s := trace q O z.1 z.2 k
          let reply := replyAt q O z.1 z.2 k (query q s)
          some (query q s,reply,collectorPendingAfter q s reply)
        else none)
    have freyaPageInvocationHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        Measurable[historyBefore q O batch]
          (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => invocation q O z.1 z.2 batch) := by
      exact measurable_fst.comp (show Measurable[historyBefore q O batch]
        (freyaHistoryView q O batch) from Measurable.of_comap_le le_rfl)
    have freyaPageDifferenceHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        MeasurableSet[historyBefore q O batch]
          {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch} := by
      let tag := fun a : Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) =>
        a.elim false (fun t => !t.1)
      have ht : Measurable tag := freyaDevelopmentOptionElimMeas false _
        ((measurable_of_countable (fun b : Bool => !b)).comp measurable_fst)
      have hi := ht.comp (freyaPageInvocationHistoryMeas q O batch)
      have he : {z | LongTails.Setups.FreyaIndependence.isDifferenceBatch q O z batch}=
          {z : Seed q.K × ((k : ℕ) → O.Seed k) | tag (invocation q O z.1 z.2 batch)=true} := by
        ext z
        dsimp only [LongTails.Setups.FreyaIndependence.isDifferenceBatch,Set.mem_ofPred_eq]
        cases h : invocation q O z.1 z.2 batch with
        | none => simp (config := { iota := false }) [tag]
        | some a =>
          obtain ⟨b,x,y,t,id⟩ := a
          cases b <;> simp (config := { iota := false }) [tag]
      rw [he]
      exact hi (measurableSet_singleton true)
    have freyaBatchInputsHistoryMeas (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
        Measurable[historyBefore q O batch]
          (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => batchInputs q O z.1 z.2 batch) := by
      have h := (freyaDevelopmentOptionElimMeas ((0 : Space q.d),0)
        (fun a : Bool × Space q.d × Space q.d × ℝ≥0 × ℕ => (a.2.1,a.2.2.1))
        (measurable_snd.fst.prodMk measurable_snd.snd.fst)).comp (freyaPageInvocationHistoryMeas q O batch)
      convert h using 1
      funext z
      dsimp only [Function.comp_def,batchInputs]
      cases invocation q O z.1 z.2 batch <;> rfl
    have freyaBatchErrorAverage (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ) :
        ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
          batchError q f O batch z =
            if isDifferenceBatch q O z batch then
              (q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(completedLabels q O z.1 z.2 batch j).elim 0
                (fun i => gradient (f i) (batchInputs q O z.1 z.2 batch).1-
                  gradient (f i) (batchInputs q O z.1 z.2 batch).2))-
                (gradient (objective f) (batchInputs q O z.1 z.2 batch).1-
                  gradient (objective f) (batchInputs q O z.1 z.2 batch).2)
            else 0 := by
      classical
      have hs : ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
          servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
        (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
      filter_upwards [hs] with z hz
      by_cases hb : isDifferenceBatch q O z batch
      · have hbatch := hb
        obtain ⟨x,y,clock,first,hi⟩ := hb
        have ha := difference_average q hm hn hS hK f τ O z.1 z.2 hz batch first x y clock hi
        have hxy : batchInputs q O z.1 z.2 batch=(x,y) := by
          dsimp only [batchInputs]
          rw [hi]
          rfl
        dsimp only [batchError]
        simp (config := { iota := false }) only [ite_eq_left hbatch,hxy]
        rw [ha]
      · dsimp only [batchError]
        simp (config := { iota := false }) only [ite_eq_right hb]
    have freyaObjectiveGradient {d m : ℕ} (f : Fin m → Space d → ℝ)
        (hf : ∀ i,Differentiable ℝ (f i)) (x : Space d) :
        gradient (objective f) x=(m : ℝ)⁻¹ • ∑ i,gradient (f i) x := by
      have hg : HasGradientAt (objective f) ((m : ℝ)⁻¹ • ∑ i,gradient (f i) x) x := by
        rw [hasGradientAt_iff_hasFDerivAt]
        have hd := (HasFDerivAt.sum (u:=Finset.univ)
          (fun i _ => (hf i x).hasGradientAt.hasFDerivAt)).const_mul (m : ℝ)⁻¹
        simp (config := { iota := false }) only [Finset.sum_apply] at hd
        simp (config := { iota := false }) only [map_sum,map_smul]
        exact hd
      exact hg.gradient
    have freyaComponentBound {d m : ℕ} (hm : 0<m) (f : Fin m → Space d → ℝ) (L : ℝ)
        (hmean : ∀ x y,(m : ℝ)⁻¹*(∑ i,‖gradient (f i) x-gradient (f i) y‖^2)≤L^2*‖x-y‖^2) :
        ∀ i x y,‖gradient (f i) x-gradient (f i) y‖≤Real.sqrt m * |L| * ‖x-y‖ := by
      intro i x y
      have hmR : (0 : ℝ)<m := by exact_mod_cast hm
      have hsum : ‖gradient (f i) x-gradient (f i) y‖^2≤∑ j,‖gradient (f j) x-gradient (f j) y‖^2 :=
        Finset.single_le_sum (f:=fun j : Fin m => ‖gradient (f j) x-gradient (f j) y‖^2)
          (a:=i) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have hmean' := mul_le_mul_of_nonneg_left (hmean x y) hmR.le
      rw [← mul_assoc,mul_inv_cancel₀ hmR.ne',one_mul] at hmean'
      have hbound := hsum.trans hmean'
      have hsq : (Real.sqrt (m : ℝ) * |L| * ‖x-y‖)^2=(m : ℝ)*(L^2*‖x-y‖^2) := by
        rw [mul_pow,mul_pow,Real.sq_sqrt hmR.le,sq_abs]
        ring
      have hnonneg : 0≤Real.sqrt (m : ℝ) * |L| * ‖x-y‖ := by positivity
      nlinarith [norm_nonneg (gradient (f i) x-gradient (f i) y)]
    have freyaComponentMeas {d m : ℕ} (hm : 0<m) (f : Fin m → Space d → ℝ) (L : ℝ)
        (hmean : ∀ x y,(m : ℝ)⁻¹*(∑ i,‖gradient (f i) x-gradient (f i) y‖^2)≤L^2*‖x-y‖^2) :
        ∀ i,Measurable (gradient (f i)) := by
      intro i
      have hlip : LipschitzWith ⟨Real.sqrt m*|L|,by positivity⟩ (gradient (f i)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        change ‖gradient (f i) x-gradient (f i) y‖≤Real.sqrt m * |L| * ‖x-y‖
        exact freyaComponentBound hm f L hmean i x y
      exact hlip.continuous.measurable
    have freyaBatchErrorAEStrong (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (lower Lminus Lplus Lpm Δ : ℝ) (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ)
        (hH : historyBefore q O batch ≤ (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))))
        (hl : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => completedLabels q O z.1 z.2 batch)) :
        AEStronglyMeasurable (batchError q f O batch) (executionLaw q O : Measure _) := by
      classical
      let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
      let xy := fun z : Ω => batchInputs q O z.1 z.2 batch
      have hxy : Measurable xy := (freyaBatchInputsHistoryMeas q O batch).mono hH le_rfl
      have hg := freyaComponentMeas hm f Lplus hreg.mean_square
      have hmean : Measurable (gradient (objective f)) := by
        have h : Measurable (fun x => (q.m : ℝ)⁻¹ • ∑ i,gradient (f i) x) :=
          (Finset.measurable_sum Finset.univ (fun i _ => hg i)).const_smul ((q.m : ℝ)⁻¹)
        convert h using 1
        funext x
        exact freyaObjectiveGradient f hreg.differentiable x
      have hv (j : Fin q.S) : Measurable (fun z : Ω =>
          (completedLabels q O z.1 z.2 batch j).elim (0 : Space q.d)
            (fun i => gradient (f i) (xy z).1-gradient (f i) (xy z).2)) := by
        have hb : Measurable (fun z : Ω × Fin q.m => gradient (f z.2) (xy z.1).1-
            gradient (f z.2) (xy z.1).2) :=
          freyaMeasurableSelect _ measurable_snd _ (fun i =>
            ((hg i).comp (hxy.fst.comp measurable_fst)).sub ((hg i).comp (hxy.snd.comp measurable_fst)))
        exact freyaOptionParamMeas _ ((measurable_pi_apply j).comp hl) _ measurable_const _ hb
      have hmodel : Measurable (fun z : Ω => if isDifferenceBatch q O z batch then
          (q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(completedLabels q O z.1 z.2 batch j).elim (0 : Space q.d)
            (fun i => gradient (f i) (xy z).1-gradient (f i) (xy z).2))-
            (gradient (objective f) (xy z).1-gradient (objective f) (xy z).2) else 0) :=
        (((Finset.measurable_sum Finset.univ (fun j _ => hv j)).const_smul ((q.S : ℝ)⁻¹)).sub
          ((hmean.comp hxy.fst).sub (hmean.comp hxy.snd))).ite
          (hH _ (freyaPageDifferenceHistoryMeas q O batch)) measurable_const
      apply hmodel.aestronglyMeasurable.congr
      filter_upwards [freyaBatchErrorAverage q hm hn hS hK f τ O hservice batch] with z hz
      exact hz.symm
    have freyaPageFirstMatch (N : ℕ) (p : ℕ → Bool) (k : ℕ)
        (h : (List.range N).find? p = some k) :
        k < N ∧ p k = true ∧ ∀ r < k, p r ≠ true := by
      obtain ⟨hp,i,hi,hik,hprev⟩ := List.find?_eq_some_iff_getElem.mp h
      simp (config := { iota := false }) only [List.length_range,List.getElem_range] at hi hik hprev
      subst i
      refine ⟨hi,hp,?_⟩
      intro r hr htrue
      have hh := hprev r hr
      rw [htrue] at hh
      contradiction
    have freyaPageBatchStartFacts (q : Raw)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ)
        (h : batchStartCall q O seed ω batch = some call) :
        call ≤ eventLimit q ∧ (trace q O seed ω call).iteration = batch ∧
          active (trace q O seed ω call) = true ∧
          ∀ r < call, ¬ ((trace q O seed ω r).iteration = batch ∧ active (trace q O seed ω r) = true) := by
      delta batchStartCall at h
      obtain ⟨hcall,hvalue,hprev⟩ := freyaPageFirstMatch _ _ call h
      obtain ⟨hit,ha⟩ := Bool.and_eq_true_iff.mp hvalue
      refine ⟨by omega,of_decide_eq_true hit,ha,?_⟩
      intro r hr hh
      apply hprev r hr
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hh.1,hh.2⟩
    have freyaDifferenceLiveStep {d m n : ℕ} (hm : 0 < m) (hn : 0 < n)
        (s : DifferenceState d m n) (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i = some j ∧ reply (some r) = some (i,j.id,c,jobValue f j) ∧
            r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i')
        (ha : s.count < s.target)
        (hp : ∀ i, ∃ job, s.pending i = some job ∧ job.started ≤ s.clock ∧
          (s.clock : ℝ≥0∞) ≤ deadline τ job i ∧ job.kind = Sum.inr (s.x,s.y)) :
        ∃ i job c next,
          s.pending i = some job ∧
          differenceQuery s = some ⟨s.clock,s.pending⟩ ∧
          reply (differenceQuery s) = some (i,job.id,c,jobValue f job) ∧
          s.clock ≤ c ∧
          next.id = s.nextID ∧ next.kind = Sum.inr (s.x,s.y) ∧ next.started = c ∧
          labelAt (s.rows s.nextID) m = some next.component ∧
          differenceUpdate s (reply (differenceQuery s)) =
            {s with
              count := s.count+1
              sum := s.sum+jobValue f job
              pending := Function.update s.pending i (some next)
              clock := c
              nextID := s.nextID+1} ∧
          ∀ k, ∃ old, (Function.update s.pending i (some next)) k = some old ∧
            old.started ≤ c ∧ (c : ℝ≥0∞) ≤ deadline τ old k ∧ old.kind = Sum.inr (s.x,s.y) := by
      classical
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hlegal : legalRequest τ r := by
        refine ⟨?_,?_⟩
        · obtain ⟨job,hj,_⟩ := hp ⟨0,hn⟩
          exact ⟨⟨0,hn⟩,job,hj⟩
        · intro i job hj
          obtain ⟨old,hold,hs,ht,_⟩ := hp i
          have heq : job=old := Option.some.inj (hj.symm.trans hold)
          subst old
          exact ⟨hs,ht⟩
      have hquery : differenceQuery s = some r := by
        delta differenceQuery
        rw [ite_eq_right (by omega)]
        delta pendingRequest
        have hex : ∃ i, s.pending i ≠ none := by
          obtain ⟨i,job,hj⟩ := hlegal.1
          change s.pending i=some job at hj
          exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,c,hjob,hreply,hclock,hdeadline⟩ := hservice r hlegal
      change s.pending i=some job at hjob
      change s.clock≤c at hclock
      obtain ⟨b,hb⟩ : ∃ b : Fin m, labelAt (s.rows s.nextID) m = some b := by
        delta labelAt
        simp (config := { iota := false }) only [hm,dite_true]
        exact ⟨_,rfl⟩
      let next : Job d m := ⟨b,Sum.inr (s.x,s.y),c,s.nextID⟩
      refine ⟨i,job,c,next,hjob,hquery,?_,hclock,rfl,rfl,rfl,hb,?_,?_⟩
      · rw [hquery]; exact hreply
      · rw [hquery,hreply]
        delta differenceUpdate
        rw [ite_eq_right (by omega)]
        dsimp only
        rw [hjob]
        dsimp only
        rw [ite_eq_left (And.intro rfl hclock)]
        delta dispatch
        rw [hb]
        rfl
      · intro k
        by_cases hk : k=i
        · subst k
          refine ⟨next,Function.update_self _ _ _,le_rfl,?_,rfl⟩
          change (c : ℝ≥0∞) ≤ (c : ℝ≥0∞)+(2 : ℕ)*τ i
          exact le_add_of_nonneg_right zero_le
        · obtain ⟨old,hold,hstarted,_,hkind⟩ := hp k
          refine ⟨old,?_,hstarted.trans hclock,hdeadline k old hold,hkind⟩
          rw [Function.update_of_ne hk]
          exact hold
    have freyaPageDifferenceQuery (q : Raw) (s : State q)
        (c : DifferenceState q.d q.m q.n) (h : s.phase = Phase.difference c) :
        query q s = (0,differenceQuery c) := by
      delta query
      rw [h]
      rfl
    have freyaFullSelect {m : ℕ} (labels : List (Fin m)) (rem : List ℕ)
        (hne : rem≠[]) (hbound : ∀ b ∈ rem,b<labels.length) (row : ChoiceRow) :
        ∃ b, b ∈ rem ∧ ∃ hb : b<labels.length, selectedLabel labels rem row=some labels[b] := by
      have hlen : rem.length≠0 := by intro hz; exact hne (List.length_eq_zero_iff.mp hz)
      let j : Fin rem.length := ⟨(row (rem.length-1)).val,by
        have hj := (row (rem.length-1)).isLt
        omega⟩
      have hb := hbound _ (List.get_mem rem j)
      refine ⟨rem.get j,List.get_mem rem j,hb,?_⟩
      delta selectedLabel chooseRemaining
      rw [dite_eq_right hlen]
      dsimp only
      exact List.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩
    have freyaFullSafeUpdate {d m n : ℕ} (s : FullState d m n)
        (hne : s.remaining≠[]) (hbound : ∀ b ∈ s.remaining,b<s.original.length)
        (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
        (reply : Option (Request d m n) → Reply d n)
        (hr : legalRequest τ ⟨s.clock,s.pending⟩)
        (hservice : ∀ r, legalRequest τ r → ∃ i j c,
          r.pending i=some j ∧ reply (some r)=some (i,j.id,c,jobValue f j) ∧
          r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i') :
        let t := fullUpdate s (reply (fullQuery s))
        t.original=s.original ∧ (∀ b ∈ t.remaining,b<t.original.length) ∧
          (t.remaining≠[] → legalRequest τ ⟨t.clock,t.pending⟩) := by
      classical
      have hisEmpty : s.remaining.isEmpty=false := by
        cases h : s.remaining with
        | nil => exact False.elim (hne h)
        | cons b bs => rfl
      let r : Request d m n := ⟨s.clock,s.pending⟩
      have hquery : fullQuery s=some r := by
        delta fullQuery
        rw [hisEmpty,ite_eq_right Bool.false_ne_true]
        delta pendingRequest
        have hex : ∃ i,s.pending i≠none := by
          obtain ⟨i,job,hj⟩ := hr.1
          change s.pending i=some job at hj
          exact ⟨i,by rw [hj]; simp (config := { iota := false })⟩
        rw [ite_eq_left hex]
      obtain ⟨i,job,time,hjob,hreply,hclock,hdeadline⟩ := hservice r hr
      change s.pending i=some job at hjob
      change s.clock≤time at hclock
      let found := s.remaining.find? fun b => decide (s.original[b]?=some job.component)
      let rem := found.elim s.remaining (fun b => s.remaining.erase b)
      let next := dispatch (Sum.inl s.point) time s.nextID
        (selectedLabel s.original rem (s.rows s.nextID))
      let t : FullState d m n :=
        {s with
          remaining := rem
          sum := if found.isSome then s.sum+jobValue f job else s.sum
          pending := Function.update s.pending i next
          clock := time
          nextID := s.nextID+1}
      have ht : fullUpdate s (reply (fullQuery s))=t := by
        rw [hquery,hreply]
        delta fullUpdate
        rw [hisEmpty,ite_eq_right Bool.false_ne_true]
        dsimp only
        rw [hjob]
        dsimp only
        rw [ite_eq_left (And.intro rfl hclock)]
      have hb : ∀ b ∈ rem,b<s.original.length := by
        cases hf : found with
        | none => simpa (config := { iota := false }) only [rem,hf,Option.elim_none] using hbound
        | some a =>
          intro b h
          exact hbound b (List.mem_of_mem_erase (by simpa (config := { iota := false }) only [rem,hf,Option.elim_some] using h))
      dsimp only
      rw [ht]
      refine ⟨rfl,hb,?_⟩
      intro htne
      obtain ⟨b,hbr,hbl,hlabel⟩ := freyaFullSelect s.original rem htne hb (s.rows s.nextID)
      let new : Job d m := ⟨s.original[b],Sum.inl s.point,time,s.nextID⟩
      have hnew : next=some new := by
        dsimp only [next]
        rw [hlabel]
        rfl
      refine ⟨⟨i,new,?_⟩,?_⟩
      · change Function.update s.pending i next i=some new
        rw [Function.update_self,hnew]
      · intro k old hold
        change Function.update s.pending i next k=some old at hold
        by_cases hk : k=i
        · subst k
          rw [Function.update_self,hnew] at hold
          have heq : new=old := Option.some.inj hold
          subst old
          refine ⟨le_rfl,?_⟩
          exact le_add_of_nonneg_right zero_le
        · rw [Function.update_of_ne hk] at hold
          exact ⟨((hr.2 k old hold).1).trans hclock,hdeadline k old hold⟩
    have freyaFullInitialSafe {d m n : ℕ} (hn : 0<n) (labels : List (Fin m))
        (hne : labels≠[]) (x : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow)
        (firstID : ℕ) (τ : Fin n → ℝ≥0∞) :
        let s := fullInitial n labels x clock rows firstID
        s.remaining≠[] ∧ (∀ b ∈ s.remaining,b<s.original.length) ∧
          legalRequest τ ⟨s.clock,s.pending⟩ := by
      classical
      let s := fullInitial n labels x clock rows firstID
      have hrem : (List.range labels.length)≠[] := by
        intro h
        have := congrArg List.length h
        simp (config := { iota := false }) only [List.length_range,List.length_nil] at this
        exact hne (List.length_eq_zero_iff.mp this)
      have hbound : ∀ b ∈ List.range labels.length,b<labels.length := fun b hb => List.mem_range.mp hb
      refine ⟨hrem,hbound,?_,?_⟩
      · let i : Fin n := ⟨0,hn⟩
        obtain ⟨b,_,hb,hlabel⟩ := freyaFullSelect labels _ hrem hbound (rows (firstID+i.val))
        refine ⟨i,⟨labels[b],Sum.inl x,clock,firstID+i.val⟩,?_⟩
        change dispatch (Sum.inl x) clock (firstID+i.val)
          (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=_
        rw [hlabel]
        rfl
      · intro i job hj
        change dispatch (Sum.inl x) clock (firstID+i.val)
          (selectedLabel labels (List.range labels.length) (rows (firstID+i.val)))=some job at hj
        delta dispatch at hj
        obtain ⟨b,_,heq⟩ := Option.map_eq_some_iff.mp hj
        cases heq
        exact ⟨le_rfl,le_add_of_nonneg_right zero_le⟩
    have freyaDifferenceInitialSafe {d m n : ℕ} (hm : 0<m) (S : ℕ) (hS : 0<S)
        (x y : Space d) (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ)
        (τ : Fin n → ℝ≥0∞) :
        let c : DifferenceState d m n := differenceInitial n S x y clock rows firstID
        ∀ i, ∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
          (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y) := by
      dsimp only
      intro i
      obtain ⟨b,hb⟩ : ∃ b : Fin m,labelAt (rows (firstID+i.val)) m=some b := by
        delta labelAt
        simp (config := { iota := false }) only [hm,dite_true]
        exact ⟨_,rfl⟩
      refine ⟨⟨b,Sum.inr (x,y),clock,firstID+i.val⟩,?_,le_rfl,?_,rfl⟩
      · change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (firstID+i.val)
          (labelAt (rows (firstID+i.val)) m))=_
        rw [ite_eq_right (by omega),hb]
        rfl
      · exact le_add_of_nonneg_right zero_le
    have freyaPageFullQuery (q : Raw) (s : State q) (first : Bool)
        (c : FullState q.d q.m q.n) (h : s.phase=Phase.full first c) :
        query q s=(0,fullQuery c) := by
      delta query
      rw [h]
      rfl
    have freyaPagePhaseSafety (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
        let Safe := fun s : State q =>
          (∀ first c,s.phase=Phase.full first c →
            c.original.length=q.m ∧ c.remaining≠[] ∧
            (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
          (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
            ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
          s.iteration≤rounds q
        ∀ k,Safe (trace q O seed ω k) := by
      classical
      let Safe := fun s : State q =>
          (∀ first c,s.phase=Phase.full first c →
            c.original.length=q.m ∧ c.remaining≠[] ∧
            (∀ b ∈ c.remaining,b<c.original.length) ∧ legalRequest τ ⟨c.clock,c.pending⟩) ∧
          (∀ c,s.phase=Phase.difference c → c.target=q.S ∧ c.count<c.target ∧
            ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
              (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y)) ∧
          s.iteration≤rounds q
      change ∀ k,Safe (trace q O seed ω k)
      have hfull (s : State q) (first : Bool) (c : FullState q.d q.m q.n)
          (hp : s.phase=Phase.full first c) (h1 : c.original.length=q.m) (h2 : c.remaining≠[])
          (h3 : ∀ b ∈ c.remaining,b<c.original.length)
          (h4 : legalRequest τ ⟨c.clock,c.pending⟩) (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first' c' he
          rw [hp] at he
          cases he
          exact ⟨h1,h2,h3,h4⟩
        · intro c' he
          rw [hp] at he
          cases he
      have hdiff (s : State q) (c : DifferenceState q.d q.m q.n)
          (hp : s.phase=Phase.difference c) (h1 : c.target=q.S) (h2 : c.count<c.target)
          (h3 : ∀ i,∃ job,c.pending i=some job ∧ job.started≤c.clock ∧
            (c.clock : ℝ≥0∞)≤deadline τ job i ∧ job.kind=Sum.inr (c.x,c.y))
          (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first c' he
          rw [hp] at he
          cases he
        · intro c' he
          rw [hp] at he
          cases he
          exact ⟨h1,h2,h3⟩
      have hhalt (s : State q) (hp : s.phase=Phase.halted) (hi : s.iteration≤rounds q) : Safe s := by
        refine ⟨?_,?_,hi⟩
        · intro first c he; rw [hp] at he; cases he
        · intro c he; rw [hp] at he; cases he
      have hlabels : (List.ofFn (id : Fin q.m → Fin q.m))≠[] := by
        intro he
        have hh := congrArg List.length he
        simp (config := { iota := false }) only [List.length_ofFn,List.length_nil] at hh
        omega
      have hadvance (s : State q) (hi : s.iteration≤rounds q) : Safe (advance q s) := by
        delta advance
        split
        · exact hhalt _ rfl hi
        · rename_i hlt
          dsimp only
          by_cases hrefresh : refreshAt s.seed s.iteration=true
          · rw [ite_eq_left hrefresh]
            have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels
              (s.x-q.η • s.g) s.clock (s.seed.1 (s.iteration+1)) s.nextID τ
            apply hfull _ false _ rfl (List.length_ofFn) hf.1 hf.2.1 hf.2.2
            dsimp only
            omega
          · rw [ite_eq_right hrefresh]
            apply hdiff _ _ rfl rfl hS
              (freyaDifferenceInitialSafe hm q.S hS _ _ _ _ _ τ)
            dsimp only
            omega
      have hinit : Safe (initial q seed) := by
        have hp : (initial q seed).phase=Phase.full true
            (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0)) := by
          delta initial
          dsimp only
          rw [ite_eq_right (by omega)]
        have hf := freyaFullInitialSafe hn (List.ofFn id) hlabels q.x0 0 (seed.1 0) 0 τ
        exact hfull _ true _ hp (List.length_ofFn) hf.1 hf.2.1 hf.2.2 (Nat.zero_le _)
      intro k
      induction k with
      | zero => exact hinit
      | succ k ih =>
        let s := trace q O seed ω k
        change Safe s at ih
        change Safe (update q s (replyAt q O seed ω k (query q s)))
        cases hs : s.phase with
        | halted =>
          have hu : update q s (replyAt q O seed ω k (query q s))=s := by delta update; rw [hs]
          rw [hu]
          exact ih
        | full first c =>
          obtain ⟨hlen,hne,hb,hl⟩ := ih.1 first c hs
          have hquery := freyaPageFullQuery q s first c hs
          rw [hquery]
          let t := fullUpdate c (replyAt q O seed ω k (0,fullQuery c))
          have ht := freyaFullSafeUpdate c hne hb f τ (fun r => replyAt q O seed ω k (0,r)) hl (hservice k).2
          change t.original=c.original ∧ _ at ht
          delta update
          rw [hs]
          dsimp only
          change Safe (if t.remaining.isEmpty then advance q _ else _)
          by_cases he : t.remaining.isEmpty=true
          · rw [ite_eq_left he]
            apply hadvance
            exact ih.2.2
          · rw [ite_eq_right he]
            have htne : t.remaining≠[] := by intro hz; apply he; rw [hz]; rfl
            exact hfull _ first t rfl (ht.1 ▸ hlen) htne ht.2.1 (ht.2.2 htne) ih.2.2
        | difference c =>
          obtain ⟨htarget,hcount,hp⟩ := ih.2.1 c hs
          have hquery := freyaPageDifferenceQuery q s c hs
          rw [hquery]
          obtain ⟨i,job,time,next,_,_,_,_,_,_,_,_,ht,hpn⟩ :=
            freyaDifferenceLiveStep hm hn c f τ (fun r => replyAt q O seed ω k (0,r)) (hservice k).2 hcount hp
          delta update
          rw [hs]
          dsimp only
          rw [ht]
          dsimp only
          by_cases he : c.target≤c.count+1
          · rw [ite_eq_left he]
            apply hadvance
            exact ih.2.2
          · rw [ite_eq_right he]
            refine hdiff _ _ rfl ?_ ?_ ?_ ?_
            · exact htarget
            · change c.count+1<c.target
              omega
            · exact hpn
            · exact ih.2.2
    let freyaJobBound {d m : ℕ} (B : ℝ) (job : Job d m) : Prop :=
      job.kind.elim (fun x => ‖x‖≤B) (fun xy => ‖xy.1‖≤B ∧ ‖xy.2‖≤B)
    let freyaFullBound {d m n : ℕ} (B : ℝ) (s : FullState d m n) : Prop :=
      ‖s.point‖≤B ∧ ‖s.sum‖≤B ∧ ∀ i job,s.pending i=some job → freyaJobBound B job
    let freyaDifferenceBound {d m n : ℕ} (B : ℝ) (s : DifferenceState d m n) : Prop :=
      ‖s.x‖≤B ∧ ‖s.y‖≤B ∧ ‖s.sum‖≤B ∧ ∀ i job,s.pending i=some job → freyaJobBound B job
    let freyaStateBound {q : Raw} (B : ℝ) (s : State q) : Prop :=
      ‖s.x‖≤B ∧ ‖s.g‖≤B ∧ ‖s.selected‖≤B ∧
        s.phase.casesOn (fun _ c => freyaFullBound B c) (fun c => freyaDifferenceBound B c) True
    have freyaJobBoundMono {d m : ℕ} {B C : ℝ} (hBC : B≤C) (job : Job d m)
        (h : freyaJobBound B job) : freyaJobBound C job := by
      dsimp only [freyaJobBound] at h ⊢
      generalize job.kind = kind at h ⊢
      cases kind with
      | inl x => exact h.trans hBC
      | inr xy => exact ⟨h.1.trans hBC,h.2.trans hBC⟩
    have freyaFullBoundMono {d m n : ℕ} {B C : ℝ} (hBC : B≤C) (s : FullState d m n)
        (h : freyaFullBound B s) : freyaFullBound C s :=
      ⟨h.1.trans hBC,h.2.1.trans hBC,fun i j hj => freyaJobBoundMono hBC j (h.2.2 i j hj)⟩
    have freyaDifferenceBoundMono {d m n : ℕ} {B C : ℝ} (hBC : B≤C) (s : DifferenceState d m n)
        (h : freyaDifferenceBound B s) : freyaDifferenceBound C s :=
      ⟨h.1.trans hBC,h.2.1.trans hBC,h.2.2.1.trans hBC,
        fun i j hj => freyaJobBoundMono hBC j (h.2.2.2 i j hj)⟩
    have freyaStateBoundMono {q : Raw} {B C : ℝ} (hBC : B≤C) (s : State q)
        (h : freyaStateBound B s) : freyaStateBound C s := by
      refine ⟨h.1.trans hBC,h.2.1.trans hBC,h.2.2.1.trans hBC,?_⟩
      have hp := h.2.2.2
      generalize s.phase = phase at hp ⊢
      cases phase with
      | halted => trivial
      | full b c => exact freyaFullBoundMono hBC c hp
      | difference c => exact freyaDifferenceBoundMono hBC c hp
    have freyaDispatchBound {d m : ℕ} (B : ℝ) (kind : JobKind d) (clock : ℝ≥0) (id : ℕ)
        (label : Option (Fin m))
        (hkind : kind.elim (fun x => ‖x‖≤B) (fun xy => ‖xy.1‖≤B ∧ ‖xy.2‖≤B)) :
        ∀ job,dispatch kind clock id label=some job → freyaJobBound B job := by
      intro job hj
      delta dispatch at hj
      cases label with
      | none => cases hj
      | some i =>
        cases hj
        exact hkind
    have freyaFullInitialBound {d m : ℕ} (n : ℕ) (B : ℝ) (hB : 0≤B)
        (labels : List (Fin m)) (x : Space d) (hx : ‖x‖≤B) (clock : ℝ≥0)
        (rows : ℕ → ChoiceRow) (first : ℕ) :
        freyaFullBound B (fullInitial n labels x clock rows first) := by
      dsimp only [freyaFullBound,fullInitial]
      refine ⟨hx,?_,?_⟩
      · simpa (config := { iota := false }) only [norm_zero] using hB
      · intro i job hj
        exact freyaDispatchBound B (Sum.inl x) _ _ _ hx job hj
    have freyaDifferenceInitialBound {d m : ℕ} (n S : ℕ) (B : ℝ) (hB : 0≤B)
        (x y : Space d) (hx : ‖x‖≤B) (hy : ‖y‖≤B) (clock : ℝ≥0)
        (rows : ℕ → ChoiceRow) (first : ℕ) :
        freyaDifferenceBound B (differenceInitial (m:=m) n S x y clock rows first) := by
      dsimp only [freyaDifferenceBound,differenceInitial]
      refine ⟨hx,hy,?_,?_⟩
      · simpa (config := { iota := false }) only [norm_zero] using hB
      · intro i job hj
        change (if S=0 then none else dispatch (Sum.inr (x,y)) clock (first+i.val)
          (labelAt (rows (first+i.val)) m))=some job at hj
        by_cases hS : S=0
        · rw [ite_eq_left hS] at hj
          cases hj
        · rw [ite_eq_right hS] at hj
          exact freyaDispatchBound B (Sum.inr (x,y)) _ _ _ ⟨hx,hy⟩ job hj
    have freyaFullUpdateBound {d m n : ℕ} (B R : ℝ) (hR : 0≤R)
        (s : FullState d m n) (hs : freyaFullBound B s) (reply : Reply d n)
        (hr : ∀ i id t v,reply=some (i,id,t,v) → ‖v‖≤R) :
        freyaFullBound (B+R) (fullUpdate s reply) := by
      classical
      have hBC : B≤B+R := le_add_of_nonneg_right hR
      delta fullUpdate
      by_cases he : s.remaining.isEmpty=true
      · simp (config := { iota := false }) only [ite_eq_left he]
        exact freyaFullBoundMono hBC s hs
      · simp (config := { iota := false }) only [ite_eq_right he]
        cases hreply : reply with
        | none => exact freyaFullBoundMono hBC s hs
        | some a =>
          obtain ⟨i,id,t,v⟩ := a
          have hv := hr i id t v hreply
          dsimp only
          cases hp : s.pending i with
          | none => exact freyaFullBoundMono hBC s hs
          | some old =>
            dsimp only
            split
            · dsimp only [freyaFullBound]
              refine ⟨hs.1.trans hBC,?_,?_⟩
              · split
                · exact (norm_add_le s.sum v).trans (add_le_add hs.2.1 hv)
                · exact hs.2.1.trans hBC
              · intro j job hj
                by_cases hji : j=i
                · subst j
                  rw [Function.update_self] at hj
                  exact freyaDispatchBound (B+R) (Sum.inl s.point) _ _ _ (hs.1.trans hBC) job hj
                · rw [Function.update_of_ne hji] at hj
                  exact freyaJobBoundMono hBC job (hs.2.2 j job hj)
            · exact freyaFullBoundMono hBC s hs
    have freyaDifferenceUpdateBound {d m n : ℕ} (B R : ℝ) (hR : 0≤R)
        (s : DifferenceState d m n) (hs : freyaDifferenceBound B s) (reply : Reply d n)
        (hr : ∀ i id t v,reply=some (i,id,t,v) → ‖v‖≤R) :
        freyaDifferenceBound (B+R) (differenceUpdate s reply) := by
      classical
      have hBC : B≤B+R := le_add_of_nonneg_right hR
      delta differenceUpdate
      by_cases he : s.target≤s.count
      · simp (config := { iota := false }) only [ite_eq_left he]
        exact freyaDifferenceBoundMono hBC s hs
      · simp (config := { iota := false }) only [ite_eq_right he]
        cases hreply : reply with
        | none => exact freyaDifferenceBoundMono hBC s hs
        | some a =>
          obtain ⟨i,id,t,v⟩ := a
          have hv := hr i id t v hreply
          dsimp only
          cases hp : s.pending i with
          | none => exact freyaDifferenceBoundMono hBC s hs
          | some old =>
            dsimp only
            split
            · dsimp only [freyaDifferenceBound]
              refine ⟨hs.1.trans hBC,hs.2.1.trans hBC,
                (norm_add_le s.sum v).trans (add_le_add hs.2.2.1 hv),?_⟩
              intro j job hj
              by_cases hji : j=i
              · subst j
                rw [Function.update_self] at hj
                exact freyaDispatchBound (B+R) (Sum.inr (s.x,s.y)) _ _ _ ⟨hs.1.trans hBC,hs.2.1.trans hBC⟩ job hj
              · rw [Function.update_of_ne hji] at hj
                exact freyaJobBoundMono hBC job (hs.2.2.2 j job hj)
            · exact freyaDifferenceBoundMono hBC s hs
    have freyaInverseNatNorm (n : ℕ) : ‖(n : ℝ)⁻¹‖≤1 := by
      by_cases hn : n=0
      · subst n
        norm_num
      · have hnat : 1≤n := Nat.one_le_iff_ne_zero.mpr hn
        have hreal : (1 : ℝ)≤n := by exact_mod_cast hnat
        rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact inv_le_one_of_one_le₀ hreal
    have freyaFullResultBound {d m n : ℕ} (B : ℝ) (s : FullState d m n)
        (hs : freyaFullBound B s) : ‖fullResult s‖≤B := by
      dsimp only [fullResult]
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (freyaInverseNatNorm _)).trans hs.2.1
    have freyaDifferenceResultBound {d m n : ℕ} (B : ℝ) (s : DifferenceState d m n)
        (hs : freyaDifferenceBound B s) : ‖differenceResult s‖≤B := by
      dsimp only [differenceResult]
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (freyaInverseNatNorm _)).trans hs.2.2.1
    have freyaPageInitialBound (q : Raw) (seed : Seed q.K) (B : ℝ) (hB : 0≤B)
        (hx : ‖q.x0‖≤B) : freyaStateBound B (initial q seed) := by
      classical
      dsimp only [initial,freyaStateBound]
      refine ⟨hx,by simpa (config := { iota := false }) only [norm_zero] using hB,hx,?_⟩
      by_cases hb : q.m=0 ∨ q.n=0 ∨ q.K=0
      · simp (config := { iota := false }) only [ite_eq_left hb]
        all_goals exact True.intro
      · simp (config := { iota := false }) only [ite_eq_right hb]
        exact freyaFullInitialBound q.n B hB _ q.x0 hx 0 _ 0
    have freyaPageAdvanceBound (q : Raw) (s : State q) (B : ℝ) (hB : 0≤B)
        (hs : freyaStateBound B s) : freyaStateBound ((1+|q.η|)*B) (advance q s) := by
      classical
      let C := (1+|q.η|)*B
      have hBC : B≤C := by dsimp [C]; nlinarith [mul_nonneg (abs_nonneg q.η) hB]
      have hC : 0≤C := hB.trans hBC
      have hx : ‖s.x-q.η • s.g‖≤C := by
        have h := (norm_sub_le s.x (q.η • s.g)).trans (add_le_add hs.1
          ((norm_smul q.η s.g).le.trans (mul_le_mul_of_nonneg_left hs.2.1 (norm_nonneg q.η))))
        simpa (config := { iota := false }) only [C,Real.norm_eq_abs,add_mul,one_mul] using h
      delta advance
      by_cases hstop : rounds q≤s.iteration
      · simp (config := { iota := false }) only [ite_eq_left hstop]
        exact ⟨hs.1.trans hBC,hs.2.1.trans hBC,hs.2.2.1.trans hBC,True.intro⟩
      · simp (config := { iota := false }) only [ite_eq_right hstop]
        dsimp only [freyaStateBound]
        refine ⟨hx,hs.2.1.trans hBC,?_,?_⟩
        · split
          · exact hx
          · exact hs.2.2.1.trans hBC
        · by_cases hr : refreshAt s.seed s.iteration=true
          · simp (config := { iota := false }) only [ite_eq_left hr]
            exact freyaFullInitialBound q.n C hC _ _ hx _ _ _
          · simp (config := { iota := false }) only [ite_eq_right hr]
            exact freyaDifferenceInitialBound q.n q.S C hC _ _ hx (hs.1.trans hBC) _ _ _
    have freyaPageUpdateBound (q : Raw) (s : State q) (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
        (hs : freyaStateBound B s) (reply : Reply q.d q.n)
        (hr : ∀ i id t v,reply=some (i,id,t,v) → ‖v‖≤R) :
        freyaStateBound ((1+|q.η|)*(2*B+R)) (update q s reply) := by
      classical
      let D := 2*B+R
      let C := (1+|q.η|)*D
      have hBD : B≤D := by dsimp [D]; linarith
      have hMD : B+R≤D := by dsimp [D]; linarith
      have hD : 0≤D := hB.trans hBD
      have hDC : D≤C := by dsimp [C]; nlinarith [mul_nonneg (abs_nonneg q.η) hD]
      have hp := hs.2.2.2
      delta update
      cases hphase : s.phase with
      | halted => exact freyaStateBoundMono (hBD.trans hDC) s hs
      | full first c =>
        rw [hphase] at hp
        have hc := freyaFullUpdateBound B R hR c hp reply hr
        have hcD := freyaFullBoundMono hMD _ hc
        dsimp only
        by_cases he : (fullUpdate c reply).remaining.isEmpty=true
        · simp (config := { iota := false }) only [ite_eq_left he]
          exact freyaPageAdvanceBound q _ D hD
            ⟨hs.1.trans hBD,(freyaFullResultBound (B+R) _ hc).trans hMD,hs.2.2.1.trans hBD,hcD⟩
        · simp (config := { iota := false }) only [ite_eq_right he]
          apply freyaStateBoundMono hDC
          exact ⟨hs.1.trans hBD,hs.2.1.trans hBD,hs.2.2.1.trans hBD,hcD⟩
      | difference c =>
        rw [hphase] at hp
        have hc := freyaDifferenceUpdateBound B R hR c hp reply hr
        have hcD := freyaDifferenceBoundMono hMD _ hc
        dsimp only
        by_cases he : (differenceUpdate c reply).target≤(differenceUpdate c reply).count
        · simp (config := { iota := false }) only [ite_eq_left he]
          apply freyaPageAdvanceBound q _ D hD
          refine ⟨hs.1.trans hBD,?_,hs.2.2.1.trans hBD,hcD⟩
          have h := (norm_add_le s.g (differenceResult (differenceUpdate c reply))).trans
            (add_le_add hs.2.1 (freyaDifferenceResultBound (B+R) _ hc))
          dsimp only [D]
          linarith
        · simp (config := { iota := false }) only [ite_eq_right he]
          apply freyaStateBoundMono hDC
          exact ⟨hs.1.trans hBD,hs.2.1.trans hBD,hs.2.2.1.trans hBD,hcD⟩
    have freyaPageQueryJobBound (q : Raw) (s : State q) (B : ℝ) (hs : freyaStateBound B s)
        (r : Request q.d q.m q.n) (hr : (query q s).2=some r) :
        ∀ i job,r.pending i=some job → freyaJobBound B job := by
      classical
      have hp := hs.2.2.2
      delta query at hr
      cases hphase : s.phase with
      | halted => rw [hphase] at hr; cases hr
      | full first c =>
        rw [hphase] at hr hp
        dsimp only at hr hp
        by_cases he : c.remaining.isEmpty=true
        · rw [ite_eq_left he] at hr
          cases hr
        · rw [ite_eq_right he] at hr
          delta pendingRequest at hr
          split at hr
          · cases hr
            exact hp.2.2
          · cases hr
      | difference c =>
        rw [hphase] at hr hp
        dsimp only at hr hp
        by_cases he : c.target≤c.count
        · rw [ite_eq_left he] at hr
          cases hr
        · rw [ite_eq_right he] at hr
          delta pendingRequest at hr
          split at hr
          · cases hr
            exact hp.2.2.2
          · cases hr
    have freyaJobValueBound {d m : ℕ} (f : Fin m → Space d → ℝ) (A C B : ℝ)
        (hA : 0≤A) (hC : 0≤C) (hB : 0≤B)
        (hg : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖) (job : Job d m)
        (hj : freyaJobBound B job) : ‖jobValue f job‖≤2*(A+C*B) := by
      have hnonneg : 0≤A+C*B := by positivity
      dsimp only [jobValue,freyaJobBound] at hj ⊢
      generalize job.kind=kind at hj ⊢
      cases kind with
      | inl x =>
        have h := (hg job.component x).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj hC))
        linarith
      | inr xy =>
        have hx := (hg job.component xy.1).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj.1 hC))
        have hy := (hg job.component xy.2).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj.2 hC))
        have h := (norm_sub_le (gradient (f job.component) xy.1) (gradient (f job.component) xy.2)).trans
          (add_le_add hx hy)
        linarith
    have freyaPageReplyBound (q : Raw) (s : State q) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞) (answer : Option (Request q.d q.m q.n) → Reply q.d q.n)
        (hservice : answer none=none ∧ ∀ r,legalRequest τ r → ∃ i job c,
          r.pending i=some job ∧ answer (some r)=some (i,job.id,c,jobValue f job) ∧
          r.clock≤c ∧ ∀ i' j',r.pending i'=some j' → (c : ℝ≥0∞)≤deadline τ j' i')
        (hlegal : ∀ r,(query q s).2=some r → legalRequest τ r)
        (A C B : ℝ) (hA : 0≤A) (hC : 0≤C) (hB : 0≤B)
        (hg : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖) (hs : freyaStateBound B s) :
        ∀ i id t v,answer (query q s).2=some (i,id,t,v) → ‖v‖≤2*(A+C*B) := by
      intro i id t v hr
      cases hq : (query q s).2 with
      | none => rw [hq,hservice.1] at hr; cases hr
      | some r =>
        obtain ⟨j,job,c,hpend,hreply,_,_⟩ := hservice.2 r (hlegal r hq)
        rw [hq,hreply] at hr
        cases hr
        exact freyaJobValueBound f A C B hA hC hB hg job (freyaPageQueryJobBound q s B hs r hq _ job hpend)
    let freyaRunBound (q : Raw) (A C : ℝ) : ℕ → ℝ :=
      Nat.rec ‖q.x0‖ (fun _ B => (1+|q.η|)*(2*B+2*(A+C*B)))
    have freyaRunBoundNonneg (q : Raw) (A C : ℝ) (hA : 0≤A) (hC : 0≤C) :
        ∀ k,0≤freyaRunBound q A C k := by
      intro k
      induction k with
      | zero => exact norm_nonneg _
      | succ k ih =>
        change 0≤(1+|q.η|)*(2*freyaRunBound q A C k+2*(A+C*freyaRunBound q A C k))
        positivity
    have freyaRunBoundMono (q : Raw) (A C : ℝ) (hA : 0≤A) (hC : 0≤C) :
        Monotone (freyaRunBound q A C) := by
      apply monotone_nat_of_le_succ
      intro k
      have hB := freyaRunBoundNonneg q A C hA hC k
      let B := freyaRunBound q A C k
      change B≤(1+|q.η|)*(2*B+2*(A+C*B))
      have hCB : 0≤A+C*B := by positivity
      have hM : 0≤2*B+2*(A+C*B) := by positivity
      nlinarith [mul_nonneg (abs_nonneg q.η) hM]
    have freyaPageTraceBound (q : Raw) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r)))
        (hlegal : ∀ k r,(query q (trace q O seed ω k)).2=some r → legalRequest τ r)
        (A C : ℝ) (hA : 0≤A) (hC : 0≤C) (hg : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖) :
        ∀ k,freyaStateBound (freyaRunBound q A C k) (trace q O seed ω k) := by
      intro k
      induction k with
      | zero => exact freyaPageInitialBound q seed _ (norm_nonneg _) le_rfl
      | succ k ih =>
        have hB := freyaRunBoundNonneg q A C hA hC k
        let R := 2*(A+C*freyaRunBound q A C k)
        have hR : 0≤R := by dsimp [R]; positivity
        change freyaStateBound ((1+|q.η|)*(2*freyaRunBound q A C k+R))
          (update q (trace q O seed ω k) (replyAt q O seed ω k (query q (trace q O seed ω k))))
        apply freyaPageUpdateBound q _ _ R hB hR ih
        exact freyaPageReplyBound q _ f τ (fun r => replyAt q O seed ω k (0,r))
          (hservice k) (hlegal k) A C _ hA hC hB hg ih
    have freyaPageTraceQueryLegal (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k)
        (hservice : servicePath f τ (fun a r => replyAt q O seed ω a (0,r))) :
        ∀ k r,(query q (trace q O seed ω k)).2=some r → legalRequest τ r := by
      classical
      intro k r hr
      have hs := freyaPagePhaseSafety q hm hn hS hK f τ O seed ω hservice k
      let s := trace q O seed ω k
      change (query q s).2=some r at hr
      delta query at hr
      cases hp : s.phase with
      | halted => rw [hp] at hr; cases hr
      | full first c =>
        have hf := hs.1 first c hp
        rw [hp] at hr
        dsimp only at hr
        by_cases he : c.remaining.isEmpty=true
        · rw [ite_eq_left he] at hr; cases hr
        · rw [ite_eq_right he] at hr
          delta pendingRequest at hr
          split at hr
          · cases hr
            exact hf.2.2.2
          · cases hr
      | difference c =>
        have hd := (hs.2.1 c hp).2.2
        rw [hp] at hr
        dsimp only at hr
        by_cases he : c.target≤c.count
        · rw [ite_eq_left he] at hr; cases hr
        · rw [ite_eq_right he] at hr
          delta pendingRequest at hr
          split at hr
          · cases hr
            refine ⟨?_,?_⟩
            · obtain ⟨job,hjob,_,_,_⟩ := hd ⟨0,hn⟩
              exact ⟨⟨0,hn⟩,job,hjob⟩
            · intro i job hjob
              change c.pending i=some job at hjob
              obtain ⟨old,hold,hstart,hdeadline,_⟩ := hd i
              rw [hjob] at hold
              cases hold
              exact ⟨hstart,hdeadline⟩
          · cases hr
    have freyaBatchInputsBound (q : Raw) (B : ℝ) (hB : 0≤B)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
        (hb : ∀ k,k≤eventLimit q → freyaStateBound B (trace q O seed ω k)) :
        ‖(batchInputs q O seed ω batch).1‖≤B ∧ ‖(batchInputs q O seed ω batch).2‖≤B := by
      dsimp only [batchInputs,invocation]
      cases hc : batchStartCall q O seed ω batch with
      | none => simpa (config := { iota := false }) only [Option.bind_none,Option.map_none,Option.getD_none,norm_zero] using And.intro hB hB
      | some call =>
        have hs := hb call (freyaPageBatchStartFacts q O seed ω batch call hc).1
        have hp := hs.2.2.2
        dsimp only [Option.bind_some]
        generalize (trace q O seed ω call).phase = phase at hp ⊢
        cases phase with
        | halted =>
          change ‖(0 : Space q.d)‖≤B ∧ ‖(0 : Space q.d)‖≤B
          simpa (config := { iota := false }) only [norm_zero] using And.intro hB hB
        | full first c => exact ⟨hp.1,hp.1⟩
        | difference c => exact ⟨hp.1,hp.2.1⟩
    have freyaGradientGrowth {d m : ℕ} (hm : 0<m) (f : Fin m → Space d → ℝ) (L : ℝ)
        (hmean : ∀ x y,(m : ℝ)⁻¹*(∑ i,‖gradient (f i) x-gradient (f i) y‖^2)≤L^2*‖x-y‖^2) :
        ∀ i x,‖gradient (f i) x‖≤(∑ j,‖gradient (f j) 0‖)+Real.sqrt m * |L| * ‖x‖ := by
      intro i x
      have hbase : ‖gradient (f i) 0‖≤∑ j,‖gradient (f j) 0‖ :=
        Finset.single_le_sum (f:=fun j : Fin m => ‖gradient (f j) 0‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have hd := freyaComponentBound hm f L hmean i x 0
      rw [sub_zero] at hd
      have h := (norm_le_norm_sub_add (gradient (f i) x) (gradient (f i) 0)).trans (add_le_add hd hbase)
      linarith
    have freyaAverageErrorBound {d m S : ℕ} (f : Fin m → Space d → ℝ)
        (hf : ∀ i,Differentiable ℝ (f i)) (x y : Space d) (labels : Fin S → Option (Fin m))
        (G : ℝ) (hG : 0≤G) (hx : ∀ i,‖gradient (f i) x‖≤G) (hy : ∀ i,‖gradient (f i) y‖≤G) :
        ‖(S : ℝ)⁻¹ • (∑ j : Fin S,(labels j).elim 0 (fun i => gradient (f i) x-gradient (f i) y))-
          (gradient (objective f) x-gradient (objective f) y)‖≤(S+m : ℝ)*(2*G) := by
      have hdiff (i : Fin m) : ‖gradient (f i) x-gradient (f i) y‖≤2*G := by
        have h := (norm_sub_le (gradient (f i) x) (gradient (f i) y)).trans (add_le_add (hx i) (hy i))
        linarith
      have hsample : ‖(S : ℝ)⁻¹ • (∑ j : Fin S,(labels j).elim 0
          (fun i => gradient (f i) x-gradient (f i) y))‖≤(S : ℝ)*(2*G) := by
        rw [norm_smul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (freyaInverseNatNorm S)).trans
        calc
          ‖∑ j : Fin S,(labels j).elim 0 (fun i => gradient (f i) x-gradient (f i) y)‖
              ≤∑ j : Fin S,‖(labels j).elim 0 (fun i => gradient (f i) x-gradient (f i) y)‖ := norm_sum_le _ _
          _≤∑ _j : Fin S,2*G := by
            apply Finset.sum_le_sum
            intro j _
            cases labels j with
            | none => simpa (config := { iota := false }) only [Option.elim_none,norm_zero] using mul_nonneg (by norm_num : (0 : ℝ)≤2) hG
            | some i => exact hdiff i
          _=(S : ℝ)*(2*G) := by simp (config := { iota := false })
      have hobj : ‖gradient (objective f) x-gradient (objective f) y‖≤(m : ℝ)*(2*G) := by
        rw [freyaObjectiveGradient f hf x,freyaObjectiveGradient f hf y,← smul_sub,← Finset.sum_sub_distrib,norm_smul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (freyaInverseNatNorm m)).trans
        calc
          ‖∑ i,(gradient (f i) x-gradient (f i) y)‖≤∑ i,‖gradient (f i) x-gradient (f i) y‖ := norm_sum_le _ _
          _≤∑ _i : Fin m,2*G := Finset.sum_le_sum (fun i _ => hdiff i)
          _=(m : ℝ)*(2*G) := by simp (config := { iota := false })
      have h := (norm_sub_le _ _).trans (add_le_add hsample hobj)
      nlinarith
    have freyaBatchInputsAEBounded (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ) (L : ℝ)
        (hmean : ∀ x y,(q.m : ℝ)⁻¹*(∑ i,‖gradient (f i) x-gradient (f i) y‖^2)≤L^2*‖x-y‖^2)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ) :
        ∃ B : ℝ,0≤B ∧ ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
          ‖(batchInputs q O z.1 z.2 batch).1‖≤B ∧ ‖(batchInputs q O z.1 z.2 batch).2‖≤B := by
      let A := ∑ i,‖gradient (f i) 0‖
      let C := Real.sqrt q.m * |L|
      have hA : 0≤A := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hC : 0≤C := by dsimp [C]; positivity
      have hg : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖ := freyaGradientGrowth hm f L hmean
      let B := freyaRunBound q A C (eventLimit q)
      have hB : 0≤B := freyaRunBoundNonneg q A C hA hC _
      refine ⟨B,hB,?_⟩
      have hs : ∀ᵐ z ∂(executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k))),
          servicePath f τ (fun a r => replyAt q O z.1 z.2 a (0,r)) :=
        (measurePreserving_snd.quasiMeasurePreserving.ae hservice.2).mono
          fun z hz => servicePath_replyAt z.1 hz
      filter_upwards [hs] with z hz
      apply freyaBatchInputsBound q B hB O z.1 z.2 batch
      intro k hk
      apply freyaStateBoundMono (freyaRunBoundMono q A C hA hC hk)
      exact freyaPageTraceBound q f τ O z.1 z.2 hz
        (freyaPageTraceQueryLegal q hm hn hS hK f τ O z.1 z.2 hz) A C hA hC hg k
    have freyaBatchErrorIntegrable (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (lower Lminus Lplus Lpm Δ : ℝ) (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ)
        (hH : historyBefore q O batch ≤ (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))))
        (hl : Measurable (fun z : Seed q.K × ((k : ℕ) → O.Seed k) => completedLabels q O z.1 z.2 batch)) :
        let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
        Integrable (batchError q f O batch) P ∧
          Integrable (fun z => ‖batchError q f O batch z‖^2) P ∧
          Integrable (fun z => ‖(batchInputs q O z.1 z.2 batch).1-(batchInputs q O z.1 z.2 batch).2‖^2) P := by
      classical
      let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
      obtain ⟨B,hB,hxy⟩ := freyaBatchInputsAEBounded q hm hn hS hK f Lplus hreg.mean_square τ O hservice batch
      let A := ∑ i,‖gradient (f i) 0‖
      let C := Real.sqrt q.m * |Lplus|
      let G := A+C*B
      let M := (q.S+q.m : ℝ)*(2*G)
      have hA : 0≤A := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hC : 0≤C := by dsimp [C]; positivity
      have hG : 0≤G := by dsimp [G]; positivity
      have hM : 0≤M := by dsimp [M]; positivity
      have hg : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖ := freyaGradientGrowth hm f Lplus hreg.mean_square
      have hb : ∀ᵐ z ∂P,‖batchError q f O batch z‖≤M := by
        filter_upwards [hxy,freyaBatchErrorAverage q hm hn hS hK f τ O hservice batch] with z hz he
        rw [he]
        by_cases hd : isDifferenceBatch q O z batch
        · rw [ite_eq_left hd]
          exact freyaAverageErrorBound f hreg.differentiable _ _ _ G hG
            (fun i => (hg i _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz.1 hC)))
            (fun i => (hg i _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz.2 hC)))
        · rw [ite_eq_right hd,norm_zero]
          exact hM
      have ha := freyaBatchErrorAEStrong q hm hn hS hK f lower Lminus Lplus Lpm Δ hreg τ O hservice batch hH hl
      refine ⟨(integrable_const M).mono' ha hb,?_,?_⟩
      · apply (integrable_const (M^2)).mono' (ha.norm.pow 2)
        filter_upwards [hb] with z hz
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hz 2
      · have hmxy := (freyaBatchInputsHistoryMeas q O batch).mono hH le_rfl
        apply (integrable_const ((2*B)^2)).mono' ((hmxy.fst.sub hmxy.snd).norm.pow_const 2).aestronglyMeasurable
        filter_upwards [hxy] with z hz
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        change ‖(batchInputs q O z.1 z.2 batch).1-(batchInputs q O z.1 z.2 batch).2‖≤2*B
        have h := (norm_sub_le _ _).trans (add_le_add hz.1 hz.2)
        linarith
    have freyaWeightedEventIntegral {Ω V : Type} [mΩ : MeasurableSpace Ω]
        [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (μ : Measure Ω) (H : MeasurableSpace Ω) (hH : H≤mΩ) (B D E : Set Ω)
        (hE : MeasurableSet[H] E) (hEB : E⊆B) (c : ℝ≥0∞)
        (hlaw : ∀ T,MeasurableSet[H] T → T⊆B → μ (T∩D)=μ T*c)
        (g : Ω → V) (hg : StronglyMeasurable[H] g) :
        (∫ z in E∩D,g z ∂μ)=c.toReal • (∫ z in E,g z ∂μ) := by
      let : MeasurableSpace Ω := mΩ
      have he : (μ.restrict (E∩D)).trim hH=c • (μ.restrict E).trim hH := by
        let : MeasurableSpace Ω := H
        apply Measure.ext
        intro T hT
        rw [trim_measurableSet_eq hH hT,Measure.smul_apply,
          trim_measurableSet_eq hH hT,Measure.restrict_apply (hH _ hT),
          Measure.restrict_apply (hH _ hT)]
        simpa (config := { iota := false }) only [Set.inter_assoc,mul_comm,smul_eq_mul] using hlaw (T∩E) (hT.inter hE) (fun z hz => hEB hz.2)
      rw [integral_trim hH hg,he,integral_smul_measure,← integral_trim hH hg]
    have freyaFiniteConditionalAverage {Ω α β V : Type} [mΩ : MeasurableSpace Ω]
        [Fintype α] [MeasurableSpace β] [MeasurableSingletonClass β]
        [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
        (μ : Measure Ω) (H : MeasurableSpace Ω) (hH : H≤mΩ) (B E : Set Ω)
        (hE : MeasurableSet[H] E) (hEB : E⊆B) (c : ℝ≥0∞)
        (X : Ω → β) (hX : Measurable[mΩ] X) (encode : α → β) (hinj : Function.Injective encode)
        (hlaw : ∀ a T,MeasurableSet[H] T → T⊆B → μ (T∩{z | X z=encode a})=μ T*c)
        (hcover : ∀ᵐ z ∂μ,z∈E → ∃ a,X z=encode a)
        (F : Ω → V) (g : α → Ω → V)
        (hg : ∀ a,StronglyMeasurable[H] (g a)) (hint : ∀ a,Integrable (g a) (μ.restrict E))
        (hF : ∀ᵐ z ∂μ,∀ a,z∈E → X z=encode a → F z=g a z) :
        (∫ z in E,F z ∂μ)=c.toReal • (∫ z in E,∑ a,g a z ∂μ) := by
      classical
      let : MeasurableSpace Ω := mΩ
      let D := fun a => {z | X z=encode a}
      have hD (a : α) : MeasurableSet (D a) := hX (measurableSet_singleton (encode a))
      have hsplit : (∫ z in E,F z ∂μ)=(∫ z in E,∑ a,(D a).indicator (g a) z ∂μ) := by
        apply setIntegral_congr_ae (hH _ hE)
        filter_upwards [hcover,hF] with z hz hf hzE
        obtain ⟨a,ha⟩ := hz hzE
        rw [Finset.sum_eq_single a]
        · rw [Set.indicator_of_mem (show z∈D a from ha)]
          exact hf a hzE ha
        · intro b _ hba
          apply Set.indicator_of_notMem
          intro hb
          exact hba (hinj (hb.symm.trans ha))
        · intro ha
          exact (ha (Finset.mem_univ a)).elim
      rw [hsplit,integral_finsetSum _ (fun a _ => (hint a).indicator (hD a))]
      calc
        (∑ a,∫ z in E,(D a).indicator (g a) z ∂μ)
            =∑ a,c.toReal • (∫ z in E,g a z ∂μ) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [setIntegral_indicator (hD a)]
              exact freyaWeightedEventIntegral μ H hH B (D a) E hE hEB c (hlaw a) (g a) (hg a)
        _=c.toReal • (∫ z in E,∑ a,g a z ∂μ) := by
          rw [← Finset.smul_sum,integral_finsetSum _ (fun a _ => hint a)]
    have freyaFiniteVectorMoments {d m S : ℕ} (hm : 0<m) (hS : 0<S)
        (f : Fin m → Space d → ℝ) (hf : ∀ i,Differentiable ℝ (f i))
        (D : ℝ) (x y : Space d)
        (hvar : (m : ℝ)⁻¹*(∑ i,‖gradient (f i) x-gradient (f i) y‖^2)-
          ‖gradient (objective f) x-gradient (objective f) y‖^2≤D^2*‖x-y‖^2) :
        let e := fun v : Fin S → Fin m => (S : ℝ)⁻¹ •
          (∑ j : Fin S,(gradient (f (v j)) x-gradient (f (v j)) y))-
          (gradient (objective f) x-gradient (objective f) y)
        (((m : ℝ≥0∞)^S)⁻¹).toReal • (∑ v,e v)=0 ∧
          (((m : ℝ≥0∞)^S)⁻¹).toReal * (∑ v,‖e v‖^2)≤D^2/S*‖x-y‖^2 := by
      classical
      let : NeZero m := ⟨hm.ne'⟩
      let μ := (PMF.uniformOfFintype (Fin m)).toMeasure
      let ν := Measure.pi (fun _ : Fin S => μ)
      let P : ProbabilityMeasure (Fin S → Fin m) := ⟨ν,inferInstance⟩
      let v := fun i => gradient (f i) x-gradient (f i) y
      let u := gradient (objective f) x-gradient (objective f) y
      let avg := fun r : Fin S → Fin m => (S : ℝ)⁻¹ • ∑ j,v (r j)
      have hu : (m : ℝ)⁻¹ • (∑ i,v i)=u := by
        dsimp only [u,v]
        rw [freyaObjectiveGradient f hf x,freyaObjectiveGradient f hf y,
          Finset.sum_sub_distrib,smul_sub]
      have hmoment := LongTails.Proofs.FreyaMoments.uniform_centered_second_moment P hS v
        (fun j r => r j) (fun j => measurable_pi_apply j)
        (fun j => ⟨(measurable_pi_apply j).aemeasurable,
          (measurePreserving_eval (fun _ : Fin S => μ) j).map_eq⟩)
        (iIndepFun_pi (fun _ : Fin S =>
          (measurable_id : Measurable (id : Fin m → Fin m)).aemeasurable))
      rw [hu] at hmoment
      have hmass (r : Fin S → Fin m) : ν {r}=((m : ℝ≥0∞)^S)⁻¹ := by
        simp (config := { iota := false }) [ν,μ,Measure.pi_singleton,PMF.uniformOfFintype_apply,ENNReal.inv_pow]
      have hzero : (∫ r,avg r-u ∂ν)=0 := by
        rw [integral_sub Integrable.of_finite Integrable.of_finite]
        simpa (config := { iota := false }) [P,avg] using congrArg (fun a : Space d => a-u) hmoment.2.1
      have hsecond : (∫ r,‖avg r-u‖^2 ∂ν)≤D^2/S*‖x-y‖^2 := by
        have he := hmoment.2.2.2
        change (∫ r,‖avg r-u‖^2 ∂ν)=_ at he
        rw [he]
        simpa (config := { iota := false }) only [v,u,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
          mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr (Nat.cast_nonneg S : (0 : ℝ)≤S))
      rw [integral_fintype Integrable.of_finite] at hzero hsecond
      simp (config := { iota := false }) only [Measure.real,hmass,← Finset.smul_sum] at hzero
      simp (config := { iota := false }) only [Measure.real,hmass,smul_eq_mul,← Finset.mul_sum] at hsecond
      exact ⟨hzero,hsecond⟩
    have freyaFixedVectorRegularity (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (f : Fin q.m → Space q.d → ℝ)
        (lower Lminus Lplus Lpm Δ : ℝ) (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
        (τ : Fin q.n → ℝ≥0∞) (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (batch : ℕ)
        (hH : historyBefore q O batch ≤ (inferInstance : MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k))))
        (v : Fin q.S → Fin q.m) :
        let e := fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
          (q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(gradient (f (v j)) (batchInputs q O z.1 z.2 batch).1-
            gradient (f (v j)) (batchInputs q O z.1 z.2 batch).2))-
          (gradient (objective f) (batchInputs q O z.1 z.2 batch).1-
            gradient (objective f) (batchInputs q O z.1 z.2 batch).2)
        StronglyMeasurable[historyBefore q O batch] e ∧
          Integrable e (executionLaw q O : Measure _) ∧
          Integrable (fun z => ‖e z‖^2) (executionLaw q O : Measure _) := by
      classical
      let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
      let xy := fun z : Ω => batchInputs q O z.1 z.2 batch
      let e := fun z : Ω => (q.S : ℝ)⁻¹ •
        (∑ j : Fin q.S,(gradient (f (v j)) (xy z).1-gradient (f (v j)) (xy z).2))-
        (gradient (objective f) (xy z).1-gradient (objective f) (xy z).2)
      have hg := freyaComponentMeas hm f Lplus hreg.mean_square
      have hmean : Measurable (gradient (objective f)) := by
        have h : Measurable (fun x => (q.m : ℝ)⁻¹ • ∑ i,gradient (f i) x) :=
          (Finset.measurable_sum Finset.univ (fun i _ => hg i)).const_smul ((q.m : ℝ)⁻¹)
        convert h using 1
        funext x
        exact freyaObjectiveGradient f hreg.differentiable x
      have he : Measurable[historyBefore q O batch] e := by
        have hxy := freyaBatchInputsHistoryMeas q O batch
        exact ((Finset.measurable_sum Finset.univ (fun j _ =>
          ((hg (v j)).comp hxy.fst).sub ((hg (v j)).comp hxy.snd))).const_smul ((q.S : ℝ)⁻¹)).sub
          ((hmean.comp hxy.fst).sub (hmean.comp hxy.snd))
      obtain ⟨B,hB,hxy⟩ := freyaBatchInputsAEBounded q hm hn hS hK f Lplus hreg.mean_square τ O hservice batch
      let A := ∑ i,‖gradient (f i) 0‖
      let C := Real.sqrt q.m * |Lplus|
      let G := A+C*B
      let M := (q.S+q.m : ℝ)*(2*G)
      have hA : 0≤A := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hC : 0≤C := by dsimp [C]; positivity
      have hG : 0≤G := by dsimp [G]; positivity
      have hgrad : ∀ i x,‖gradient (f i) x‖≤A+C*‖x‖ := freyaGradientGrowth hm f Lplus hreg.mean_square
      have hb : ∀ᵐ z ∂(executionLaw q O : Measure Ω),‖e z‖≤M := by
        filter_upwards [hxy] with z hz
        exact freyaAverageErrorBound f hreg.differentiable _ _ (fun j => some (v j)) G hG
          (fun i => (hgrad i _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz.1 hC)))
          (fun i => (hgrad i _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hz.2 hC)))
      have ha : AEStronglyMeasurable e (executionLaw q O : Measure Ω) :=
        (he.mono hH le_rfl).aestronglyMeasurable
      refine ⟨he.stronglyMeasurable,(integrable_const M).mono' ha hb,?_⟩
      apply (integrable_const (M^2)).mono' (ha.norm.pow 2)
      filter_upwards [hb] with z hz
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hz 2
    have freyaDifferenceMoments (q : Raw) (hm : 0<q.m) (hn : 0<q.n)
        (hS : 0<q.S) (hK : 0<q.K) (hρ : 0<q.ρ) (hρone : q.ρ≤1)
        (f : Fin q.m → Space q.d → ℝ) (lower Lminus Lplus Lpm Δ : ℝ)
        (hreg : RegularObjective f q.x0 lower Lminus Lplus Lpm Δ)
        (τ : Fin q.n → ℝ≥0∞)
        (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
        (hservice : PrimitiveService f τ O) (hind : batchScheduleIndependent q f τ O)
        (batch : ℕ) :
        let P := (executionLaw q O : Measure (Seed q.K × ((k : ℕ) → O.Seed k)))
        let error := batchError q f O batch
        Integrable error P ∧ Integrable (fun z => ‖error z‖^2) P ∧
          ∀ E,MeasurableSet[historyBefore q O batch] E →
            (∀ z∈E,isDifferenceBatch q O z batch) →
            (∫ z in E,error z ∂P)=0 ∧
              (∫ z in E,‖error z‖^2 ∂P)≤Lpm^2/q.S*
                (∫ z in E,‖(batchInputs q O z.1 z.2 batch).1-
                  (batchInputs q O z.1 z.2 batch).2‖^2 ∂P) := by
      classical
      let : MeasurableSingletonClass (Option (Fin q.m)) := freyaOptionSingleton
      let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
      let ambient := (inferInstance : MeasurableSpace Ω)
      let P := (executionLaw q O : Measure Ω)
      let H := historyBefore q O batch
      let : MeasurableSpace Ω := ambient
      let B := {z : Ω | isDifferenceBatch q O z batch}
      let X := fun z : Ω => completedLabels q O z.1 z.2 batch
      let encode := fun v : Fin q.S → Fin q.m => fun j => some (v j)
      let xy := fun z : Ω => batchInputs q O z.1 z.2 batch
      let g := fun (v : Fin q.S → Fin q.m) (z : Ω) => (q.S : ℝ)⁻¹ •
        (∑ j : Fin q.S,(gradient (f (v j)) (xy z).1-gradient (f (v j)) (xy z).2))-
        (gradient (objective f) (xy z).1-gradient (objective f) (xy z).2)
      let c : ℝ≥0∞ := ((q.m : ℝ≥0∞)^q.S)⁻¹
      have hH := (hind batch).1
      have hlabels := completed_labels_iid q hm hn hS hK hρ hρone f τ O hservice hind batch
      have hi := freyaBatchErrorIntegrable q hm hn hS hK f lower Lminus Lplus Lpm Δ hreg τ O hservice batch hH hlabels.1
      refine ⟨hi.1,hi.2.1,?_⟩
      intro E hE hEB
      have hregg (v : Fin q.S → Fin q.m) :
          StronglyMeasurable[H] (g v) ∧ Integrable (g v) P ∧ Integrable (fun z => ‖g v z‖^2) P :=
        freyaFixedVectorRegularity q hm hn hS hK f lower Lminus Lplus Lpm Δ hreg τ O hservice batch hH v
      have hinj : Function.Injective encode := by
        intro v w he
        funext j
        exact Option.some.inj (congrFun he j)
      have hlaw : ∀ v T,MeasurableSet[H] T → T⊆B → P (T∩{z | X z=encode v})=P T*c := by
        intro v T hT hTB
        exact hlabels.2.2 T hT hTB v
      have hcover : ∀ᵐ z ∂P,z∈E → ∃ v,X z=encode v := by
        filter_upwards [hlabels.2.1] with z hz hzE
        have hh := hz (hEB z hzE)
        have hex : ∀ j : Fin q.S,∃ i : Fin q.m,X z j=some i := by
          intro j
          exact Option.isSome_iff_exists.mp (hh j)
        choose v hv using hex
        exact ⟨v,funext hv⟩
      have hF : ∀ᵐ z ∂P,∀ v,z∈E → X z=encode v → batchError q f O batch z=g v z := by
        filter_upwards [freyaBatchErrorAverage q hm hn hS hK f τ O hservice batch] with z hz v hzE he
        rw [hz,ite_eq_left (hEB z hzE)]
        change (q.S : ℝ)⁻¹ • (∑ j : Fin q.S,(X z j).elim 0
          (fun i => gradient (f i) (xy z).1-gradient (f i) (xy z).2))-
          (gradient (objective f) (xy z).1-gradient (objective f) (xy z).2)=g v z
        rw [he]
        rfl
      have havg := freyaFiniteConditionalAverage P H hH B E hE hEB c X hlabels.1 encode hinj
        hlaw hcover (batchError q f O batch) g (fun v => (hregg v).1)
        (fun v => (hregg v).2.1.restrict) hF
      have havg2 := freyaFiniteConditionalAverage P H hH B E hE hEB c X hlabels.1 encode hinj
        hlaw hcover (fun z => ‖batchError q f O batch z‖^2) (fun v z => ‖g v z‖^2)
        (fun v => (hregg v).1.norm.pow 2) (fun v => (hregg v).2.2.restrict)
        (by filter_upwards [hF] with z hz v hzE he; rw [hz v hzE he])
      have hmom (z : Ω) : c.toReal • (∑ v,g v z)=0 ∧
          c.toReal*(∑ v,‖g v z‖^2)≤Lpm^2/q.S*‖(xy z).1-(xy z).2‖^2 :=
        freyaFiniteVectorMoments hm hS f hreg.differentiable Lpm (xy z).1 (xy z).2 (hreg.centered _ _)
      constructor
      · rw [havg,← integral_smul]
        simp (config := { iota := false }) only [(hmom _).1,integral_zero]
      · rw [havg2,smul_eq_mul,← integral_const_mul,← integral_const_mul]
        apply integral_mono
        · exact ((integrable_finsetSum _ (fun v _ => (hregg v).2.2.restrict)).const_mul c.toReal)
        · exact hi.2.2.restrict.const_mul (Lpm^2/q.S)
        · intro z
          exact (hmom z).2
    exact freyaDifferenceMoments q hm hn hS hK hρ hρone f lower Lminus Lplus Lpm Δ hreg τ O hservice hind batch


end LongTails.Proofs.FreyaCollectors
