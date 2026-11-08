import LongTails.Algorithms.BirchCollectionLocal
import LongTails.Proofs.BirchCollectionPrivatePacket

namespace LongTails.Proofs.BirchCollectionLocalTrace

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionPrivatePacket

structure Forest {m : ℕ} (s : Round m) (start B : ℕ) (move : ℝ) : Prop where
  count : s.trace.nextDirection = start + s.completed
  base : s.base < s.trace.nextState
  marker : s.trace.markers.getLast?.getD 0 = s.base
  baseHistory : (s.trace.states s.base).history = range start
  head : ∀ w, s.head w < s.trace.nextState
  headPrefix : ∀ w, range start ⊆ (s.trace.states (s.head w)).history
  headPast : ∀ w, (s.trace.states (s.head w)).history ⊆ range s.trace.nextDirection
  disjoint : ∀ w v, w ≠ v → (s.trace.states (s.head w)).history ∩
    (s.trace.states (s.head v)).history = range start
  covered : ∀ q ∈ range s.trace.nextDirection, q ∈ range start ∨
    ∃ w, q ∈ (s.trace.states (s.head w)).history
  direction : ∀ n, start ≤ n → n < s.trace.nextDirection →
    range start ⊆ (s.trace.directions n).history ∧
      (s.trace.directions n).history ⊆ range n ∧ (s.trace.directions n).refresh = 1 ∧
      (s.trace.directions n).movement = move ∧ (s.trace.directions n).raw.length = B

structure Data {m : ℕ} (s : Round m) (start B : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  forest : Forest s start B move
  ticket : ∀ w (t : Ticket), s.pending w = some t →
    PrivateTicket s.trace t.collection t.firstRaw (w.val + 1) (s.head w) B move
  distinct : ∀ w v (t u : Ticket), s.pending w = some t → s.pending v = some u →
    w ≠ v → t.collection ≠ u.collection

lemma forest_same {m start B : ℕ} {move : ℝ} {s t : Round m} (h : Forest s start B move)
    (hbase : t.base = s.base) (hhead : t.head = s.head) (hcomplete : t.completed = s.completed)
    (hcount : t.trace.nextDirection = s.trace.nextDirection)
    (hsc : t.trace.nextState = s.trace.nextState) (hstates : t.trace.states = s.trace.states)
    (hdirs : t.trace.directions = s.trace.directions) (hmarks : t.trace.markers = s.trace.markers) :
    Forest t start B move := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcount, hcomplete]
    exact h.count
  · rw [hbase, hsc]
    exact h.base
  · rw [hbase, hmarks]
    exact h.marker
  · rw [hbase, hstates]
    exact h.baseHistory
  · rw [hhead, hsc]
    exact h.head
  · rw [hhead, hstates]
    exact h.headPrefix
  · rw [hhead, hstates, hcount]
    exact h.headPast
  · rw [hhead, hstates]
    exact h.disjoint
  · rw [hhead, hstates, hcount]
    exact h.covered
  · rw [hdirs, hcount]
    exact h.direction

lemma round_initial (m B : ℕ) (move : ℝ) (s : TraceState) (events : List Event)
    (hr : run events = s) (hv : ValidFrom (m + 1) {} events) (hret : RetiredPast s)
    (hb : s.markers.getLast?.getD 0 < s.nextState)
    (hh : (s.states (s.markers.getLast?.getD 0)).history = range s.nextDirection) :
    Data (Round.initial m s events) s.nextDirection B move := by
  refine ⟨hr, hv, hret, ⟨by simp [Round.initial], hb, rfl, hh, fun _ => hb, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · intro _
    change range s.nextDirection ⊆ (s.states (s.markers.getLast?.getD 0)).history
    rw [hh]
  · intro _
    change (s.states (s.markers.getLast?.getD 0)).history ⊆ range s.nextDirection
    rw [hh]
  · intro _ _ _
    change (s.states (s.markers.getLast?.getD 0)).history ∩
      (s.states (s.markers.getLast?.getD 0)).history = range s.nextDirection
    rw [hh, inter_self]
  · exact fun _ h => Or.inl h
  · intro n hn hn'
    exact (not_lt_of_ge hn hn').elim
  · simp [Round.initial]
  · simp [Round.initial]

lemma append_legal {m start B : ℕ} {move : ℝ} {s : Round m} (hs : Data s start B move)
    (events : List Event) (he : ValidFrom (m + 1) s.trace events) :
    run (s.append events).events = (s.append events).trace ∧
      ValidFrom (m + 1) {} (s.append events).events ∧ RetiredPast (s.append events).trace := by
  have hr : run (s.events ++ events) = events.foldl step (run s.events) := List.foldl_append
  rw [hs.represented] at hr
  have hv : ValidFrom (m + 1) {} (s.events ++ events) := by
    apply (valid_append _ _ _ _).2
    refine ⟨hs.legal, ?_⟩
    change ValidFrom (m + 1) (run s.events) events
    rwa [hs.represented]
  exact ⟨hr, hv, retired_past_fold _ _ _ hs.retired he⟩

lemma query_data {m start B : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s start B move) (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1) :
    Data (advance B move s (.query w)) start B move := by
  let es := localCapture B move s w
  let out := advance B move s (.query w)
  let t := step s.trace (.capture (w.val + 1) (s.head w) B 1 move)
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hi, hn⟩ := launch_private (m + 1) s.trace (w.val + 1) (s.head w) B move
    (Nat.succ_lt_succ w.isLt) (hs.forest.head w) hB hm0 hm1 hs.retired
  change IssueData t out.trace s.trace.nextCollection (w.val + 1) B at hi
  have hfield := hi.fields
  have hcoll : out.trace.nextCollection = s.trace.nextCollection + 1 :=
    congrArg TraceState.nextCollection hfield
  have ht (v : Fin m) : out.pending v = Function.update s.pending w (some ticket) v := rfl
  obtain ⟨hr, hv', hret⟩ := append_legal hs es hv
  change Data out start B move
  refine ⟨hr, hv', hret, forest_same hs.forest rfl rfl rfl
    (by simpa only [t, step] using congrArg TraceState.nextDirection hfield)
    (by simpa only [t, step] using congrArg TraceState.nextState hfield)
    (by simpa only [t, step] using congrArg TraceState.states hfield)
    (by simpa only [t, step] using congrArg TraceState.directions hfield)
    (by simpa only [t, step] using congrArg TraceState.markers hfield), ?_, ?_⟩
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [ht, Function.update_self, Option.some.injEq] at hj
      subst j
      exact hn
    · rw [ht, Function.update_of_ne he] at hj
      have hp := hs.ticket v j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hcoll]
        exact hp.collection.trans (Nat.lt_succ_self _)
      · rw [congrArg TraceState.collections hfield]
        change Function.update s.trace.collections s.trace.nextCollection _ j.collection = _
        rw [Function.update_of_ne (Nat.ne_of_lt hp.collection)]
        exact hp.header
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := hp.raw q hq
        refine ⟨?_, ?_, ?_⟩
        · rw [hi.nextRaw]
          exact hqr.trans_le (Nat.le_add_right _ _)
        · rw [congrArg TraceState.retired hfield]
          exact hqf
        · rw [hi.oldRaw q hqr]
          exact hqc
  · intro v u j j' hj hj' hne
    by_cases h₁ : v = w
    · subst v
      have h₂ : u ≠ w := Ne.symm hne
      rw [ht, Function.update_self, Option.some.injEq] at hj
      rw [ht, Function.update_of_ne h₂] at hj'
      subst j
      exact Nat.ne_of_gt (hs.ticket u j' hj').collection
    · rw [ht, Function.update_of_ne h₁] at hj
      by_cases h₂ : u = w
      · subst u
        rw [ht, Function.update_self, Option.some.injEq] at hj'
        subst j'
        exact Nat.ne_of_lt (hs.ticket v j hj).collection
      · rw [ht, Function.update_of_ne h₂] at hj'
        exact hs.distinct v u j j' hj hj' hne

structure ForestStep {m : ℕ} (s out : Round m) (w : Fin m) (start B : ℕ) (move : ℝ) : Prop where
  nextDirection : out.trace.nextDirection = s.trace.nextDirection + 1
  stateCount : s.trace.nextState ≤ out.trace.nextState
  oldState : ∀ i < s.trace.nextState, out.trace.states i = s.trace.states i
  oldDirection : ∀ i < s.trace.nextDirection, out.trace.directions i = s.trace.directions i
  markers : out.trace.markers = s.trace.markers
  base : out.base = s.base
  completed : out.completed = s.completed + 1
  otherHead : ∀ v ≠ w, out.head v = s.head v
  headBound : out.head w < out.trace.nextState
  newHistory : (out.trace.states (out.head w)).history =
    insert s.trace.nextDirection (s.trace.states (s.head w)).history
  newDirection : let d := out.trace.directions s.trace.nextDirection
    range start ⊆ d.history ∧ d.history ⊆ range s.trace.nextDirection ∧ d.refresh = 1 ∧
      d.movement = move ∧ d.raw.length = B

lemma forest_step {m start B : ℕ} {move : ℝ} {s out : Round m} (w : Fin m)
    (hs : Forest s start B move) (hf : ForestStep s out w start B move) : Forest out start B move := by
  let n := s.trace.nextDirection
  have old (v : Fin m) : (s.trace.states (s.head v)).history ⊆ range n := hs.headPast v
  have latest (v : Fin m) : n ∉ (s.trace.states (s.head v)).history :=
    fun h => (Nat.lt_irrefl n (mem_range.mp (old v h))).elim
  have hnew : (out.trace.states (out.head w)).history =
      insert n (s.trace.states (s.head w)).history := hf.newHistory
  have hkeep (v : Fin m) (hne : v ≠ w) :
      (out.trace.states (out.head v)).history = (s.trace.states (s.head v)).history := by
    rw [hf.otherHead v hne, hf.oldState _ (hs.head v)]
  have hmono (v : Fin m) : (s.trace.states (s.head v)).history ⊆
      (out.trace.states (out.head v)).history := by
    by_cases h : v = w
    · subst v
      rw [hnew]
      exact subset_insert _ _
    · rw [hkeep v h]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun v => (hs.headPrefix v).trans (hmono v), ?_, ?_, ?_, ?_⟩
  · rw [hf.nextDirection, hs.count, hf.completed, Nat.add_assoc]
  · rw [hf.base]
    exact hs.base.trans_le hf.stateCount
  · rw [hf.markers, hf.base, hs.marker]
  · rw [hf.base, hf.oldState _ hs.base, hs.baseHistory]
  · intro v
    by_cases h : v = w
    · subst v
      exact hf.headBound
    · rw [hf.otherHead v h]
      exact (hs.head v).trans_le hf.stateCount
  · intro v
    rw [hf.nextDirection]
    by_cases h : v = w
    · subst v
      rw [hnew]
      exact insert_subset (mem_range.mpr (Nat.lt_succ_self _))
        ((old w).trans (range_mono (Nat.le_succ _)))
    · rw [hkeep v h]
      exact (old v).trans (range_mono (Nat.le_succ _))
  · intro v u hne
    by_cases h : v = w
    · subst v
      have hu : u ≠ w := Ne.symm hne
      rw [hnew, hkeep u hu, ← hs.disjoint w u hne]
      ext q
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hq, hqu⟩
        · exact (latest u hqu).elim
        · exact ⟨hq, hqu⟩
      · rintro ⟨hq, hu⟩
        exact ⟨Or.inr hq, hu⟩
    · rw [hkeep v h]
      by_cases hu : u = w
      · subst u
        rw [hnew, ← hs.disjoint v w hne]
        ext q
        simp only [mem_inter, mem_insert]
        constructor
        · rintro ⟨hq, rfl | hw⟩
          · exact (latest v hq).elim
          · exact ⟨hq, hw⟩
        · rintro ⟨hq, hw⟩
          exact ⟨hq, Or.inr hw⟩
      · rw [hkeep u hu]
        exact hs.disjoint v u hne
  · intro q hq
    rw [hf.nextDirection] at hq
    have hle : q ≤ n := Nat.le_of_lt_succ (mem_range.mp hq)
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact Or.inr ⟨w, by rw [hnew]; exact mem_insert_self _ _⟩
    · rcases hs.covered q (mem_range.mpr hlt) with hh | ⟨v, hv⟩
      · exact Or.inl hh
      · exact Or.inr ⟨v, hmono v hv⟩
  · intro j hj hlt
    rw [hf.nextDirection] at hlt
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · exact hf.newDirection
    · rw [hf.oldDirection _ hlt']
      exact hs.direction j hj hlt'

lemma forest_finish {m start B : ℕ} {move : ℝ} {s out : Round m} (w : Fin m) (t : Ticket)
    (hs : Forest s start B move)
    (hf : FinishData s.trace out.trace t.collection t.firstRaw (w.val + 1) (s.head w) B move)
    (hb : out.base = s.base) (hc : out.completed = s.completed + 1)
    (hh : out.head = Function.update s.head w s.trace.nextState) :
    Forest out start B move := by
  apply forest_step w hs
  refine ⟨hf.nextDirection, hf.nextState.symm ▸ Nat.le_succ _, hf.oldState, hf.oldDirection,
    hf.markers, hb, hc, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hh, Function.update_of_ne hv]
  · rw [hh, Function.update_self, hf.nextState]
    exact Nat.lt_succ_self _
  · rw [hh, Function.update_self, hf.newState]
  · change range start ⊆ (out.trace.directions s.trace.nextDirection).history ∧ _
    rw [hf.newDirection]
    exact ⟨hs.headPrefix w, hs.headPast w, rfl, rfl, List.length_range'⟩

lemma reply_data {m Q start B : ℕ} {move : ℝ} (s : Round m) (w : Fin m)
    (hs : Data s start B move) (hw : Enabled Q s (.reply w)) :
    Data (advance B move s (.reply w)) start B move := by
  cases hticket : s.pending w with
  | none =>
    have h : (s.pending w).isSome := hw.2
    simp [hticket] at h
  | some t =>
    let out := advance B move s (.reply w)
    let es := localComplete B t
    have ht := hs.ticket w t hticket
    obtain ⟨hv, hf⟩ := finish_private (m + 1) s.trace t.collection t.firstRaw (w.val + 1)
      (s.head w) B move ht
    obtain ⟨hr, hv', hret⟩ := append_legal hs es hv
    have hout : out = { s.append es with
        head := Function.update s.head w s.trace.nextState
        pending := Function.update s.pending w none
        completed := s.completed + 1 } := by simp [out, advance, hticket, es]
    have hf' : FinishData s.trace out.trace t.collection t.firstRaw (w.val + 1) (s.head w) B move := by
      rw [hout]
      exact hf
    have hkeep (v : Fin m) (j : Ticket) (hj : out.pending v = some j) :
        v ≠ w ∧ s.pending v = some j := by
      rw [hout] at hj
      change Function.update s.pending w none v = some j at hj
      by_cases h : v = w
      · subst v
        simp at hj
      · rw [Function.update_of_ne h] at hj
        exact ⟨h, hj⟩
    change Data out start B move
    refine ⟨?_, ?_, ?_, forest_finish w t hs.forest hf' ?_ ?_ ?_, ?_, ?_⟩
    · rw [hout]
      exact hr
    · rw [hout]
      exact hv'
    · rw [hout]
      exact hret
    · rw [hout]
      rfl
    · rw [hout]
    · rw [hout]
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      have hp := hs.ticket v j hj
      have hdiff := hs.distinct v w j t hj hticket hne
      have hhead : out.head v = s.head v := by
        rw [hout]
        change Function.update s.head w s.trace.nextState v = s.head v
        rw [Function.update_of_ne hne]
      rw [hhead]
      refine ⟨?_, ?_, ?_⟩
      · rw [hf'.nextCollection]
        exact hp.collection
      · rw [hf'.oldCollection _ hdiff]
        exact hp.header
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := hp.raw q hq
        rw [hf'.nextRaw, hf'.raw, hf'.retired]
        refine ⟨hqr, ?_, hqc⟩
        intro h
        rcases mem_union.mp h with h | h
        · exact hqf h
        · have he := (ht.raw q (List.mem_toFinset.mp h)).2.2
          exact hdiff (congrArg RawRecord.collection (hqc.symm.trans he))
    · intro v u j j' hv hu hne
      exact hs.distinct v u j j' (hkeep v j hv).2 (hkeep u j' hu).2 hne

lemma run_data {m Q start B : ℕ} {move : ℝ} (s : Round m)
    (events : List (OriginalEvent m)) (hs : Data s start B move)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom Q B move s events) :
    Data (events.foldl (advance B move) s) start B move := by
  induction events generalizing s with
  | nil => exact hs
  | cons e events ih =>
    apply ih _ _ he.2
    cases e with
    | query w => exact query_data s w hs hB hm0 hm1
    | reply w => exact reply_data s w hs he.1

end LongTails.Proofs.BirchCollectionLocalTrace
