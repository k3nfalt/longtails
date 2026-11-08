import LongTails.Proofs.BirchCollectionLocalTrace
import LongTails.Proofs.BirchCollectionPublication

namespace LongTails.Proofs.BirchCollectionLocalPublish

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Proofs.BirchCollectionLocalTrace
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionPrivatePacket
open LongTails.Proofs.BirchCollectionPublication

structure RoundInfo {m : ℕ} (s : Round m) (start B : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  forest : Forest s start B move
  ticket : ∀ w (t : Ticket), s.pending w = some t →
    ∃ source, PrivateTicket s.trace t.collection t.firstRaw (w.val + 1) source B move
  distinct : ∀ w v (t u : Ticket), s.pending w = some t → s.pending v = some u →
    w ≠ v → t.collection ≠ u.collection

lemma round_info {m start B : ℕ} {move : ℝ} {s : Round m} (hs : Data s start B move) :
    RoundInfo s start B move :=
  ⟨hs.represented, hs.legal, hs.retired, hs.forest,
    fun w t hw => ⟨s.head w, hs.ticket w t hw⟩, hs.distinct⟩

lemma append_round_info {m start B : ℕ} {move : ℝ} {s : Round m}
    (hs : RoundInfo s start B move) (events : List Event)
    (he : ValidFrom (m + 1) s.trace events) :
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

def abortOne {m : ℕ} (B : ℕ) (s : Round m) (w : Fin m) : Round m :=
  match s.pending w with
  | none => s
  | some j =>
    { s.append (localAbort B j) with pending := Function.update s.pending w none }

lemma abort_one {m start B : ℕ} {move : ℝ} (s : Round m) (w : Fin m) (hs : RoundInfo s start B move) :
    RoundInfo (abortOne B s w) start B move ∧
      (abortOne B s w).trace.states = s.trace.states ∧
      (abortOne B s w).trace.directions = s.trace.directions ∧
      (abortOne B s w).trace.nextState = s.trace.nextState ∧
      (abortOne B s w).trace.nextDirection = s.trace.nextDirection ∧
      (abortOne B s w).trace.markers = s.trace.markers ∧
      (abortOne B s w).trace.nextRaw = s.trace.nextRaw := by
  cases h : s.pending w with
  | none => simp [abortOne, h, hs]
  | some t =>
    let out := abortOne B s w
    let qs := List.range' t.firstRaw B
    let es := localAbort B t
    let v := (qs.map Event.discard).foldl step s.trace
    have hout : out = { s.append es with pending := Function.update s.pending w none } := by
      simp [out, abortOne, h, es]
    obtain ⟨_, hp⟩ := hs.ticket w t h
    obtain ⟨hv, hdiscard⟩ := discard_data (m + 1) s.trace qs List.nodup_range' (fun q hq =>
      ⟨(hp.raw q hq).1, (hp.raw q hq).2.1⟩)
    change v = _ at hdiscard
    have hcancel : (Event.cancel t.collection).Valid (m + 1) v := by
      rw [hdiscard]
      exact ⟨hp.collection, by rw [hp.header]⟩
    have he : ValidFrom (m + 1) s.trace es :=
      (valid_append _ _ (qs.map Event.discard) [.cancel t.collection]).2 ⟨hv, hcancel, trivial⟩
    have htrace : out.trace = {s.trace with
        retired := s.trace.retired ∪ qs.toFinset
        collections := Function.update s.trace.collections t.collection
          {s.trace.collections t.collection with closed := true} } := by
      rw [hout]
      change es.foldl step s.trace = _
      simp only [es, localAbort, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change step v (.cancel t.collection) = _
      rw [hdiscard]
      rfl
    have hsc : out.trace.nextState = s.trace.nextState := by rw [htrace]
    have hdc : out.trace.nextDirection = s.trace.nextDirection := by rw [htrace]
    have hstates : out.trace.states = s.trace.states := by rw [htrace]
    have hdirs : out.trace.directions = s.trace.directions := by rw [htrace]
    have hmarkers : out.trace.markers = s.trace.markers := by rw [htrace]
    have hraw : out.trace.nextRaw = s.trace.nextRaw := by rw [htrace]
    have hkeep (u : Fin m) (j : Ticket) (hj : out.pending u = some j) :
        u ≠ w ∧ s.pending u = some j := by
      rw [hout] at hj
      change Function.update s.pending w none u = some j at hj
      by_cases heq : u = w
      · subst u
        simp at hj
      · rw [Function.update_of_ne heq] at hj
        exact ⟨heq, hj⟩
    obtain ⟨hr, hl, hret⟩ := append_round_info hs es he
    change RoundInfo out start B move ∧ _
    refine ⟨⟨?_, ?_, ?_, forest_same hs.forest ?_ ?_ ?_ hdc hsc hstates hdirs hmarkers, ?_, ?_⟩,
      hstates, hdirs, hsc, hdc, hmarkers, hraw⟩
    · rw [hout]
      exact hr
    · rw [hout]
      exact hl
    · rw [hout]
      exact hret
    · rw [hout]
      rfl
    · rw [hout]
      rfl
    · rw [hout]
      rfl
    · intro u j hj
      obtain ⟨hne, hj⟩ := hkeep u j hj
      obtain ⟨source, hu⟩ := hs.ticket u j hj
      have hd := hs.distinct u w j t hj h hne
      rw [htrace]
      refine ⟨source, hu.collection, ?_, ?_⟩
      · change Function.update s.trace.collections t.collection _ j.collection = _
        rw [Function.update_of_ne hd]
        exact hu.header
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := hu.raw q hq
        refine ⟨hqr, ?_, hqc⟩
        intro hmem
        rcases mem_union.mp hmem with hmem | hmem
        · exact hqf hmem
        · have hother := (hp.raw q (List.mem_toFinset.mp hmem)).2.2
          exact hd (congrArg RawRecord.collection (hqc.symm.trans hother))
    · intro u v j j' hj hj' hne
      exact hs.distinct u v j j' (hkeep u j hj).2 (hkeep v j' hj').2 hne

structure AbortEffect (s t : TraceState) : Prop where
  states : t.states = s.states
  directions : t.directions = s.directions
  stateCount : t.nextState = s.nextState
  directionCount : t.nextDirection = s.nextDirection
  markers : t.markers = s.markers
  raw : t.nextRaw = s.nextRaw

lemma abort_fold {m start B : ℕ} {move : ℝ} (s : Round m) (ws : List (Fin m))
    (hs : RoundInfo s start B move) :
    let out := ws.foldl (abortOne B) s
    RoundInfo out start B move ∧ AbortEffect s.trace out.trace := by
  induction ws generalizing s with
  | nil => exact ⟨hs, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | cons w ws ih =>
    obtain ⟨ht, hst, hdir, hsc, hdc, hm, hraw⟩ := abort_one s w hs
    obtain ⟨hu, h⟩ := ih (abortOne B s w) ht
    exact ⟨hu, ⟨h.states.trans hst, h.directions.trans hdir, h.stateCount.trans hsc,
      h.directionCount.trans hdc, h.markers.trans hm, h.raw.trans hraw⟩⟩

lemma abort_pending {m start B : ℕ} {move : ℝ} (s : Round m) (hs : RoundInfo s start B move) :
    RoundInfo (abortPending B s) start B move ∧ AbortEffect s.trace (abortPending B s).trace :=
  abort_fold s (List.finRange m) hs

structure JoinInvariant {m : ℕ} (s : Round m) (t : Round m × ℕ) (seen : Finset (Fin m))
    (start : ℕ) : Prop where
  represented : run t.1.events = t.1.trace
  legal : ValidFrom (m + 1) {} t.1.events
  retired : RetiredPast t.1.trace
  extension : Extends s.trace t.1.trace
  directions : t.1.trace.directions = s.trace.directions
  directionCount : t.1.trace.nextDirection = s.trace.nextDirection
  markers : t.1.trace.markers = s.trace.markers
  raw : t.1.trace.nextRaw = s.trace.nextRaw
  head : t.2 < t.1.trace.nextState
  history : ∀ q, q ∈ (t.1.trace.states t.2).history ↔
    q ∈ range start ∨ ∃ w ∈ seen, q ∈ (s.trace.states (s.head w)).history

def joinOne {m : ℕ} (s : Round m) (t : Round m × ℕ) (w : Fin m) : Round m × ℕ :=
  (t.1.append [.merge 0 t.2 (s.head w) s.base], t.1.trace.nextState)

lemma join_one {m start B : ℕ} {move : ℝ} (s : Round m) (t : Round m × ℕ)
    (seen : Finset (Fin m)) (w : Fin m) (hs : Forest s start B move)
    (ht : JoinInvariant s t seen start) (hw : w ∉ seen) :
    JoinInvariant s (joinOne s t w) (insert w seen) start := by
  let e := Event.merge 0 t.2 (s.head w) s.base
  let out := joinOne s t w
  have hright : s.head w < t.1.trace.nextState := (hs.head w).trans_le ht.extension.stateCount
  have hbase : s.base < t.1.trace.nextState := hs.base.trans_le ht.extension.stateCount
  have hrightData : t.1.trace.states (s.head w) = s.trace.states (s.head w) :=
    ht.extension.oldState _ (hs.head w)
  have hbaseData : t.1.trace.states s.base = s.trace.states s.base :=
    ht.extension.oldState _ hs.base
  have he : e.Valid (m + 1) t.1.trace := by
    refine ⟨Nat.zero_lt_succ _, ht.head, hright, hbase, ?_⟩
    rw [hbaseData, hrightData, hs.baseHistory]
    ext q
    rw [mem_inter, ht.history q]
    constructor
    · intro hq
      exact ⟨Or.inl hq, hs.headPrefix w hq⟩
    · rintro ⟨hq | ⟨v, hv, hqv⟩, hqw⟩
      · exact hq
      · have hne : v ≠ w := fun h => hw (h ▸ hv)
        rw [← hs.disjoint v w hne]
        exact mem_inter.mpr ⟨hqv, hqw⟩
  have hv : ValidFrom (m + 1) {} out.1.events := by
    apply (valid_append _ _ t.1.events [e]).2
    refine ⟨ht.legal, ?_⟩
    change ValidFrom (m + 1) (run t.1.events) [e]
    rw [ht.represented]
    exact ⟨he, trivial⟩
  have hr : run out.1.events = out.1.trace := by
    change run (t.1.events ++ [e]) = step t.1.trace e
    rw [show run (t.1.events ++ [e]) = step (run t.1.events) e from List.foldl_append, ht.represented]
  change JoinInvariant s out (insert w seen) start
  refine ⟨hr, hv, retired_past_step _ _ _ ht.retired he,
    ht.extension.trans (extends_step _ e), ht.directions, ht.directionCount, ht.markers,
    ht.raw, Nat.lt_succ_self _, ?_⟩
  intro q
  change q ∈ ((step t.1.trace e).states t.1.trace.nextState).history ↔ _
  rw [(merge_data t.1.trace 0 t.2 (s.head w) s.base).newState]
  simp only [mem_union, ht.history, hrightData, mem_insert]
  constructor
  · rintro ((hq | ⟨v, hv, hqv⟩) | hqw)
    · exact Or.inl hq
    · exact Or.inr ⟨v, Or.inr hv, hqv⟩
    · exact Or.inr ⟨w, Or.inl rfl, hqw⟩
  · rintro (hq | ⟨v, rfl | hv, hqv⟩)
    · exact Or.inl (Or.inl hq)
    · exact Or.inr hqv
    · exact Or.inl (Or.inr ⟨v, hv, hqv⟩)

lemma join_fold {m start B : ℕ} {move : ℝ} (s : Round m) (t : Round m × ℕ)
    (seen : Finset (Fin m)) (ws : List (Fin m)) (hs : Forest s start B move)
    (ht : JoinInvariant s t seen start) (hn : ws.Nodup) (hw : ∀ w ∈ ws, w ∉ seen) :
    JoinInvariant s (ws.foldl (joinOne s) t) (seen ∪ ws.toFinset) start := by
  induction ws generalizing t seen with
  | nil => simpa using ht
  | cons w ws ih =>
    have htw := join_one s t seen w hs ht (hw w (by simp))
    have hv (v : Fin m) (hv : v ∈ ws) : v ∉ insert w seen := by
      intro h
      rcases mem_insert.mp h with rfl | h
      · exact (List.nodup_cons.mp hn).1 hv
      · exact hw v (List.mem_cons_of_mem _ hv) h
    have h := ih (joinOne s t w) (insert w seen) htw (List.nodup_cons.mp hn).2 hv
    have heq : insert w seen ∪ ws.toFinset = seen ∪ (w :: ws).toFinset := by
      ext v
      simp only [mem_union, mem_insert, List.toFinset_cons]
      tauto
    rw [heq] at h
    exact h

structure Published (s t : TraceState) : Prop where
  extension : Extends s t
  directions : t.directions = s.directions
  directionCount : t.nextDirection = s.nextDirection
  raw : t.nextRaw = s.nextRaw
  mark : ∃ head, head < t.nextState ∧ t.markers = s.markers ++ [head] ∧
    (t.states head).history = range t.nextDirection

lemma join_heads {m start B : ℕ} {move : ℝ} (s : Round m) (hs : RoundInfo s start B move) :
    let out := joinHeads s
    run out.events = out.trace ∧ ValidFrom (m + 1) {} out.events ∧ RetiredPast out.trace ∧
      Published s.trace out.trace := by
  let ws := List.finRange m
  let t := ws.foldl (joinOne s) (s, s.base)
  have hstart : JoinInvariant s (s, s.base) ∅ start := by
    refine ⟨hs.represented, hs.legal, hs.retired, extends_refl _, rfl, rfl, rfl, rfl, hs.forest.base, ?_⟩
    intro q
    change q ∈ (s.trace.states s.base).history ↔ _
    rw [hs.forest.baseHistory]
    simp
  have h : JoinInvariant s t (∅ ∪ ws.toFinset) start :=
    join_fold s (s, s.base) ∅ ws hs.forest hstart (List.nodup_finRange m) (by simp)
  have hh : (t.1.trace.states t.2).history = range s.trace.nextDirection := by
    ext q
    rw [h.history q]
    constructor
    · rintro (hq | ⟨w, _, hq⟩)
      · exact range_mono (by rw [hs.forest.count]; omega) hq
      · exact hs.forest.headPast w hq
    · intro hq
      rcases hs.forest.covered q hq with hq | ⟨w, hq⟩
      · exact Or.inl hq
      · exact Or.inr ⟨w, by simp [ws], hq⟩
  let mark := Event.mark t.2
  have hm : mark.Valid (m + 1) t.1.trace := by
    refine ⟨h.head, ?_⟩
    rw [h.markers, hs.forest.marker, h.extension.oldState _ hs.forest.base, hs.forest.baseHistory, hh]
    apply range_mono
    rw [hs.forest.count]
    omega
  change run (t.1.events ++ [mark]) = step t.1.trace mark ∧
    ValidFrom (m + 1) {} (t.1.events ++ [mark]) ∧ RetiredPast (step t.1.trace mark) ∧
    Published s.trace (step t.1.trace mark)
  refine ⟨?_, ?_, retired_past_step _ _ _ h.retired hm, ?_⟩
  · rw [show run (t.1.events ++ [mark]) = step (run t.1.events) mark from List.foldl_append,
      h.represented]
  · apply (valid_append _ _ t.1.events [mark]).2
    refine ⟨h.legal, ?_⟩
    change ValidFrom (m + 1) (run t.1.events) [mark]
    rw [h.represented]
    exact ⟨hm, trivial⟩
  · exact ⟨h.extension.trans (extends_step _ mark), h.directions, h.directionCount, h.raw,
      t.2, h.head, congrArg (· ++ [t.2]) h.markers, hh.trans (congrArg range h.directionCount).symm⟩

lemma publish_round_info {m start B : ℕ} {move : ℝ} (s : Round m) (hs : RoundInfo s start B move) :
    let out := publish B s
    run out.events = out.trace ∧ ValidFrom (m + 1) {} out.events ∧ RetiredPast out.trace ∧
      Published s.trace out.trace := by
  obtain ⟨ha, he⟩ := abort_pending s hs
  obtain ⟨hr, hv, hret, hp⟩ := join_heads (abortPending B s) ha
  refine ⟨hr, hv, hret, ?_⟩
  have habort : Extends s.trace (abortPending B s).trace :=
    ⟨he.stateCount.ge, he.directionCount.ge, fun i _ => congrFun he.states i,
      fun i _ => congrFun he.directions i, he.raw.ge⟩
  refine ⟨habort.trans hp.extension, hp.directions.trans he.directions,
    hp.directionCount.trans he.directionCount, hp.raw.trans he.raw, ?_⟩
  obtain ⟨head, hhead, hmarks, hh⟩ := hp.mark
  exact ⟨head, hhead, hmarks.trans (congrArg (· ++ [head]) he.markers), hh⟩

lemma publish_data {m start B : ℕ} {move : ℝ} (s : Round m) (hs : Data s start B move) :
    let out := publish B s
    run out.events = out.trace ∧ ValidFrom (m + 1) {} out.events ∧ RetiredPast out.trace ∧
      Published s.trace out.trace :=
  publish_round_info s (round_info hs)

end LongTails.Proofs.BirchCollectionLocalPublish
