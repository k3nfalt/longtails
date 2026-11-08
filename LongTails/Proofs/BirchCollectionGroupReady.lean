import LongTails.Proofs.BirchCollectionLocalAsyncTrace
import LongTails.Proofs.BirchCollectionLocalRounds

namespace LongTails.Proofs.BirchCollectionGroupReady

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round localComplete)
open LongTails.Algorithms.BirchCollectionLocalAsync
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Proofs.BirchCollectionLocalTrace (ForestStep forest_same forest_step)
open LongTails.Proofs.BirchCollectionLocalPublish
open LongTails.Proofs.BirchCollectionLocalRounds (marks fold_marks)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionPrivatePacket
open LongTails.Proofs.BirchCollectionPublication

open LongTails.Proofs.BirchCollectionLocalAsyncTrace (Snapshot)

structure Heads {m : ℕ} (s : Round m) (start : ℕ) : Prop where
  bound : ∀ w, s.head w < s.trace.nextState
  includes : ∀ w, range start ⊆ (s.trace.states (s.head w)).history
  past : ∀ w, (s.trace.states (s.head w)).history ⊆ range s.trace.nextDirection

structure Ready {m : ℕ} (group : Fin m → Fin m) (s : Round m) (start B : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  ticket : ∀ w (t : Ticket), s.pending w = some t →
    ∃ source, PrivateTicket s.trace t.collection t.firstRaw (w.val + 1) source B move
  distinct : ∀ w v (t u : Ticket), s.pending w = some t → s.pending v = some u →
    w ≠ v → t.collection ≠ u.collection
  saved : ∀ w t, s.pending w = some t →
    Snapshot s.trace (s.trace.collections t.collection).source (s.head (group w)) start

structure CaptureFrame {m : ℕ} (s t : Round m) : Prop where
  base : t.base = s.base
  heads : t.head = s.head
  completed : t.completed = s.completed
  stateCount : t.trace.nextState = s.trace.nextState
  states : t.trace.states = s.trace.states
  directionCount : t.trace.nextDirection = s.trace.nextDirection
  directions : t.trace.directions = s.trace.directions
  markers : t.trace.markers = s.trace.markers
  rawCount : s.trace.nextRaw ≤ t.trace.nextRaw

lemma append_ready {m start B : ℕ} {move : ℝ} {group : Fin m → Fin m} {s : Round m}
    (hs : Ready group s start B move) (events : List Event)
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

lemma ready_query {m start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m) (w : Fin m)
    (hs : Ready group s start B move) (hh : Heads s start) (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1) :
    let out := advance group B move s (.query w)
    Ready group out start B move ∧ CaptureFrame s out := by
  let es := capture group B move s w
  let out := advance group B move s (.query w)
  let source := s.head (group w)
  let t := step s.trace (.capture (w.val + 1) source B 1 move)
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hi, hn⟩ := launch_private (m + 1) s.trace (w.val + 1) source B move
    (Nat.succ_lt_succ w.isLt) (hh.bound _) hB hm hm' hs.retired
  change IssueData t out.trace s.trace.nextCollection (w.val + 1) B at hi
  have hfield := hi.fields
  have hc : out.trace.nextCollection = s.trace.nextCollection + 1 :=
    congrArg TraceState.nextCollection hfield
  have hstates : out.trace.states = s.trace.states := by
    simpa only [t, step] using congrArg TraceState.states hfield
  have hsc : out.trace.nextState = s.trace.nextState := by
    simpa only [t, step] using congrArg TraceState.nextState hfield
  have hp (v : Fin m) : out.pending v = Function.update s.pending w (some ticket) v := rfl
  have hold (c : ℕ) (hc : c < s.trace.nextCollection) :
      out.trace.collections c = s.trace.collections c := by
    rw [congrArg TraceState.collections hfield]
    change Function.update s.trace.collections s.trace.nextCollection _ c = _
    rw [Function.update_of_ne (Nat.ne_of_lt hc)]
  obtain ⟨hr, hv', hret⟩ := append_ready hs es hv
  change Ready group out start B move ∧ CaptureFrame s out
  refine ⟨⟨hr, hv', hret, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, hsc, hstates,
    by simpa only [t, step] using congrArg TraceState.nextDirection hfield,
    by simpa only [t, step] using congrArg TraceState.directions hfield,
    by simpa only [t, step] using congrArg TraceState.markers hfield,
    by rw [hi.nextRaw]; exact Nat.le_add_right _ _⟩⟩
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hj
      subst j
      exact ⟨source, hn⟩
    · rw [hp, Function.update_of_ne he] at hj
      obtain ⟨a, ht⟩ := hs.ticket v j hj
      refine ⟨a, ?_, (hold _ ht.collection).trans ht.header, ?_⟩
      · rw [hc]
        exact ht.collection.trans (Nat.lt_succ_self _)
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := ht.raw q hq
        refine ⟨?_, ?_, ?_⟩
        · rw [hi.nextRaw]
          exact hqr.trans_le (Nat.le_add_right _ _)
        · rw [congrArg TraceState.retired hfield]
          exact hqf
        · rw [hi.oldRaw q hqr]
          exact hqc
  · intro v u j j' hv hu hne
    by_cases h₁ : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hv
      rw [hp, Function.update_of_ne (Ne.symm hne)] at hu
      subst j
      obtain ⟨_, ht⟩ := hs.ticket u j' hu
      exact Nat.ne_of_gt ht.collection
    · rw [hp, Function.update_of_ne h₁] at hv
      by_cases h₂ : u = w
      · subst u
        rw [hp, Function.update_self, Option.some.injEq] at hu
        subst j'
        obtain ⟨_, ht⟩ := hs.ticket v j hv
        exact Nat.ne_of_lt ht.collection
      · rw [hp, Function.update_of_ne h₂] at hu
        exact hs.distinct v u j j' hv hu hne
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hj
      subst j
      have hc' : out.trace.collections ticket.collection =
          { owner := w.val + 1, source, size := B, refresh := 1, movement := move } := hn.header
      have hheadEq : out.head (group w) = source := rfl
      rw [hc', hheadEq]
      exact ⟨hsc.symm ▸ hh.bound _, by rw [hstates]; exact hh.includes _, le_rfl⟩
    · rw [hp, Function.update_of_ne he] at hj
      obtain ⟨_, ht⟩ := hs.ticket v j hj
      have h := hs.saved v j hj
      rw [hold _ ht.collection, show out.head = s.head from rfl]
      exact ⟨hsc.symm ▸ h.bound, by rw [hstates]; exact h.basePrefix, by rw [hstates]; exact h.past⟩

lemma ready_reply {m Q start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m) (w : Fin m)
    (hs : Ready group s start B move) (hh : Heads s start)
    (hw : LongTails.Algorithms.BirchCollectionLocal.Enabled Q s (.reply w)) :
    let out := advance group B move s (.reply w)
    Ready group out start B move ∧ ForestStep s out (group w) start B move := by
  cases hticket : s.pending w with
  | none =>
    have h : (s.pending w).isSome := hw.2
    simp [hticket] at h
  | some ticket =>
    let out := advance group B move s (.reply w)
    let g := group w
    let a := (s.trace.collections ticket.collection).source
    let f := localComplete B ticket
    let t := f.foldl step s.trace
    let merge := Event.merge (g.val + 1) (s.head g) s.trace.nextState a
    let es := f ++ [merge]
    let H := (s.trace.states (s.head g)).history
    let A := (s.trace.states a).history
    let n := s.trace.nextDirection
    have hA : Snapshot s.trace a (s.head g) start := hs.saved w ticket hticket
    obtain ⟨source, ht⟩ := hs.ticket w ticket hticket
    have ha : a = source := congrArg Collection.source ht.header
    have hticketData : PrivateTicket s.trace ticket.collection ticket.firstRaw (w.val + 1) a B move :=
      ha.symm ▸ ht
    obtain ⟨hv, hf⟩ := finish_private (m + 1) s.trace ticket.collection ticket.firstRaw (w.val + 1)
      a B move hticketData
    change FinishData s.trace t ticket.collection ticket.firstRaw (w.val + 1) a B move at hf
    have hA' : (t.states a).history = A := congrArg StateRecord.history (hf.oldState _ hA.bound)
    have hH : (t.states (s.head g)).history = H :=
      congrArg StateRecord.history (hf.oldState _ (hh.bound g))
    have hnew : (t.states s.trace.nextState).history = insert n A :=
      congrArg StateRecord.history hf.newState
    have hnot : n ∉ H := fun hn => Nat.lt_irrefl n (mem_range.mp (hh.past g hn))
    have hsub : A ⊆ H := hA.past
    have hIntersection : A = H ∩ insert n A := by
      ext q
      simp only [mem_inter, mem_insert]
      constructor
      · intro h
        exact ⟨hsub h, Or.inr h⟩
      · rintro ⟨hH, rfl | hA⟩
        · exact (hnot hH).elim
        · exact hA
    have hUnion : H ∪ insert n A = insert n H := by
      ext q
      simp only [mem_union, mem_insert]
      constructor
      · rintro (hq | hq | hq)
        · exact Or.inr hq
        · exact Or.inl hq
        · exact Or.inr (hsub hq)
      · rintro (hq | hq)
        · exact Or.inr (Or.inl hq)
        · exact Or.inl hq
    have hmerge : merge.Valid (m + 1) t := by
      refine ⟨Nat.succ_lt_succ g.isLt, ?_, ?_, ?_, ?_⟩
      · rw [hf.nextState]
        exact (hh.bound g).trans (Nat.lt_succ_self _)
      · rw [hf.nextState]
        exact Nat.lt_succ_self _
      · rw [hf.nextState]
        exact hA.bound.trans (Nat.lt_succ_self _)
      · rw [hA', hH, hnew]
        exact hIntersection
    have he : ValidFrom (m + 1) s.trace es := (valid_append _ _ f [merge]).2 ⟨hv, hmerge, trivial⟩
    have hout : out = {s.append es with
        head := Function.update s.head g (s.trace.nextState + 1)
        pending := Function.update s.pending w none
        completed := s.completed + 1 } := by simp [out, advance, hticket, complete, es, f, merge, a, g]
    have htrace : out.trace = step t merge := by
      rw [hout]
      change (f ++ [merge]).foldl step s.trace = _
      rw [List.foldl_append]
      rfl
    have htData : MergeData t out.trace (g.val + 1) (s.head g) s.trace.nextState := by
      rw [htrace]
      exact merge_data _ _ _ _ _
    have hhead : out.head g = t.nextState := by
      rw [hout, hf.nextState]
      change Function.update s.head g (s.trace.nextState + 1) g = _
      rw [Function.update_self]
    have hstep : ForestStep s out g start B move := by
      refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hout]; rfl, by rw [hout], ?_, ?_, ?_, ?_⟩
      · rw [htrace]
        exact hf.nextDirection
      · rw [htData.stateCount, hf.nextState]
        omega
      · intro i hi
        exact (htData.oldState _ (hi.trans_le (hf.nextState.symm ▸ Nat.le_succ _))).trans (hf.oldState i hi)
      · intro i hi
        rw [htrace]
        exact hf.oldDirection i hi
      · rw [htrace]
        exact hf.markers
      · intro v hne
        rw [hout]
        change Function.update s.head g (s.trace.nextState + 1) v = _
        rw [Function.update_of_ne hne]
      · rw [hhead, htData.stateCount]
        exact Nat.lt_succ_self _
      · rw [hhead, htData.newState]
        change (t.states (s.head g)).history ∪ (t.states s.trace.nextState).history = _
        rw [hH, hnew]
        exact hUnion
      · change range start ⊆ (out.trace.directions n).history ∧ _
        rw [htrace]
        change range start ⊆ (t.directions n).history ∧
          (t.directions n).history ⊆ range n ∧ (t.directions n).refresh = 1 ∧
          (t.directions n).movement = move ∧ (t.directions n).raw.length = B
        rw [hf.newDirection]
        exact ⟨hA.basePrefix, hsub.trans (hh.past g), rfl, rfl, List.length_range'⟩
    have hkeep (v : Fin m) (j : Ticket) (hj : out.pending v = some j) :
        v ≠ w ∧ s.pending v = some j := by
      rw [hout] at hj
      change Function.update s.pending w none v = some j at hj
      by_cases hv : v = w
      · subst v
        simp at hj
      · rw [Function.update_of_ne hv] at hj
        exact ⟨hv, hj⟩
    have hcollection (j : Ticket) (h : j.collection ≠ ticket.collection) :
        out.trace.collections j.collection = s.trace.collections j.collection := by
      rw [htrace]
      exact hf.oldCollection _ h
    have hcount : out.trace.nextCollection = s.trace.nextCollection := by rw [htrace]; exact hf.nextCollection
    have hraw : out.trace.nextRaw = s.trace.nextRaw := by rw [htrace]; exact hf.nextRaw
    have hraws : out.trace.raws = s.trace.raws := by rw [htrace]; exact hf.raw
    have hretired : out.trace.retired = s.trace.retired ∪ (List.range' ticket.firstRaw B).toFinset := by
      rw [htrace]
      exact hf.retired
    obtain ⟨hr, hl, hret⟩ := append_ready hs es he
    change Ready group out start B move ∧ ForestStep s out g start B move
    refine ⟨⟨by rw [hout]; exact hr, by rw [hout]; exact hl, by rw [hout]; exact hret, ?_, ?_, ?_⟩, hstep⟩
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      obtain ⟨b, h⟩ := hs.ticket v j hj
      have hd := hs.distinct v w j ticket hj hticket hne
      refine ⟨b, hcount.symm ▸ h.collection, (hcollection j hd).trans h.header, ?_⟩
      intro q hq
      obtain ⟨hqr, hqf, hqc⟩ := h.raw q hq
      rw [hraw, hraws, hretired]
      refine ⟨hqr, ?_, hqc⟩
      intro hmem
      rcases mem_union.mp hmem with hmem | hmem
      · exact hqf hmem
      · have heq := (ht.raw q (List.mem_toFinset.mp hmem)).2.2
        exact hd (congrArg RawRecord.collection (hqc.symm.trans heq))
    · intro v u j j' hv hu hne
      exact hs.distinct v u j j' (hkeep v j hv).2 (hkeep u j' hu).2 hne
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      have hd := hs.distinct v w j ticket hj hticket hne
      have hsnap := hs.saved v j hj
      rw [hcollection j hd]
      refine ⟨hsnap.bound.trans_le hstep.stateCount, ?_, ?_⟩
      · rw [hstep.oldState _ hsnap.bound]
        exact hsnap.basePrefix
      · rw [hstep.oldState _ hsnap.bound]
        by_cases heq : group v = g
        · rw [heq, hstep.newHistory]
          exact (heq ▸ hsnap.past).trans (subset_insert _ _)
        · rw [hstep.otherHead _ heq, hstep.oldState _ (hh.bound _)]
          exact hsnap.past

lemma ready_abort {m start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m) (w : Fin m)
    (hs : Ready group s start B move) :
    let out := abortOne B s w
    Ready group out start B move ∧ CaptureFrame s out ∧
      out.pending = Function.update s.pending w none := by
  cases h : s.pending w with
  | none =>
    have hu : Function.update s.pending w none = s.pending := by
      funext v
      by_cases hv : v = w
      · subst v
        simp [h]
      · simp [Function.update_of_ne hv]
    simpa only [abortOne, h, hu] using
      (show Ready group s start B move ∧ CaptureFrame s s ∧ s.pending = s.pending from
        ⟨hs, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩, rfl⟩)
  | some j =>
    let qs := List.range' j.firstRaw B
    let es := LongTails.Algorithms.BirchCollectionLocal.localAbort B j
    let mid := (qs.map Event.discard).foldl step s.trace
    let out := { s.append es with pending := Function.update s.pending w none }
    obtain ⟨a, ht⟩ := hs.ticket w j h
    obtain ⟨hv, hd⟩ := discard_data (m + 1) s.trace qs List.nodup_range' (fun q hq =>
      ⟨(ht.raw q hq).1, (ht.raw q hq).2.1⟩)
    change mid = _ at hd
    have hcancel : (Event.cancel j.collection).Valid (m + 1) mid := by
      rw [hd]
      exact ⟨ht.collection, by rw [ht.header]⟩
    have he : ValidFrom (m + 1) s.trace es :=
      (valid_append _ _ (qs.map Event.discard) [.cancel j.collection]).2 ⟨hv, hcancel, trivial⟩
    obtain ⟨hr, hl, hret⟩ := append_ready hs es he
    have htrace : out.trace = {s.trace with
        retired := s.trace.retired ∪ qs.toFinset
        collections := Function.update s.trace.collections j.collection
          {s.trace.collections j.collection with closed := true} } := by
      change es.foldl step s.trace = _
      simp only [es, LongTails.Algorithms.BirchCollectionLocal.localAbort,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      change step mid (.cancel j.collection) = _
      rw [hd]
      rfl
    have hkeep (v : Fin m) (t : Ticket) (ht : out.pending v = some t) :
        v ≠ w ∧ s.pending v = some t := by
      change Function.update s.pending w none v = some t at ht
      by_cases hv : v = w
      · subst v
        simp at ht
      · rw [Function.update_of_ne hv] at ht
        exact ⟨hv, ht⟩
    have hcollect (t : Ticket) (h : t.collection ≠ j.collection) :
        out.trace.collections t.collection = s.trace.collections t.collection := by
      rw [htrace]
      exact Function.update_of_ne h _ _
    have hready : Ready group out start B move := by
      refine ⟨hr, hl, hret, ?_, ?_, ?_⟩
      · intro v t hp
        obtain ⟨hv, hp⟩ := hkeep v t hp
        obtain ⟨b, hp⟩ := hs.ticket v t hp
        have hne := hs.distinct v w t j (hkeep v t ‹out.pending v = some t›).2 h hv
        refine ⟨b, ?_, (hcollect t hne).trans hp.header, ?_⟩
        · rw [htrace]
          exact hp.collection
        · intro q hq
          obtain ⟨hqr, hqf, hqc⟩ := hp.raw q hq
          rw [htrace]
          refine ⟨hqr, ?_, hqc⟩
          intro hret
          rcases mem_union.mp hret with hret | hret
          · exact hqf hret
          · have hsame := (ht.raw q (List.mem_toFinset.mp hret)).2.2
            exact hne (congrArg RawRecord.collection (hqc.symm.trans hsame))
      · intro v u t k hv hu hne
        exact hs.distinct v u t k (hkeep v t hv).2 (hkeep u k hu).2 hne
      · intro v t hp
        obtain ⟨hv, hp⟩ := hkeep v t hp
        have hne := hs.distinct v w t j hp h hv
        have hsnap := hs.saved v t hp
        rw [hcollect t hne]
        have hhead : out.head = s.head := rfl
        rw [hhead]
        have hstates : out.trace.states = s.trace.states := by rw [htrace]
        have hsc : out.trace.nextState = s.trace.nextState := by rw [htrace]
        exact ⟨hsc.symm ▸ hsnap.bound, by rw [hstates]; exact hsnap.basePrefix,
          by rw [hstates]; exact hsnap.past⟩
    have hf : CaptureFrame s out := ⟨rfl, rfl, rfl, by rw [htrace], by rw [htrace],
      by rw [htrace], by rw [htrace], by rw [htrace], by rw [htrace]⟩
    simpa only [abortOne, h, out, es] using
      (show Ready group out start B move ∧ CaptureFrame s out ∧ out.pending = _ from ⟨hready, hf, rfl⟩)

lemma CaptureFrame.trans {m : ℕ} {s t u : Round m} (h₁ : CaptureFrame s t)
    (h₂ : CaptureFrame t u) : CaptureFrame s u :=
  ⟨h₂.base.trans h₁.base, h₂.heads.trans h₁.heads, h₂.completed.trans h₁.completed,
    h₂.stateCount.trans h₁.stateCount, h₂.states.trans h₁.states,
    h₂.directionCount.trans h₁.directionCount, h₂.directions.trans h₁.directions,
    h₂.markers.trans h₁.markers, h₁.rawCount.trans h₂.rawCount⟩

lemma abort_fold_ready {m start B : ℕ} {move : ℝ} (group : Fin m → Fin m)
    (s : Round m) (ws : List (Fin m)) (hs : Ready group s start B move) :
    let out := ws.foldl (abortOne B) s
    Ready group out start B move ∧ CaptureFrame s out ∧
      ∀ w, out.pending w = if w ∈ ws then none else s.pending w := by
  induction ws generalizing s with
  | nil => exact ⟨hs, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩, by simp⟩
  | cons w ws ih =>
    obtain ⟨ht, hf, hp⟩ := ready_abort group s w hs
    obtain ⟨hu, huf, hup⟩ := ih (abortOne B s w) ht
    refine ⟨hu, hf.trans huf, ?_⟩
    intro v
    change ((ws.foldl (abortOne B) (abortOne B s w)).pending v) = _
    rw [hup v, hp]
    by_cases hv : v = w
    · subst v
      by_cases hm : w ∈ ws <;> simp [hm]
    · by_cases hm : v ∈ ws <;> simp [hv, hm]

lemma ready_merge {m start B : ℕ} {move : ℝ} {group : Fin m → Fin m} (s : Round m)
    (owner left right common : ℕ) (hs : Ready group s start B move) (hh : Heads s start)
    (he : (Event.merge owner left right common).Valid (m + 1) s.trace) :
    Ready group (s.append [.merge owner left right common]) start B move := by
  let e := Event.merge owner left right common
  let t := s.append [e]
  obtain ⟨hr, hl, hret⟩ := append_ready hs [e] ⟨he, trivial⟩
  have hx := LongTails.Proofs.BirchCollectionPublication.extends_step s.trace e
  change Ready group t start B move
  refine ⟨hr, hl, hret, ?_, hs.distinct, ?_⟩
  · intro w j hj
    obtain ⟨source, h⟩ := hs.ticket w j hj
    exact ⟨source, h.collection, h.header, h.raw⟩
  · intro w j hj
    have h := hs.saved w j hj
    refine ⟨h.bound.trans_le hx.stateCount, ?_, ?_⟩
    · change range start ⊆ ((step s.trace e).states (s.trace.collections j.collection).source).history
      rw [hx.oldState _ h.bound]
      exact h.basePrefix
    · change ((step s.trace e).states (s.trace.collections j.collection).source).history ⊆
        ((step s.trace e).states (s.head (group w))).history
      rw [hx.oldState _ h.bound, hx.oldState _ (hh.bound (group w))]
      exact h.past

lemma ready_change_heads {m start B : ℕ} {move : ℝ} {group : Fin m → Fin m} (s : Round m)
    (heads : Fin m → ℕ) (hs : Ready group s start B move)
    (h : ∀ w j, s.pending w = some j → heads (group w) = s.head (group w)) :
    Ready group {s with head := heads} start B move := by
  refine ⟨hs.represented, hs.legal, hs.retired, hs.ticket, hs.distinct, ?_⟩
  intro w j hj
  change Snapshot s.trace (s.trace.collections j.collection).source (heads (group w)) start
  rw [h w j hj]
  exact hs.saved w j hj

end LongTails.Proofs.BirchCollectionGroupReady
