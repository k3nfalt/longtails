import LongTails.Algorithms.BirchCollectionLocalAsync
import LongTails.Proofs.BirchCollectionLocalRounds

namespace LongTails.Proofs.BirchCollectionLocalAsyncTrace

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

structure Snapshot (s : TraceState) (source head start : ℕ) : Prop where
  bound : source < s.nextState
  basePrefix : range start ⊆ (s.states source).history
  past : (s.states source).history ⊆ (s.states head).history

structure Data {m : ℕ} (group : Fin m → Fin m) (s : Round m) (start B : ℕ) (move : ℝ) : Prop where
  info : RoundInfo s start B move
  saved : ∀ w t, s.pending w = some t →
    Snapshot s.trace (s.trace.collections t.collection).source (s.head (group w)) start

lemma initial_data {m start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (trace : TraceState)
    (events : List Event) (h : RoundInfo (Round.initial m trace events) start B move) :
    Data group (Round.initial m trace events) start B move := by
  refine ⟨h, ?_⟩
  simp [Round.initial]

lemma data_query {m start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m) (w : Fin m)
    (hs : Data group s start B move) (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1) :
    Data group (advance group B move s (.query w)) start B move := by
  let es := capture group B move s w
  let out := advance group B move s (.query w)
  let source := s.head (group w)
  let t := step s.trace (.capture (w.val + 1) source B 1 move)
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hi, hn⟩ := launch_private (m + 1) s.trace (w.val + 1) source B move
    (Nat.succ_lt_succ w.isLt) (hs.info.forest.head _) hB hm hm' hs.info.retired
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
  obtain ⟨hr, hv', hret⟩ := append_round_info hs.info es hv
  change Data group out start B move
  refine ⟨⟨hr, hv', hret, forest_same hs.info.forest rfl rfl rfl
    (by simpa only [t, step] using congrArg TraceState.nextDirection hfield) hsc hstates
    (by simpa only [t, step] using congrArg TraceState.directions hfield)
    (by simpa only [t, step] using congrArg TraceState.markers hfield), ?_, ?_⟩, ?_⟩
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hj
      subst j
      exact ⟨source, hn⟩
    · rw [hp, Function.update_of_ne he] at hj
      obtain ⟨a, ht⟩ := hs.info.ticket v j hj
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
      obtain ⟨_, ht⟩ := hs.info.ticket u j' hu
      exact Nat.ne_of_gt ht.collection
    · rw [hp, Function.update_of_ne h₁] at hv
      by_cases h₂ : u = w
      · subst u
        rw [hp, Function.update_self, Option.some.injEq] at hu
        subst j'
        obtain ⟨_, ht⟩ := hs.info.ticket v j hv
        exact Nat.ne_of_lt ht.collection
      · rw [hp, Function.update_of_ne h₂] at hu
        exact hs.info.distinct v u j j' hv hu hne
  · intro v j hj
    by_cases he : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hj
      subst j
      have hc' : out.trace.collections ticket.collection =
          { owner := w.val + 1, source, size := B, refresh := 1, movement := move } := hn.header
      have hh : out.head (group w) = source := rfl
      rw [hc', hh]
      exact ⟨hsc.symm ▸ hs.info.forest.head _, by rw [hstates]; exact hs.info.forest.headPrefix _, le_rfl⟩
    · rw [hp, Function.update_of_ne he] at hj
      obtain ⟨_, ht⟩ := hs.info.ticket v j hj
      have h := hs.saved v j hj
      rw [hold _ ht.collection, show out.head = s.head from rfl]
      exact ⟨hsc.symm ▸ h.bound, by rw [hstates]; exact h.basePrefix, by rw [hstates]; exact h.past⟩

lemma data_reply {m Q start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m) (w : Fin m)
    (hs : Data group s start B move)
    (hw : LongTails.Algorithms.BirchCollectionLocal.Enabled Q s (.reply w)) :
    Data group (advance group B move s (.reply w)) start B move := by
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
    obtain ⟨source, ht⟩ := hs.info.ticket w ticket hticket
    have ha : a = source := congrArg Collection.source ht.header
    have hticketData : PrivateTicket s.trace ticket.collection ticket.firstRaw (w.val + 1) a B move :=
      ha.symm ▸ ht
    obtain ⟨hv, hf⟩ := finish_private (m + 1) s.trace ticket.collection ticket.firstRaw (w.val + 1)
      a B move hticketData
    change FinishData s.trace t ticket.collection ticket.firstRaw (w.val + 1) a B move at hf
    have hA' : (t.states a).history = A := congrArg StateRecord.history (hf.oldState _ hA.bound)
    have hH : (t.states (s.head g)).history = H :=
      congrArg StateRecord.history (hf.oldState _ (hs.info.forest.head g))
    have hnew : (t.states s.trace.nextState).history = insert n A :=
      congrArg StateRecord.history hf.newState
    have hnot : n ∉ H := fun hn => Nat.lt_irrefl n (mem_range.mp (hs.info.forest.headPast g hn))
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
        exact (hs.info.forest.head g).trans (Nat.lt_succ_self _)
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
        exact ⟨hA.basePrefix, hsub.trans (hs.info.forest.headPast g), rfl, rfl, List.length_range'⟩
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
    obtain ⟨hr, hl, hret⟩ := append_round_info hs.info es he
    change Data group out start B move
    refine ⟨⟨by rw [hout]; exact hr, by rw [hout]; exact hl, by rw [hout]; exact hret,
      forest_step g hs.info.forest hstep, ?_, ?_⟩, ?_⟩
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      obtain ⟨b, h⟩ := hs.info.ticket v j hj
      have hd := hs.info.distinct v w j ticket hj hticket hne
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
      exact hs.info.distinct v u j j' (hkeep v j hv).2 (hkeep u j' hu).2 hne
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      have hd := hs.info.distinct v w j ticket hj hticket hne
      have hsnap := hs.saved v j hj
      rw [hcollection j hd]
      refine ⟨hsnap.bound.trans_le hstep.stateCount, ?_, ?_⟩
      · rw [hstep.oldState _ hsnap.bound]
        exact hsnap.basePrefix
      · rw [hstep.oldState _ hsnap.bound]
        by_cases heq : group v = g
        · rw [heq, hstep.newHistory]
          exact (heq ▸ hsnap.past).trans (subset_insert _ _)
        · rw [hstep.otherHead _ heq, hstep.oldState _ (hs.info.forest.head _)]
          exact hsnap.past

lemma data_fold {m Q start B : ℕ} {move : ℝ} (group : Fin m → Fin m) (s : Round m)
    (events : List (OriginalEvent m)) (hs : Data group s start B move)
    (hB : 0 < B) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (he : LegalFrom group Q B move s events) :
    Data group (events.foldl (advance group B move) s) start B move := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih _ _ he.2
    cases e with
    | query w => exact data_query group s w hs hB hm0 hm1
    | reply w => exact data_reply group s w hs he.1

end LongTails.Proofs.BirchCollectionLocalAsyncTrace
