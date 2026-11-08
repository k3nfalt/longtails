import LongTails.Algorithms.BirchCollectionWorkerPools
import LongTails.Proofs.BirchCollectionAsyncLocalPublish

namespace LongTails.Proofs.BirchCollectionPoolTrace

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionLocal (localComplete)
open LongTails.Proofs.BirchCollectionAsyncLocalTrace (AcceptedDirection prefixSet savedIndex)
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication
open LongTails.Proofs.BirchCollectionPrivatePacket
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionOrdering

def cutIndex (cuts : List ℕ) (n : ℕ) : ℕ := cuts[n]?.getD 0

structure Log (s : TraceState) (main : ℕ) (accepted cuts frontiers : List ℕ)
    (B lower upper window : ℕ) (move : ℝ) : Prop where
  nonempty : 0 < cuts.length
  frontierCount : frontiers.length = accepted.length
  unique : accepted.Nodup
  labels : ∀ d ∈ accepted, d < s.nextDirection
  cutStart : cutIndex cuts 0 = 0
  cutLast : cuts.getLast?.getD 0 = accepted.length
  cutBound : ∀ k < cuts.length, cutIndex cuts k ≤ accepted.length
  positive : ∀ k, k + 1 < cuts.length → cutIndex cuts k < cutIndex cuts (k + 1)
  mass : ∀ k, k + 1 < cuts.length → lower ≤ cutIndex cuts (k + 1) - cutIndex cuts k ∧
    cutIndex cuts (k + 1) - cutIndex cuts k ≤ upper
  markerCount : s.markers.length = cuts.length
  headMarker : s.markers.getLast?.getD 0 = main
  headBound : main < s.nextState
  headHistory : (s.states main).history = accepted.toFinset
  markers : ∀ k < cuts.length, (s.states (s.markers[k]?.getD 0)).history =
    prefixSet accepted (cutIndex cuts k)
  directions : ∀ n (hn : n < accepted.length),
    AcceptedDirection s accepted frontiers B window move n accepted[n]

structure Branch (s : TraceState) (accepted : List ℕ) (B : ℕ)
    (move : ℝ) (worker : Worker) : Prop where
  frontierBound : worker.frontier ≤ accepted.length
  baseHistory : (s.states worker.base).history = prefixSet accepted worker.frontier
  chain : Chain s worker.base worker.head worker.privateLabels B move
  separate : Disjoint worker.privateLabels.toFinset accepted.toFinset

structure Data {m : ℕ} (s : Pool m) (B lower upper window : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  main : Log s.trace s.main s.accepted s.cuts s.frontiers B lower upper window move
  branch : ∀ w, Branch s.trace s.accepted B move (s.worker w)
  disjoint : ∀ w v, w ≠ v →
    Disjoint (s.worker w).privateLabels.toFinset (s.worker v).privateLabels.toFinset
  ticket : ∀ w j, (s.worker w).pending = some j →
    PrivateTicket s.trace j.collection j.firstRaw (w.val + 1) (s.worker w).head B move
  distinct : ∀ w v (j t : Ticket), (s.worker w).pending = some j →
    (s.worker v).pending = some t → w ≠ v → j.collection ≠ t.collection

lemma Log.extend {s t : TraceState} {main B lower upper window : ℕ} {move : ℝ}
    {accepted cuts frontiers : List ℕ}
    (h : Log s main accepted cuts frontiers B lower upper window move)
    (he : Extends s t) (hm : t.markers = s.markers)
    (hbound : ∀ a ∈ s.markers, a < s.nextState) :
    Log t main accepted cuts frontiers B lower upper window move := by
  refine ⟨h.nonempty, h.frontierCount, h.unique, fun d hd => (h.labels d hd).trans_le he.directionCount,
    h.cutStart, h.cutLast, h.cutBound, h.positive, h.mass,
    by rw [hm]; exact h.markerCount, by rw [hm]; exact h.headMarker,
    h.headBound.trans_le he.stateCount, by rw [he.oldState _ h.headBound]; exact h.headHistory, ?_, ?_⟩
  · intro k hk
    have hidx : k < s.markers.length := h.markerCount.symm ▸ hk
    have hmem : s.markers[k]?.getD 0 ∈ s.markers := by simp [hidx]
    rw [hm, he.oldState _ (hbound _ hmem)]
    exact h.markers k hk
  · intro n hn
    have hd := h.directions n hn
    have hlabel : accepted[n] ∈ accepted := List.getElem_mem hn
    have heq := he.oldDirection _ (h.labels _ hlabel)
    refine ⟨hd.frontierBound, hd.delayBound, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [heq]
    · exact hd.includes
    · exact hd.prior
    · exact hd.refresh
    · exact hd.movement
    · exact hd.raw

lemma Branch.extend {s t : TraceState} {B : ℕ} {accepted : List ℕ}
    {worker : Worker} {move : ℝ}
    (h : Branch s accepted B move worker) (he : Extends s t) :
    Branch t accepted B move worker :=
  ⟨h.frontierBound, by rw [he.oldState _ h.chain.baseBound]; exact h.baseHistory,
    h.chain.extend he, h.separate⟩

lemma initial_data (m B lower upper window : ℕ) (move : ℝ) :
    Data (m := m) {} B lower upper window move := by
  refine ⟨rfl, trivial, by simp [RetiredPast], ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Nat.one_pos, rfl, List.nodup_nil, by simp, rfl, rfl, ?_, ?_, ?_, rfl, rfl,
      Nat.one_pos, rfl, ?_, ?_⟩
    · intro k hk
      have hk' : k = 0 := by change k < 1 at hk; omega
      subst k
      exact le_rfl
    · intro k hk
      change k + 1 < 1 at hk
      omega
    · intro k hk
      change k + 1 < 1 at hk
      omega
    · intro k hk
      have hk' : k = 0 := by change k < 1 at hk; omega
      subst k
      simp [prefixSet, cutIndex]
    · simp
  · intro w
    exact ⟨le_rfl, by simp [prefixSet], chain_initial _ 0 B move Nat.one_pos, by simp⟩
  · simp
  · simp
  · simp

lemma append_legal {m B lower upper window : ℕ} {move : ℝ} {s : Pool m}
    (hs : Data s B lower upper window move) (events : List Event)
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

lemma marker_bounds {m B lower upper window : ℕ} {s : Pool m} {move : ℝ}
    (hs : Data s B lower upper window move) : ∀ a ∈ s.trace.markers, a < s.trace.nextState := by
  rw [← hs.represented]
  exact markers_bound_run _ _ hs.legal

lemma data_issue {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (w : Fin m)
    (hs : Data s B lower upper window move) (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1) :
    Data (issue B move s w) B lower upper window move := by
  let owner := w.val + 1
  let source := (s.worker w).head
  let cap := Event.capture owner source B 1 move
  let es := cap :: List.replicate B (Event.issue s.trace.nextCollection owner)
  let t := step s.trace cap
  let out := issue B move s w
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hi, hn⟩ := launch_private (m + 1) s.trace owner source B move
    (Nat.succ_lt_succ w.isLt) (hs.branch w).chain.headBound hB hm hm' hs.retired
  change IssueData t out.trace s.trace.nextCollection owner B at hi
  have hf := hi.fields
  have hc : out.trace.nextCollection = s.trace.nextCollection + 1 := congrArg TraceState.nextCollection hf
  have hp (v : Fin m) : (out.worker v).pending =
      (Function.update s.worker w {s.worker w with pending := some ticket} v).pending := rfl
  have hworkers (v : Fin m) : (out.worker v).base = (s.worker v).base ∧
      (out.worker v).head = (s.worker v).head ∧ (out.worker v).frontier = (s.worker v).frontier ∧
      (out.worker v).privateLabels = (s.worker v).privateLabels := by
    let u := Function.update s.worker w {s.worker w with pending := some ticket} v
    change u.base = _ ∧ u.head = _ ∧ u.frontier = _ ∧ u.privateLabels = _
    by_cases he : v = w
    · subst v
      simp [u]
    · simp [u, Function.update_of_ne he]
  have he : Extends s.trace out.trace := extends_fold _ es
  have hmarks : out.trace.markers = s.trace.markers := by
    simpa only [t, cap, step] using congrArg TraceState.markers hf
  obtain ⟨hr, hl, hret⟩ := append_legal hs es hv
  change Data out B lower upper window move
  refine ⟨hr, hl, hret, hs.main.extend he hmarks (marker_bounds hs), ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨hb, hh, hround, hdir⟩ := hworkers v
    have h := (hs.branch v).extend he
    exact ⟨hround.symm ▸ h.frontierBound, by rw [hb, hround]; exact h.baseHistory,
      by rw [hb, hh, hdir]; exact h.chain, by rw [hdir]; exact h.separate⟩
  · intro v u hne
    rw [(hworkers v).2.2.2, (hworkers u).2.2.2]
    exact hs.disjoint v u hne
  · intro v j hj
    by_cases h : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hj
      subst j
      rw [(hworkers w).2.1]
      exact hn
    · rw [hp, Function.update_of_ne h] at hj
      have h := hs.ticket v j hj
      rw [(hworkers v).2.1]
      refine ⟨?_, ?_, ?_⟩
      · rw [hc]
        exact h.collection.trans (Nat.lt_succ_self _)
      · rw [congrArg TraceState.collections hf]
        change Function.update s.trace.collections s.trace.nextCollection _ j.collection = _
        rw [Function.update_of_ne (Nat.ne_of_lt h.collection)]
        exact h.header
      · intro q hq
        obtain ⟨hqr, hqf, hqc⟩ := h.raw q hq
        refine ⟨?_, ?_, ?_⟩
        · rw [hi.nextRaw]
          exact hqr.trans_le (Nat.le_add_right _ _)
        · rw [congrArg TraceState.retired hf]
          exact hqf
        · rw [hi.oldRaw q hqr]
          exact hqc
  · intro v u j j' hv hu hne
    by_cases h₁ : v = w
    · subst v
      rw [hp, Function.update_self, Option.some.injEq] at hv
      rw [hp, Function.update_of_ne (Ne.symm hne)] at hu
      subst j
      exact Nat.ne_of_gt (hs.ticket u j' hu).collection
    · rw [hp, Function.update_of_ne h₁] at hv
      by_cases h₂ : u = w
      · subst u
        rw [hp, Function.update_self, Option.some.injEq] at hu
        subst j'
        exact Nat.ne_of_lt (hs.ticket v j hv).collection
      · rw [hp, Function.update_of_ne h₂] at hu
        exact hs.distinct v u j j' hv hu hne

lemma data_complete {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (w : Fin m)
    (hs : Data s B lower upper window move) (hw : (s.worker w).pending.isSome) :
    Data (complete B s w) B lower upper window move := by
  cases h : (s.worker w).pending with
  | none =>
    have hw' : ((s.worker w).pending).isSome := hw
    simp [h] at hw'
  | some ticket =>
    let out := complete B s w
    let n := s.trace.nextDirection
    let new : Worker := {s.worker w with
      head := s.trace.nextState
      privateLabels := (s.worker w).privateLabels ++ [n]
      pending := none}
    let es := localComplete B ticket
    let t := es.foldl step s.trace
    have hout : out = {s.append es with worker := Function.update s.worker w new} := by
      simp only [out, complete, h, Pool.put]
      rfl
    have ht := hs.ticket w ticket h
    obtain ⟨hv, hf⟩ := finish_private (m + 1) s.trace ticket.collection ticket.firstRaw (w.val + 1)
      (s.worker w).head B move ht
    change FinishData s.trace t ticket.collection ticket.firstRaw (w.val + 1) (s.worker w).head B move at hf
    have htrace : out.trace = t := by rw [hout]; rfl
    have hsame (v : Fin m) (hne : v ≠ w) : out.worker v = s.worker v := by
      rw [hout]
      change Function.update s.worker w new v = _
      rw [Function.update_of_ne hne]
    have hnew : out.worker w = new := by
      rw [hout]
      change Function.update s.worker w new w = _
      rw [Function.update_self]
    have he : Extends s.trace t := finish_extends hf
    have hfreshA : n ∉ s.accepted.toFinset := fun hn =>
      Nat.lt_irrefl n (hs.main.labels n (List.mem_toFinset.mp hn))
    have hfresh (v : Fin m) : n ∉ (s.worker v).privateLabels.toFinset := fun hn =>
      Nat.lt_irrefl n ((hs.branch v).chain.bounded n (List.mem_toFinset.mp hn))
    obtain ⟨hr, hl, hret⟩ := append_legal hs es hv
    have hkeep (v : Fin m) (j : Ticket) (hj : (out.worker v).pending = some j) :
        v ≠ w ∧ (s.worker v).pending = some j := by
      by_cases hv : v = w
      · subst v
        rw [hnew] at hj
        simp [new] at hj
      · rw [hsame v hv] at hj
        exact ⟨hv, hj⟩
    have hcuts : out.cuts = s.cuts := by rw [hout]; rfl
    have hmain : out.main = s.main := by rw [hout]; rfl
    have haccept : out.accepted = s.accepted := by rw [hout]; rfl
    have hfront : out.frontiers = s.frontiers := by rw [hout]; rfl
    change Data out B lower upper window move
    refine ⟨by rw [hout]; exact hr, by rw [hout]; exact hl, by rw [hout]; exact hret,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [htrace, hmain, hcuts, haccept, hfront]
      exact hs.main.extend he hf.markers (marker_bounds hs)
    · intro v
      rw [htrace, haccept]
      by_cases hv : v = w
      · subst v
        rw [hnew]
        have hb := hs.branch w
        refine ⟨hb.frontierBound, ?_, chain_finish hb.chain hf, ?_⟩
        · change (t.states (s.worker w).base).history = _
          rw [he.oldState _ hb.chain.baseBound]
          exact hb.baseHistory
        · change Disjoint (((s.worker w).privateLabels ++ [n]).toFinset) s.accepted.toFinset
          rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, disjoint_union_left]
          exact ⟨hb.separate, disjoint_singleton_left.mpr hfreshA⟩
      · rw [hsame v hv]
        exact (hs.branch v).extend he
    · intro v u hne
      by_cases hv : v = w
      · subst v
        rw [hnew, hsame u (Ne.symm hne)]
        change Disjoint (((s.worker w).privateLabels ++ [n]).toFinset) (s.worker u).privateLabels.toFinset
        rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, disjoint_union_left]
        exact ⟨hs.disjoint w u hne, disjoint_singleton_left.mpr (hfresh u)⟩
      · rw [hsame v hv]
        by_cases hu : u = w
        · subst u
          rw [hnew]
          change Disjoint (s.worker v).privateLabels.toFinset (((s.worker w).privateLabels ++ [n]).toFinset)
          rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, disjoint_union_right]
          exact ⟨hs.disjoint v w hne, disjoint_singleton_right.mpr (hfresh v)⟩
        · rw [hsame u hu]
          exact hs.disjoint v u hne
    · intro v j hj
      obtain ⟨hne, hj⟩ := hkeep v j hj
      rw [htrace, hsame v hne]
      have hp := hs.ticket v j hj
      have hd := hs.distinct v w j ticket hj h hne
      refine ⟨hf.nextCollection.symm ▸ hp.collection, (hf.oldCollection _ hd).trans hp.header, ?_⟩
      intro q hq
      obtain ⟨hqr, hqf, hqc⟩ := hp.raw q hq
      rw [hf.nextRaw, hf.raw, hf.retired]
      refine ⟨hqr, ?_, hqc⟩
      intro hmem
      rcases mem_union.mp hmem with hmem | hmem
      · exact hqf hmem
      · have heq := (ht.raw q (List.mem_toFinset.mp hmem)).2.2
        exact hd (congrArg RawRecord.collection (hqc.symm.trans heq))
    · intro v u j j' hv hu hne
      exact hs.distinct v u j j' (hkeep v j hv).2 (hkeep u j' hu).2 hne

lemma data_discard {m B lower upper window : ℕ} {move : ℝ} (s : Pool m) (w : Fin m)
    (hs : Data s B lower upper window move) :
    Data (LongTails.Algorithms.BirchCollectionWorkerPools.discard B s w) B lower upper window move := by
  cases h : (s.worker w).pending with
  | none => simpa only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h] using hs
  | some j =>
    let es := LongTails.Algorithms.BirchCollectionLocal.localAbort B j
    let out := (s.append es).put w {s.worker w with pending := none}
    have hp := hs.ticket w j h
    let qs := List.range' j.firstRaw B
    let mid := (qs.map Event.discard).foldl step s.trace
    obtain ⟨hv, hd⟩ := discard_data (m + 1) s.trace qs List.nodup_range' (fun q hq =>
      ⟨(hp.raw q hq).1, (hp.raw q hq).2.1⟩)
    change mid = _ at hd
    have hcancel : (Event.cancel j.collection).Valid (m + 1) mid := by
      rw [hd]
      exact ⟨hp.collection, by rw [hp.header]⟩
    have he : ValidFrom (m + 1) s.trace es :=
      (valid_append _ _ (qs.map Event.discard) [.cancel j.collection]).2 ⟨hv, hcancel, trivial⟩
    obtain ⟨hr, hl, hret⟩ := append_legal hs es he
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
    have hworker (v : Fin m) : out.worker v =
        Function.update s.worker w {s.worker w with pending := none} v := rfl
    have hbase (v : Fin m) : (out.worker v).base = (s.worker v).base ∧
        (out.worker v).head = (s.worker v).head ∧ (out.worker v).frontier = (s.worker v).frontier ∧
        (out.worker v).privateLabels = (s.worker v).privateLabels := by
      rw [hworker]
      by_cases hv : v = w
      · subst v
        simp
      · rw [Function.update_of_ne hv]
        exact ⟨rfl, rfl, rfl, rfl⟩
    have hpending (v : Fin m) (t : Ticket) (ht : (out.worker v).pending = some t) :
        v ≠ w ∧ (s.worker v).pending = some t := by
      rw [hworker] at ht
      by_cases hv : v = w
      · subst v
        simp at ht
      · rw [Function.update_of_ne hv] at ht
        exact ⟨hv, ht⟩
    have hx : Extends s.trace out.trace := extends_fold _ es
    have hmarks : out.trace.markers = s.trace.markers := by rw [htrace]
    have hdOut : Data out B lower upper window move := by
      refine ⟨hr, hl, hret, hs.main.extend hx hmarks (marker_bounds hs), ?_, ?_, ?_, ?_⟩
      · intro v
        have h := (hs.branch v).extend hx
        obtain ⟨hb, hh, hf, hlabels⟩ := hbase v
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hf]
          exact h.frontierBound
        · rw [hb, hf]
          exact h.baseHistory
        · rw [hb, hh, hlabels]
          exact h.chain
        · rw [hlabels]
          exact h.separate
      · intro v u hne
        rw [(hbase v).2.2.2, (hbase u).2.2.2]
        exact hs.disjoint v u hne
      · intro v t ht
        obtain ⟨hne, ht⟩ := hpending v t ht
        have hp' := hs.ticket v t ht
        have hdiff := hs.distinct v w t j ht h hne
        rw [(hbase v).2.1, htrace]
        refine ⟨hp'.collection, ?_, ?_⟩
        · change Function.update s.trace.collections j.collection _ t.collection = _
          rw [Function.update_of_ne hdiff]
          exact hp'.header
        · intro q hq
          obtain ⟨hqr, hqf, hqc⟩ := hp'.raw q hq
          refine ⟨hqr, ?_, hqc⟩
          intro hretired
          rcases mem_union.mp hretired with hretired | hretired
          · exact hqf hretired
          · have heq := (hp.raw q (List.mem_toFinset.mp hretired)).2.2
            exact hdiff (congrArg RawRecord.collection (hqc.symm.trans heq))
      · intro v u t k hv hu hne
        exact hs.distinct v u t k (hpending v t hv).2 (hpending u k hu).2 hne
    simpa only [LongTails.Algorithms.BirchCollectionWorkerPools.discard, h, out, es] using hdOut

lemma data_merge {m B lower upper window : ℕ} {move : ℝ} (s : Pool m)
    (owner left right base : ℕ) (hs : Data s B lower upper window move)
    (he : (Event.merge owner left right base).Valid (m + 1) s.trace) :
    Data (s.append [.merge owner left right base]) B lower upper window move := by
  let e := Event.merge owner left right base
  let t := s.append [e]
  have hx : Extends s.trace t.trace := extends_step _ e
  obtain ⟨hr, hl, hret⟩ := append_legal hs [e] ⟨he, trivial⟩
  refine ⟨hr, hl, hret, hs.main.extend hx rfl (marker_bounds hs),
    fun w => (hs.branch w).extend hx, hs.disjoint, ?_, hs.distinct⟩
  intro w j hj
  have hp := hs.ticket w j hj
  exact ⟨hp.collection, hp.header, hp.raw⟩

end LongTails.Proofs.BirchCollectionPoolTrace
