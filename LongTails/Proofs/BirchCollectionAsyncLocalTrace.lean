import LongTails.Algorithms.BirchCollectionAsyncLocal
import LongTails.Proofs.BirchCollectionPrivateChain
import LongTails.Proofs.BirchCollectionAcceptedOrder

namespace LongTails.Proofs.BirchCollectionAsyncLocalTrace

open Finset
open LongTails.Setups.BirchCollections (TraceState StateRecord Direction RawRecord Collection run step
  ValidFrom)
open LongTails.Algorithms.BirchCollectionAsyncLocal
open LongTails.Algorithms.BirchCollectionDelayed (Ticket)
open LongTails.Algorithms.BirchCollectionLocal (localComplete)
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionPrivatePacket
open LongTails.Proofs.BirchCollectionPrivateChain
open LongTails.Proofs.BirchCollectionPublication

local notation "PhysicalEvent" => LongTails.Setups.BirchCollections.Event

def prefixSet (labels : List ℕ) (n : ℕ) : Finset ℕ := (labels.take n).toFinset

def savedIndex (frontiers : List ℕ) (n : ℕ) : ℕ := frontiers[n]?.getD 0

structure AcceptedDirection (s : TraceState) (accepted frontiers : List ℕ)
    (B window : ℕ) (move : ℝ) (n label : ℕ) : Prop where
  frontierBound : savedIndex frontiers n ≤ n
  delayBound : n - savedIndex frontiers n ≤ window
  includes : prefixSet accepted (savedIndex frontiers n) ⊆ (s.directions label).history
  prior : (s.directions label).history ⊆ prefixSet accepted n
  refresh : (s.directions label).refresh = 1
  movement : (s.directions label).movement = move
  raw : (s.directions label).raw.length = B

structure Main (s : TraceState) (head rounds : ℕ) (accepted frontiers : List ℕ)
    (G M B : ℕ) (move : ℝ) : Prop where
  count : accepted.length = rounds * M
  frontierCount : frontiers.length = accepted.length
  unique : accepted.Nodup
  labels : ∀ d ∈ accepted, d < s.nextDirection
  markerCount : s.markers.length = rounds + 1
  headMarker : s.markers.getLast?.getD 0 = head
  headBound : head < s.nextState
  headHistory : (s.states head).history = accepted.toFinset
  markers : ∀ k ≤ rounds, (s.states (s.markers[k]?.getD 0)).history = prefixSet accepted (k * M)
  directions : ∀ n (hn : n < accepted.length),
    AcceptedDirection s accepted frontiers B (delayWindow G M) move n accepted[n]

structure Branch (s : TraceState) (rounds : ℕ) (accepted : List ℕ) (M B : ℕ)
    (move : ℝ) (worker : Worker) : Prop where
  age : worker.round ≤ rounds
  baseHistory : (s.states worker.base).history = prefixSet accepted (worker.round * M)
  chain : Chain s worker.base worker.head worker.directions B move
  separate : Disjoint worker.directions.toFinset accepted.toFinset

structure Data {m : ℕ} (s : Controller m) (G M B : ℕ) (move : ℝ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  main : Main s.trace s.main s.rounds s.accepted s.frontiers G M B move
  branch : ∀ w, Branch s.trace s.rounds s.accepted M B move (s.worker w)
  disjoint : ∀ w v, w ≠ v →
    Disjoint (s.worker w).directions.toFinset (s.worker v).directions.toFinset
  ticket : ∀ w j, (s.worker w).pending = some j →
    PrivateTicket s.trace j.collection j.firstRaw (w.val + 1) (s.worker w).head B move
  distinct : ∀ w v (j t : Ticket), (s.worker w).pending = some j →
    (s.worker v).pending = some t → w ≠ v → j.collection ≠ t.collection

lemma main_extend {s t : TraceState} {head rounds G M B : ℕ} {move : ℝ}
    {accepted frontiers : List ℕ} (h : Main s head rounds accepted frontiers G M B move)
    (he : Extends s t) (hm : t.markers = s.markers)
    (hbound : ∀ a ∈ s.markers, a < s.nextState) :
    Main t head rounds accepted frontiers G M B move := by
  refine ⟨h.count, h.frontierCount, h.unique, fun d hd => (h.labels d hd).trans_le he.directionCount,
    by rw [hm]; exact h.markerCount, by rw [hm]; exact h.headMarker,
    h.headBound.trans_le he.stateCount, by rw [he.oldState _ h.headBound]; exact h.headHistory, ?_, ?_⟩
  · intro k hk
    have hidx : k < s.markers.length := by rw [h.markerCount]; omega
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

lemma branch_extend {s t : TraceState} {rounds M B : ℕ} {accepted : List ℕ}
    {worker : Worker} {move : ℝ}
    (h : Branch s rounds accepted M B move worker) (he : Extends s t) :
    Branch t rounds accepted M B move worker := by
  exact ⟨h.age, by rw [he.oldState _ h.chain.baseBound]; exact h.baseHistory,
    h.chain.extend he, h.separate⟩

lemma initial_data (m G M B : ℕ) (move : ℝ) : Data (m := m) {} G M B move := by
  refine ⟨rfl, trivial, by simp [RetiredPast], ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp, rfl, List.nodup_nil, by simp, rfl, rfl, Nat.one_pos, rfl, ?_, ?_⟩
    · intro k hk
      have he : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [prefixSet]
    · simp
  · intro w
    exact ⟨le_rfl, by simp [prefixSet], chain_initial _ 0 B move Nat.one_pos, by simp⟩
  · simp
  · simp
  · simp

lemma append_legal {m G M B : ℕ} {move : ℝ} {s : Controller m} (hs : Data s G M B move)
    (events : List PhysicalEvent) (he : ValidFrom (m + 1) s.trace events) :
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

lemma marker_bounds {m G M B : ℕ} {s : Controller m} {move : ℝ} (hs : Data s G M B move) :
    ∀ a ∈ s.trace.markers, a < s.trace.nextState := by
  rw [← hs.represented]
  exact LongTails.Proofs.BirchCollectionOrdering.markers_bound_run _ _ hs.legal

lemma data_query {m G M B : ℕ} {move : ℝ} (s : Controller m) (w : Fin m)
    (hs : Data s G M B move) (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1) :
    Data (advance B G M move s (.query w)) G M B move := by
  let owner := w.val + 1
  let source := (s.worker w).head
  let cap := LongTails.Setups.BirchCollections.Event.capture owner source B 1 move
  let es := cap :: List.replicate B (LongTails.Setups.BirchCollections.Event.issue s.trace.nextCollection owner)
  let t := step s.trace cap
  let out := advance B G M move s (.query w)
  let ticket : Ticket := ⟨s.trace.nextCollection, s.trace.nextRaw⟩
  obtain ⟨hv, hi, hn⟩ := launch_private (m + 1) s.trace owner source B move
    (Nat.succ_lt_succ w.isLt) (hs.branch w).chain.headBound hB hm hm' hs.retired
  change IssueData t out.trace s.trace.nextCollection owner B at hi
  have hf := hi.fields
  have hc : out.trace.nextCollection = s.trace.nextCollection + 1 := congrArg TraceState.nextCollection hf
  have hp (v : Fin m) : (out.worker v).pending =
      (Function.update s.worker w {s.worker w with pending := some ticket} v).pending := rfl
  have hworkers (v : Fin m) : (out.worker v).base = (s.worker v).base ∧
      (out.worker v).head = (s.worker v).head ∧ (out.worker v).round = (s.worker v).round ∧
      (out.worker v).directions = (s.worker v).directions := by
    let u := Function.update s.worker w {s.worker w with pending := some ticket} v
    change u.base = _ ∧ u.head = _ ∧ u.round = _ ∧ u.directions = _
    by_cases he : v = w
    · subst v
      simp [u]
    · simp [u, Function.update_of_ne he]
  have he : Extends s.trace out.trace := extends_fold _ es
  have hmarks : out.trace.markers = s.trace.markers := by
    simpa only [t, cap, step] using congrArg TraceState.markers hf
  obtain ⟨hr, hl, hret⟩ := append_legal hs es hv
  change Data out G M B move
  refine ⟨hr, hl, hret, main_extend hs.main he hmarks (marker_bounds hs), ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨hb, hh, hround, hdir⟩ := hworkers v
    have h := branch_extend (hs.branch v) he
    exact ⟨hround.symm ▸ h.age, by rw [hb, hround]; exact h.baseHistory,
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

lemma data_localReply {m K G M B : ℕ} {move : ℝ} (s : Controller m) (w : Fin m)
    (hs : Data s G M B move) (hw : Enabled K M s (.localReply w)) :
    Data (advance B G M move s (.localReply w)) G M B move := by
  cases h : (s.worker w).pending with
  | none =>
    have hw' : ((s.worker w).pending).isSome := hw.2.2
    simp [h] at hw'
  | some ticket =>
    let out := advance B G M move s (.localReply w)
    let n := s.trace.nextDirection
    let new : Worker := {s.worker w with
      head := s.trace.nextState
      directions := (s.worker w).directions ++ [n]
      pending := none}
    let es := localComplete B ticket
    let t := es.foldl step s.trace
    have hout : out = {s.append es with worker := Function.update s.worker w new} := by
      simp [out, advance, h, new, es, n]
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
    have hfresh (v : Fin m) : n ∉ (s.worker v).directions.toFinset := fun hn =>
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
    have hround : out.rounds = s.rounds := by rw [hout]; rfl
    have hmain : out.main = s.main := by rw [hout]; rfl
    have haccept : out.accepted = s.accepted := by rw [hout]; rfl
    have hfront : out.frontiers = s.frontiers := by rw [hout]; rfl
    change Data out G M B move
    refine ⟨by rw [hout]; exact hr, by rw [hout]; exact hl, by rw [hout]; exact hret,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [htrace, hmain, hround, haccept, hfront]
      exact main_extend hs.main he hf.markers (marker_bounds hs)
    · intro v
      rw [htrace, hround, haccept]
      by_cases hv : v = w
      · subst v
        rw [hnew]
        have hb := hs.branch w
        refine ⟨hb.age, ?_, chain_finish hb.chain hf, ?_⟩
        · change (t.states (s.worker w).base).history = _
          rw [he.oldState _ hb.chain.baseBound]
          exact hb.baseHistory
        · change Disjoint (((s.worker w).directions ++ [n]).toFinset) s.accepted.toFinset
          rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, disjoint_union_left]
          exact ⟨hb.separate, disjoint_singleton_left.mpr hfreshA⟩
      · rw [hsame v hv]
        exact branch_extend (hs.branch v) he
    · intro v u hne
      by_cases hv : v = w
      · subst v
        rw [hnew, hsame u (Ne.symm hne)]
        change Disjoint (((s.worker w).directions ++ [n]).toFinset) (s.worker u).directions.toFinset
        rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq, disjoint_union_left]
        exact ⟨hs.disjoint w u hne, disjoint_singleton_left.mpr (hfresh u)⟩
      · rw [hsame v hv]
        by_cases hu : u = w
        · subst u
          rw [hnew]
          change Disjoint (s.worker v).directions.toFinset (((s.worker w).directions ++ [n]).toFinset)
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

end LongTails.Proofs.BirchCollectionAsyncLocalTrace
