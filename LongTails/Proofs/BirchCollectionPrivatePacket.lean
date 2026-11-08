import LongTails.Proofs.BirchCollectionPackets
import LongTails.Proofs.BirchCollectionPublication

namespace LongTails.Proofs.BirchCollectionPrivatePacket

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionPackets

structure PrivateTicket (s : TraceState) (c first owner source B : ℕ) (move : ℝ) : Prop where
  collection : c < s.nextCollection
  header : s.collections c = {owner, source, size := B, refresh := 1, movement := move}
  raw : ∀ q ∈ List.range' first B, q < s.nextRaw ∧ q ∉ s.retired ∧
    s.raws q = {collection := c, worker := owner}

lemma launch_private (workers : ℕ) (s : TraceState) (owner source B : ℕ)
    (move : ℝ) (hw : owner < workers) (hsource : source < s.nextState)
    (hB : 0 < B) (hm : 0 ≤ move) (hm' : move ≤ 1) (hr : RetiredPast s) :
    let cap := Event.capture owner source B 1 move
    let t := step s cap
    let queries := List.replicate B (Event.issue s.nextCollection owner)
    let u := queries.foldl step t
    ValidFrom workers s (cap :: queries) ∧ IssueData t u s.nextCollection owner B ∧
      PrivateTicket u s.nextCollection s.nextRaw owner source B move := by
  let cap := Event.capture owner source B 1 move
  let t := step s cap
  have hcap : cap.Valid workers s := ⟨hw, hsource, hB, hm, hm', le_rfl⟩
  have hheader : t.collections s.nextCollection =
      {owner, source, size := B, refresh := 1, movement := move} := by simp [t, cap, step]
  have hi : (Event.issue s.nextCollection owner).Valid workers t :=
    ⟨Nat.lt_succ_self _, hw, by rw [hheader]⟩
  obtain ⟨hv, he⟩ := issue_data workers t _ _ B hi
  let u := (List.replicate B (Event.issue s.nextCollection owner)).foldl step t
  change IssueData t u s.nextCollection owner B at he
  change ValidFrom workers s (cap :: List.replicate B (.issue s.nextCollection owner)) ∧
    IssueData t u s.nextCollection owner B ∧ PrivateTicket u s.nextCollection s.nextRaw owner source B move
  refine ⟨⟨hcap, hv⟩, he, ?_⟩
  constructor
  · rw [congrArg TraceState.nextCollection he.fields]
    exact Nat.lt_succ_self _
  · rw [congrArg TraceState.collections he.fields]
    exact hheader
  · intro q hq
    obtain ⟨j, hj, hqj⟩ := List.mem_range'.mp hq
    change q = s.nextRaw + 1 * j at hqj
    refine ⟨?_, ?_, he.newRaw q hq⟩
    · rw [he.nextRaw]
      change q < s.nextRaw + B
      omega
    · rw [congrArg TraceState.retired he.fields]
      intro hf
      have hlt : q < s.nextRaw := mem_range.mp (hr hf)
      omega

structure FinishData (s t : TraceState) (c first owner source B : ℕ) (move : ℝ) : Prop where
  nextState : t.nextState = s.nextState + 1
  nextDirection : t.nextDirection = s.nextDirection + 1
  nextCollection : t.nextCollection = s.nextCollection
  nextRaw : t.nextRaw = s.nextRaw
  raw : t.raws = s.raws
  retired : t.retired = s.retired ∪ (List.range' first B).toFinset
  markers : t.markers = s.markers
  oldState : ∀ i < s.nextState, t.states i = s.states i
  oldDirection : ∀ i < s.nextDirection, t.directions i = s.directions i
  oldCollection : ∀ j ≠ c, t.collections j = s.collections j
  newState : t.states s.nextState = {owner, history := insert s.nextDirection (s.states source).history}
  newDirection : t.directions s.nextDirection =
    { collection := c, source, target := s.nextState, history := (s.states source).history,
      refresh := 1, movement := move, raw := List.range' first B }

lemma finish_private (workers : ℕ) (s : TraceState) (c first owner source B : ℕ)
    (move : ℝ) (ht : PrivateTicket s c first owner source B move) :
    let qs := List.range' first B
    let events := qs.map Event.receive ++ [.finish c]
    ValidFrom workers s events ∧ FinishData s (events.foldl step s) c first owner source B move := by
  let qs := List.range' first B
  have hr (q : ℕ) (hq : q ∈ qs) : q < s.nextRaw ∧ q ∉ s.retired ∧ (s.raws q).collection = c := by
    obtain ⟨h₁, h₂, h₃⟩ := ht.raw q hq
    exact ⟨h₁, h₂, congrArg RawRecord.collection h₃⟩
  obtain ⟨hv, he⟩ := receive_data workers s c qs (by rw [ht.header]) List.nodup_range' hr
  let t := (qs.map Event.receive).foldl step s
  let u := step t (.finish c)
  change ReceiveData s t c qs at he
  have hc : t.collections c =
      {owner, source, size := B, refresh := 1, movement := move, delivered := qs} := by
    rw [he.collection, ht.header]
    rfl
  have hsc : t.nextState = s.nextState := by simpa only using congrArg TraceState.nextState he.fields
  have hdc : t.nextDirection = s.nextDirection := by
    simpa only using congrArg TraceState.nextDirection he.fields
  have hstates : t.states = s.states := by simpa only using congrArg TraceState.states he.fields
  have hdirs : t.directions = s.directions := by simpa only using congrArg TraceState.directions he.fields
  have hcc : t.nextCollection = s.nextCollection := by
    simpa only using congrArg TraceState.nextCollection he.fields
  have hfinish : (Event.finish c).Valid workers t := by simp [Event.Valid, hcc, hc, ht.collection, qs]
  refine ⟨(valid_append workers s (qs.map Event.receive) _).2 ⟨hv, hfinish, trivial⟩, ?_⟩
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change FinishData s u c first owner source B move
  refine ⟨congrArg (· + 1) hsc, congrArg (· + 1) hdc, hcc, ?_, ?_, he.retired, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · change t.nextRaw = s.nextRaw
    simpa only using congrArg TraceState.nextRaw he.fields
  · change t.raws = s.raws
    simpa only using congrArg TraceState.raws he.fields
  · change t.markers = s.markers
    simpa only using congrArg TraceState.markers he.fields
  · intro i hi
    exact (step_old_state t (.finish c) i (hsc.symm ▸ hi)).trans (congrFun hstates i)
  · intro i hi
    exact (step_old_direction t (.finish c) i (hdc.symm ▸ hi)).trans (congrFun hdirs i)
  · intro j hj
    change Function.update t.collections c _ j = _
    rw [Function.update_of_ne hj, he.other j hj]
  · simp [u, step, hsc, hdc, hc, hstates]
  · simp [u, step, hdc, hc, hsc, hstates, qs]

end LongTails.Proofs.BirchCollectionPrivatePacket
