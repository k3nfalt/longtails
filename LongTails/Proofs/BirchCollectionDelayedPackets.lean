import LongTails.Algorithms.BirchCollectionDelayed
import LongTails.Proofs.BirchCollectionPackets
import LongTails.Proofs.BirchCollectionPublication

namespace LongTails.Proofs.BirchCollectionDelayedPackets

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed
open LongTails.Proofs.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionPackets
open LongTails.Proofs.BirchCollectionPublication

structure TicketData (s : TraceState) (t : Ticket) (source worker B : ℕ) (movement : ℝ) : Prop where
  collection : t.collection < s.nextCollection
  header : s.collections t.collection =
    { owner := worker, source, size := B, refresh := 1, movement }
  raw : ∀ q ∈ List.range' t.firstRaw B,
    q < s.nextRaw ∧ q ∉ s.retired ∧ s.raws q = { collection := t.collection, worker }

structure LaunchData (s t : TraceState) (source worker B : ℕ) (movement : ℝ) : Prop where
  issue : IssueData (step s (.capture worker source B 1 movement)) t s.nextCollection worker B
  ticket : TicketData t ⟨s.nextCollection, s.nextRaw⟩ source worker B movement

lemma launch_data (workers : ℕ) {m : ℕ} (s : Controller m) (w : Fin m) (B : ℕ)
    (movement : ℝ) (hw : w.val + 1 < workers)
    (hsource : (s.saved w).point < s.trace.nextState) (hB : 0 < B)
    (hm0 : 0 ≤ movement) (hm1 : movement ≤ 1) (hret : RetiredPast s.trace) :
    let events := queryEvents B movement s w
    ValidFrom workers s.trace events ∧
      LaunchData s.trace (events.foldl step s.trace) (s.saved w).point (w.val + 1) B movement := by
  let cap := Event.capture (w.val + 1) (s.saved w).point B 1 movement
  let t := step s.trace cap
  have hcap : cap.Valid workers s.trace := ⟨hw, hsource, hB, hm0, hm1, le_rfl⟩
  have hcapData : t.collections s.trace.nextCollection =
      { owner := w.val + 1, source := (s.saved w).point, size := B, refresh := 1, movement } := by
    simp [t, cap, step]
  have hi : (Event.issue s.trace.nextCollection (w.val + 1)).Valid workers t :=
    ⟨Nat.lt_succ_self _, hw, by rw [hcapData]⟩
  obtain ⟨hv, he⟩ := issue_data workers t _ _ B hi
  let u := (List.replicate B (Event.issue s.trace.nextCollection (w.val + 1))).foldl step t
  change IssueData t u s.trace.nextCollection (w.val + 1) B at he
  change ValidFrom workers s.trace
      (cap :: List.replicate B (Event.issue s.trace.nextCollection (w.val + 1))) ∧
    LaunchData s.trace u (s.saved w).point (w.val + 1) B movement
  have hfield := he.fields
  refine ⟨⟨hcap, hv⟩, ⟨he, ?_⟩⟩
  constructor
  · rw [congrArg TraceState.nextCollection hfield]
    exact Nat.lt_succ_self _
  · rw [congrArg TraceState.collections hfield]
    exact hcapData
  · intro q hq
    obtain ⟨i, hi, hiq⟩ := List.mem_range'.mp hq
    change q = s.trace.nextRaw + 1 * i at hiq
    have hlo : s.trace.nextRaw ≤ q := by omega
    have hhi : q < s.trace.nextRaw + B := by omega
    refine ⟨?_, ?_, he.newRaw q hq⟩
    · rw [he.nextRaw]
      exact hhi
    · rw [congrArg TraceState.retired hfield]
      exact fun h => (not_lt_of_ge hlo) (mem_range.mp (hret h))

structure LandingData (s t : TraceState) (ticket : Ticket) (B : ℕ) : Prop where
  rawCount : t.nextRaw = s.nextRaw
  raw : t.raws = s.raws
  retired : t.retired = s.retired ∪ (List.range' ticket.firstRaw B).toFinset
  collectionCount : t.nextCollection = s.nextCollection
  oldCollection : ∀ c ≠ ticket.collection, t.collections c = s.collections c

structure CommitData (s t : TraceState) (j : Ticket) (source B k a : ℕ)
    (movement : ℝ) : Prop where
  landing : LandingData s t j B
  stateCount : t.nextState = s.nextState + 2
  directionCount : t.nextDirection = k + 1
  oldState : ∀ i < s.nextState, t.states i = s.states i
  oldDirection : ∀ i < k, t.directions i = s.directions i
  newDirection : t.directions k =
    { collection := j.collection, source, target := s.nextState, history := range a,
      refresh := 1, movement, raw := List.range' j.firstRaw B }
  newMain : (t.states (s.nextState + 1)).history = range (k + 1)
  markers : t.markers = s.markers ++ [s.nextState + 1]

lemma commit_data (workers : ℕ) (s : TraceState) (ticket : Ticket) (head source worker B k a : ℕ)
    (movement : ℝ) (hworkers : 0 < workers)
    (hticket : TicketData s ticket source worker B movement)
    (hhead : head < s.nextState) (hsource : source < s.nextState)
    (hmarker : s.markers.getLast?.getD 0 = head)
    (hcur : (s.states head).history = range k)
    (hquery : (s.states source).history = range a)
    (hdir : s.nextDirection = k) (ha : a ≤ k) :
    let raw := List.range' ticket.firstRaw B
    let events := raw.map Event.receive ++
      [.finish ticket.collection, .merge 0 head s.nextState source, .mark (s.nextState + 1)]
    ValidFrom workers s events ∧ CommitData s (events.foldl step s) ticket source B k a movement := by
  let raw := List.range' ticket.firstRaw B
  let c := ticket.collection
  have hr (q : ℕ) (hq : q ∈ raw) :
      q < s.nextRaw ∧ q ∉ s.retired ∧ (s.raws q).collection = c := by
    obtain ⟨h₁, h₂, h₃⟩ := hticket.raw q hq
    exact ⟨h₁, h₂, congrArg RawRecord.collection h₃⟩
  obtain ⟨hv, he⟩ := receive_data workers s c raw (by rw [hticket.header]) List.nodup_range' hr
  let t := (raw.map Event.receive).foldl step s
  let u := step t (.finish c)
  let v := step u (.merge 0 head s.nextState source)
  let out := step v (.mark (s.nextState + 1))
  change ReceiveData s t c raw at he
  have hc : t.collections c =
      { owner := worker, source, size := B, refresh := 1, movement, delivered := raw } := by
    rw [he.collection, hticket.header]
    rfl
  have hn : t.nextState = s.nextState := by simpa only using congrArg TraceState.nextState he.fields
  have hd : t.nextDirection = k := (congrArg TraceState.nextDirection he.fields).trans hdir
  have hstates : t.states = s.states := by simpa only using congrArg TraceState.states he.fields
  have hdirs : t.directions = s.directions := by simpa only using congrArg TraceState.directions he.fields
  have hmarks : t.markers = s.markers := by simpa only using congrArg TraceState.markers he.fields
  have hcc : t.nextCollection = s.nextCollection := by simpa only using congrArg TraceState.nextCollection he.fields
  have hfinish : (Event.finish c).Valid workers t := by
    simp [Event.Valid, hc, hcc, show c < s.nextCollection from hticket.collection, raw]
  have hsc : (t.collections c).source = source := congrArg Collection.source hc
  obtain ⟨hinter, hunion⟩ := finish_merge_history t c head k a (hn.symm ▸ hhead)
    (by rwa [hsc, hn]) hd (by rwa [hstates]) (by rwa [hsc, hstates]) ha
  change (u.states (t.collections c).source).history = _ at hinter
  rw [hsc, hn] at hinter
  change (u.states head).history ∪ (u.states t.nextState).history = _ at hunion
  rw [hn] at hunion
  have hmerge : (Event.merge 0 head s.nextState source).Valid workers u := by
    have hnext : u.nextState = s.nextState + 1 := congrArg (· + 1) hn
    refine ⟨hworkers, ?_, ?_, ?_, hinter⟩ <;> rw [hnext] <;> omega
  have hmark : ValidFrom workers u [.merge 0 head s.nextState source, .mark (s.nextState + 1)] := by
    have hm : u.markers.getLast?.getD 0 = head := by
      change t.markers.getLast?.getD 0 = head
      rw [hmarks]
      exact hmarker
    simpa only [show u.nextState = s.nextState + 1 from congrArg (· + 1) hn] using
      merge_mark_valid workers u 0 head s.nextState source hmerge hm
  refine ⟨(valid_append workers s (raw.map Event.receive) _).2 ⟨hv, hfinish, hmark⟩, ?_⟩
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change CommitData s out ticket source B k a movement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by
        change t.nextRaw = s.nextRaw
        simpa only using congrArg TraceState.nextRaw he.fields,
      by
        change t.raws = s.raws
        simpa only using congrArg TraceState.raws he.fields,
      he.retired, hcc, ?_⟩
    intro i hi
    change Function.update t.collections c _ i = _
    rw [Function.update_of_ne hi, he.other i hi]
  · exact congrArg (· + 1 + 1) hn
  · exact congrArg (· + 1) hd
  · intro i hi
    have hi' : i < t.nextState := hn.symm ▸ hi
    have hi'' : i < u.nextState := hi'.trans (Nat.lt_succ_self _)
    exact (step_old_state u (.merge 0 head s.nextState source) i hi'').trans
      ((step_old_state t (.finish c) i hi').trans (congrFun hstates i))
  · intro i hi
    exact (step_old_direction t (.finish c) i (hd.symm ▸ hi)).trans (congrFun hdirs i)
  · change u.directions k = _
    simp only [u, step, hd, Function.update_self, hc, hstates, hn, hquery, c, raw]
  · change (v.states (s.nextState + 1)).history = _
    rw [← show u.nextState = s.nextState + 1 from congrArg (· + 1) hn]
    change ((step u (.merge 0 head s.nextState source)).states u.nextState).history = _
    rw [(merge_data u 0 head s.nextState source).newState]
    exact hunion
  · exact congrArg (· ++ [s.nextState + 1]) hmarks

lemma rejected_data (workers : ℕ) (s : TraceState) (ticket : Ticket) (source worker B : ℕ)
    (movement : ℝ) (hticket : TicketData s ticket source worker B movement) :
    let qs := List.range' ticket.firstRaw B
    let events := qs.map Event.discard ++ [.cancel ticket.collection]
    let out := events.foldl step s
    ValidFrom workers s events ∧ LandingData s out ticket B ∧
      out = {s with
        retired := s.retired ∪ qs.toFinset
        collections := Function.update s.collections ticket.collection
          {s.collections ticket.collection with closed := true} } := by
  let qs := List.range' ticket.firstRaw B
  obtain ⟨hv, he⟩ := discard_data workers s qs List.nodup_range' (fun q hq =>
    ⟨(hticket.raw q hq).1, (hticket.raw q hq).2.1⟩)
  let t := (qs.map Event.discard).foldl step s
  change t = _ at he
  have hcancel : (Event.cancel ticket.collection).Valid workers t := by
    rw [he]
    exact ⟨hticket.collection, by rw [hticket.header]⟩
  refine ⟨(valid_append workers s (qs.map Event.discard) _).2 ⟨hv, hcancel, trivial⟩, ?_⟩
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change LandingData s (step t (.cancel ticket.collection)) ticket B ∧
    step t (.cancel ticket.collection) = _
  rw [he]
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
  intro i hi
  simp [step, Function.update_of_ne hi]

end LongTails.Proofs.BirchCollectionDelayedPackets
