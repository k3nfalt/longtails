import LongTails.Algorithms.BirchCollectionBatches
import LongTails.Proofs.BirchCollectionStructure

namespace LongTails.Proofs.BirchCollectionBatches

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchCollectionStructure

lemma valid_append (workers : ℕ) (s : TraceState) (as bs : List Event) :
    ValidFrom workers s (as ++ bs) ↔
      ValidFrom workers s as ∧ ValidFrom workers (as.foldl step s) bs := by
  induction as generalizing s with
  | nil => simp [ValidFrom]
  | cons a as ih =>
      simp only [List.cons_append, List.foldl_cons, ValidFrom, ih, and_assoc]

def RetiredPast (s : TraceState) : Prop := s.retired ⊆ range s.nextRaw

lemma retired_past_step (workers : ℕ) (s : TraceState) (e : Event)
    (hs : RetiredPast s) (he : e.Valid workers s) : RetiredPast (step s e) := by
  cases e with
  | issue c w => exact hs.trans (range_mono (Nat.le_succ _))
  | receive q => exact insert_subset (mem_range.mpr he.1) hs
  | discard q => exact insert_subset (mem_range.mpr he.1) hs
  | _ => exact hs

lemma retired_past_fold (workers : ℕ) (s : TraceState) (events : List Event)
    (hs : RetiredPast s) (he : ValidFrom workers s events) :
    RetiredPast (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e es ih => exact ih (step s e) (retired_past_step workers s e hs he.1) he.2

lemma receive_now_valid (workers : ℕ) (s : TraceState) (c w : ℕ)
    (hs : RetiredPast s) (hc : c < s.nextCollection)
    (ho : (s.collections c).closed = false) (hw : w < workers) :
    ValidFrom workers s [.issue c w, .receive s.nextRaw] := by
  refine ⟨⟨hc, hw, ho⟩, ⟨?_, trivial⟩⟩
  have hf : s.nextRaw ∉ s.retired := fun h => (Nat.lt_irrefl _ (mem_range.mp (hs h))).elim
  simp [Event.Valid, step, hf, ho]

structure ReplyEffect (s t : TraceState) (collection count : ℕ) : Prop where
  raw : t.nextRaw = s.nextRaw + count
  collectionCount : t.nextCollection = s.nextCollection
  stateCount : t.nextState = s.nextState
  directionCount : t.nextDirection = s.nextDirection
  states : t.states = s.states
  directions : t.directions = s.directions
  markers : t.markers = s.markers
  value : t.collections collection =
    { s.collections collection with
      delivered := (s.collections collection).delivered ++ List.range' s.nextRaw count }

lemma batch_replies (workers : ℕ) (s : TraceState) (c : ℕ) (ws : List ℕ)
    (hs : RetiredPast s) (hc : c < s.nextCollection)
    (ho : (s.collections c).closed = false) (hw : ∀ w ∈ ws, w < workers) :
    ValidFrom workers s (batchReplies c s ws) ∧
      ReplyEffect s ((batchReplies c s ws).foldl step s) c ws.length := by
  induction ws generalizing s with
  | nil =>
      exact ⟨trivial, ⟨by simp [batchReplies], rfl, rfl, rfl, rfl, rfl, rfl,
        by simp [batchReplies]⟩⟩
  | cons w ws ih =>
      let t := receiveNow s c w
      have hv := receive_now_valid workers s c w hs hc ho (hw w (by simp))
      have ht : RetiredPast t := retired_past_fold workers s _ hs hv
      have hval : t.collections c =
          { s.collections c with delivered := (s.collections c).delivered ++ [s.nextRaw] } := by
        simp [t, receiveNow, step]
      have hcount : t.nextCollection = s.nextCollection := rfl
      obtain ⟨hv', he⟩ := ih t ht (hcount.symm ▸ hc)
        (by rw [hval]; exact ho) (fun u hu => hw u (by simp [hu]))
      refine ⟨⟨hv.1, hv.2.1, hv'⟩, ?_⟩
      change ReplyEffect s ((batchReplies c t ws).foldl step t) c (ws.length + 1)
      constructor
      · rw [he.raw]
        change s.nextRaw + 1 + ws.length = _
        omega
      · exact he.collectionCount.trans rfl
      · exact he.stateCount.trans rfl
      · exact he.directionCount.trans rfl
      · exact he.states.trans rfl
      · exact he.directions.trans rfl
      · exact he.markers.trans rfl
      · rw [he.value, hval]
        change { s.collections c with delivered :=
            ((s.collections c).delivered ++ [s.nextRaw]) ++ List.range' (s.nextRaw + 1) ws.length } = _
        simp [List.range'_succ, List.append_assoc]

structure BatchEffect (s t : TraceState) (owner source size : ℕ) (move : ℝ := 1) : Prop where
  raw : t.nextRaw = s.nextRaw + size
  collectionCount : t.nextCollection = s.nextCollection + 1
  stateCount : t.nextState = s.nextState + 1
  directionCount : t.nextDirection = s.nextDirection + 1
  markers : t.markers = s.markers ++ [s.nextState]
  oldState : ∀ a, a < s.nextState → t.states a = s.states a
  oldDirection : ∀ a, a < s.nextDirection → t.directions a = s.directions a
  state : t.states s.nextState =
    { owner, history := insert s.nextDirection (s.states source).history }
  direction : t.directions s.nextDirection =
    { collection := s.nextCollection, source, target := s.nextState,
      history := (s.states source).history, refresh := 1, movement := move,
      raw := List.range' s.nextRaw size }

lemma batch_and_mark_with_move (workers : ℕ) (s : TraceState) (owner source : ℕ) (ws : List ℕ)
    (move : ℝ) (hm0 : 0 ≤ move) (hm1 : move ≤ 1)
    (hs : RetiredPast s) (howner : owner < workers) (hsource : source < s.nextState)
    (hsize : 0 < ws.length) (hw : ∀ w ∈ ws, w < workers)
    (hmark : (s.states (s.markers.getLast?.getD 0)).history ⊆ (s.states source).history)
    (hold : s.markers.getLast?.getD 0 < s.nextState) :
    ValidFrom workers s (batchAndMarkWithMove s owner source ws move) ∧
      BatchEffect s ((batchAndMarkWithMove s owner source ws move).foldl step s) owner source ws.length move := by
  let capture := Event.capture owner source ws.length 1 move
  let t := step s capture
  let es := batchReplies s.nextCollection t ws
  let u := es.foldl step t
  let v := step u (.finish s.nextCollection)
  have hcap : capture.Valid workers s := ⟨howner, hsource, hsize, hm0, hm1, le_rfl⟩
  have ht : RetiredPast t := retired_past_step workers s capture hs hcap
  have hc : s.nextCollection < t.nextCollection := Nat.lt_succ_self _
  have hopen : (t.collections s.nextCollection).closed = false := by simp [t, capture, step]
  obtain ⟨hvalid, he⟩ := batch_replies workers t s.nextCollection ws ht hc hopen hw
  have hraw : u.nextRaw = s.nextRaw + ws.length := he.raw
  have hcc : u.nextCollection = s.nextCollection + 1 := he.collectionCount
  have hsc : u.nextState = s.nextState := he.stateCount
  have hdc : u.nextDirection = s.nextDirection := he.directionCount
  have hstates : u.states = s.states := he.states
  have hdirs : u.directions = s.directions := he.directions
  have hmarks : u.markers = s.markers := he.markers
  have hcollection : u.collections s.nextCollection =
      { owner, source, size := ws.length, refresh := 1, movement := move,
        delivered := List.range' s.nextRaw ws.length } := by
    rw [show u.collections s.nextCollection = _ from he.value]
    simp [t, capture, step]
  have hfinish : (Event.finish s.nextCollection).Valid workers u := by
    simp [Event.Valid, hcc, hcollection]
  have hstateNew : v.states s.nextState =
      { owner, history := insert s.nextDirection (s.states source).history } := by
    simp only [v, step, hsc, Function.update_self, hdc, hcollection, hstates]
  have hstateOld (a : ℕ) (ha : a < s.nextState) : v.states a = s.states a := by
    exact (step_old_state u (.finish s.nextCollection) a (hsc.symm ▸ ha)).trans (congrFun hstates a)
  have hmarker : (Event.mark s.nextState).Valid workers v := by
    constructor
    · change s.nextState < u.nextState + 1
      omega
    · change (v.states (u.markers.getLast?.getD 0)).history ⊆ (v.states s.nextState).history
      rw [hmarks, hstateOld _ hold, hstateNew]
      exact hmark.trans (subset_insert _ _)
  refine ⟨⟨hcap, (valid_append workers t es _).2 ⟨hvalid, hfinish, hmarker, trivial⟩⟩, ?_⟩
  simp only [batchAndMarkWithMove, List.foldl_cons, List.foldl_append]
  change BatchEffect s (step v (.mark s.nextState)) owner source ws.length move
  refine ⟨hraw, hcc, ?_, ?_, ?_, hstateOld, ?_, hstateNew, ?_⟩
  · change u.nextState + 1 = s.nextState + 1
    rw [hsc]
  · change u.nextDirection + 1 = s.nextDirection + 1
    rw [hdc]
  · change u.markers ++ [s.nextState] = _
    rw [hmarks]
  · intro a ha
    exact (step_old_direction u (.finish s.nextCollection) a (hdc.symm ▸ ha)).trans
      (congrFun hdirs a)
  · change v.directions s.nextDirection = _
    simp only [v, step, hdc, Function.update_self, hcollection, hsc, hstates]

lemma batch_and_mark (workers : ℕ) (s : TraceState) (owner source : ℕ) (ws : List ℕ)
    (hs : RetiredPast s) (howner : owner < workers) (hsource : source < s.nextState)
    (hsize : 0 < ws.length) (hw : ∀ w ∈ ws, w < workers)
    (hmark : (s.states (s.markers.getLast?.getD 0)).history ⊆ (s.states source).history)
    (hold : s.markers.getLast?.getD 0 < s.nextState) :
    ValidFrom workers s (batchAndMark s owner source ws) ∧
      BatchEffect s ((batchAndMark s owner source ws).foldl step s) owner source ws.length :=
  batch_and_mark_with_move workers s owner source ws 1 zero_le_one le_rfl
    hs howner hsource hsize hw hmark hold

end LongTails.Proofs.BirchCollectionBatches
