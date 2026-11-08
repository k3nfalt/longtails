import LongTails.Proofs.BirchCollectionBatches

namespace LongTails.Proofs.BirchCollectionPublication

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionExecution

structure MergeData (s t : TraceState) (owner left right : ℕ) : Prop where
  stateCount : t.nextState = s.nextState + 1
  oldState : ∀ i < s.nextState, t.states i = s.states i
  newState : t.states s.nextState =
    { owner, history := (s.states left).history ∪ (s.states right).history }

lemma merge_data (s : TraceState) (owner left right common : ℕ) :
    MergeData s (step s (.merge owner left right common)) owner left right := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    exact step_old_state s _ i hi
  · simp [step]

lemma merge_mark_valid (workers : ℕ) (s : TraceState) (owner left right common : ℕ)
    (hmerge : (Event.merge owner left right common).Valid workers s)
    (hhead : s.markers.getLast?.getD 0 = left) :
    ValidFrom workers s [.merge owner left right common, .mark s.nextState] := by
  let t := step s (.merge owner left right common)
  have hdata : MergeData s t owner left right := merge_data _ _ _ _ _
  refine ⟨hmerge, ⟨?_, ?_⟩, trivial⟩
  · exact Nat.lt_succ_self _
  · change (t.states (s.markers.getLast?.getD 0)).history ⊆ (t.states s.nextState).history
    rw [hhead, hdata.oldState _ hmerge.2.1, hdata.newState]
    exact subset_union_left

lemma finish_merge_history (s : TraceState) (c head k j : ℕ)
    (hhead : head < s.nextState) (hsource : (s.collections c).source < s.nextState)
    (hdir : s.nextDirection = k)
    (hcur : (s.states head).history = range k)
    (hquery : (s.states (s.collections c).source).history = range j) (hj : j ≤ k) :
    let t := step s (.finish c)
    (t.states (s.collections c).source).history = (t.states head).history ∩
        (t.states s.nextState).history ∧
      (t.states head).history ∪ (t.states s.nextState).history = range (k + 1) := by
  let t := step s (.finish c)
  have hs : (t.states (s.collections c).source).history = range j :=
    congrArg StateRecord.history (step_old_state s (.finish c) _ hsource) |>.trans hquery
  have hh : (t.states head).history = range k :=
    congrArg StateRecord.history (step_old_state s (.finish c) _ hhead) |>.trans hcur
  have hn : (t.states s.nextState).history = insert k (range j) := by
    simp only [t, step, Function.update_self, hdir, hquery]
  change (t.states (s.collections c).source).history = _ ∧ _
  rw [hs, hh, hn]
  constructor
  · ext a
    simp only [mem_range, mem_inter, mem_insert]
    omega
  · rw [range_add_one]
    ext a
    simp only [mem_range, mem_union, mem_insert]
    omega

structure Extends (s t : TraceState) : Prop where
  stateCount : s.nextState ≤ t.nextState
  directionCount : s.nextDirection ≤ t.nextDirection
  oldState : ∀ i < s.nextState, t.states i = s.states i
  oldDirection : ∀ i < s.nextDirection, t.directions i = s.directions i
  rawCount : s.nextRaw ≤ t.nextRaw

lemma extends_refl (s : TraceState) : Extends s s :=
  ⟨le_rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl, le_rfl⟩

lemma Extends.trans {s t u : TraceState} (h₁ : Extends s t) (h₂ : Extends t u) : Extends s u :=
  ⟨h₁.stateCount.trans h₂.stateCount, h₁.directionCount.trans h₂.directionCount,
    fun i hi => (h₂.oldState i (hi.trans_le h₁.stateCount)).trans (h₁.oldState i hi),
    fun i hi => (h₂.oldDirection i (hi.trans_le h₁.directionCount)).trans (h₁.oldDirection i hi),
    h₁.rawCount.trans h₂.rawCount⟩

lemma extends_step (s : TraceState) (e : Event) : Extends s (step s e) :=
  ⟨step_state_mono s e, step_direction_mono s e, step_old_state s e, step_old_direction s e,
    by cases e <;> simp [step]⟩

lemma extends_fold (s : TraceState) (es : List Event) : Extends s (es.foldl step s) := by
  induction es generalizing s with
  | nil => exact extends_refl _
  | cons e es ih => exact (extends_step s e).trans (ih (step s e))

end LongTails.Proofs.BirchCollectionPublication
