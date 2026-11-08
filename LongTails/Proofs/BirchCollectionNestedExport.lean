import LongTails.Proofs.BirchCollectionNestedRun
import LongTails.Proofs.BirchCollectionLocalRounds

namespace LongTails.Proofs.BirchCollectionNestedExport

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round abortPending)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionGroupReady
open LongTails.Proofs.BirchCollectionNestedShape
open LongTails.Proofs.BirchCollectionNestedCollect
open LongTails.Proofs.BirchCollectionNestedReset
open LongTails.Proofs.BirchCollectionNestedRun
open LongTails.Proofs.BirchCollectionLocalPublish (abortOne RoundInfo)
open LongTails.Proofs.BirchCollectionPublication

def clusterWork {m : ℕ} (layout : Layout m) (s : State m) (i : Fin m) (d : ℕ) : Prop :=
  ∃ a : Node m, color layout a = i ∧ d ∈ hist s a

lemma collected_work {m start B : ℕ} {move : ℝ} {layout : Layout m} {s : State m} {i : Fin m}
    {pair : Round m × ℕ} (hc : Collected layout s i pair (groups layout i) start B move) (d : ℕ) :
    d ∈ (pair.1.trace.states pair.2).history ↔ clusterWork layout s i d := by
  rw [hc.history d]
  constructor
  · rintro (h | ⟨g, hg, h⟩)
    · exact ⟨.inl i, rfl, h⟩
    · exact ⟨.inr g, (cluster_member layout i g).1 hg, h⟩
  · rintro ⟨(c | g), h, hd⟩
    · change c = i at h
      subst c
      exact Or.inl hd
    · exact Or.inr ⟨g, (cluster_member layout i g).2 h, hd⟩

def materialize {m : ℕ} (layout : Layout m) (s : State m)
    (t : Round m × (Fin m → ℕ)) (i : Fin m) : Round m × (Fin m → ℕ) :=
  let (out, head) := collectCluster layout t.1 i (s.cluster i).point
  (out, Function.update t.2 i head)

structure Exported {m : ℕ} (layout : Layout m) (s : State m) (t : Round m × (Fin m → ℕ))
    (seen : List (Fin m)) (start B : ℕ) (move : ℝ) : Prop where
  frame : MergeFrame s.outer t.1
  ready : Ready layout.group t.1 start B move
  bound : ∀ i, t.2 i < t.1.trace.nextState
  history : ∀ i ∈ seen, ∀ d, d ∈ (t.1.trace.states (t.2 i)).history ↔ clusterWork layout s i d

lemma export_step {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m)
    (t : Round m × (Fin m → ℕ)) (seen : List (Fin m)) (i : Fin m)
    (hs : Shape layout s start B move) (ht : Exported layout s t seen start B move) :
    Exported layout s (materialize layout s t i) (seen ++ [i]) start B move := by
  let mid : State m := {s with outer := t.1}
  have hshape : Shape layout mid start B move := ht.frame.shape hs
  let pair := collectCluster layout t.1 i (s.cluster i).point
  have hc : Collected layout mid i pair (groups layout i) start B move := collect_data layout mid i hshape ht.ready
  have hh (a : Node m) : hist mid a = hist s a := by
    have hp : point mid a = point s a := by
      cases a with
      | inl c => rfl
      | inr g => exact congrFun ht.frame.head g
    unfold hist
    rw [hp]
    exact congrArg StateRecord.history (ht.frame.trace.oldState _ (hs.nodeBound a))
  have heq (d : ℕ) : clusterWork layout mid i d ↔ clusterWork layout s i d := by
    unfold clusterWork
    simp only [hh]
  refine ⟨ht.frame.trans hc.frame, hc.ready, ?_, ?_⟩
  · intro j
    change Function.update t.2 i pair.2 j < pair.1.trace.nextState
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      exact hc.head
    · rw [Function.update_of_ne hj]
      exact (ht.bound j).trans_le hc.frame.trace.stateCount
  · intro j hj d
    change d ∈ (pair.1.trace.states (Function.update t.2 i pair.2 j)).history ↔ _
    by_cases h : j = i
    · subst j
      rw [Function.update_self]
      exact (collected_work hc d).trans (heq d)
    · have hj' : j ∈ seen := (List.mem_append.mp hj).resolve_right (by simpa using h)
      rw [Function.update_of_ne h, hc.frame.trace.oldState _ (ht.bound j)]
      exact ht.history j hj' d

lemma export_fold {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m)
    (t : Round m × (Fin m → ℕ)) (seen ids : List (Fin m))
    (hs : Shape layout s start B move) (ht : Exported layout s t seen start B move) :
    Exported layout s (ids.foldl (materialize layout s) t) (seen ++ ids) start B move := by
  induction ids generalizing t seen with
  | nil => simpa only [List.foldl_nil, List.append_nil] using ht
  | cons i ids ih =>
    have h := ih (materialize layout s t i) (seen ++ [i]) (export_step layout s t seen i hs ht)
    simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using h

lemma collect_all {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m)
    (hs : Data layout s start B move) :
    let out := collectAll layout s (abortPending B s.outer)
    RoundInfo out start B move ∧ Extends s.outer.trace out.trace ∧
      out.completed = s.outer.completed ∧ out.trace.markers = s.outer.trace.markers := by
  let closed := abortPending B s.outer
  let t : State m := {s with outer := closed}
  obtain ⟨hr, hf, hpend⟩ := abort_fold_ready layout.group s.outer (List.finRange m) hs.ready
  have ht : Shape layout t start B move := shape_frame hs.shape hf (fun _ => rfl)
  let startPair : Round m × (Fin m → ℕ) := (closed, fun i => (s.cluster i).point)
  let last := (List.finRange m).foldl (materialize layout t) startPair
  let out := collectAll layout s closed
  have hi : Exported layout t startPair [] start B move := by
    refine ⟨MergeFrame.refl _, hr, ?_, by simp⟩
    intro i
    exact ht.nodeBound (.inl i)
  have hh : Exported layout t last (List.finRange m) start B move := by
    simpa only [List.nil_append] using export_fold layout t startPair [] (List.finRange m) ht hi
  have hout : out = {last.1 with head := last.2} := rfl
  have hb (i : Fin m) : out.head i < out.trace.nextState := by rw [hout]; exact hh.bound i
  have hmem (i : Fin m) (d : ℕ) : d ∈ (out.trace.states (out.head i)).history ↔ clusterWork layout t i d := by
    rw [hout]
    exact hh.history i (by simp) d
  have hp (w : Fin m) : out.pending w = none := by
    rw [hout]
    change last.1.pending w = none
    rw [hh.frame.pending]
    have h := hpend w
    have hm : w ∈ List.finRange m := by simp
    rw [ite_eq_left hm] at h
    exact h
  change RoundInfo out start B move ∧ Extends s.outer.trace out.trace ∧
    out.completed = s.outer.completed ∧ out.trace.markers = s.outer.trace.markers
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, (frame_extends hf).trans hh.frame.trace,
    hh.frame.completed.trans hf.completed, hh.frame.markers.trans hf.markers⟩
  · rw [hout]
    exact hh.ready.represented
  · rw [hout]
    exact hh.ready.legal
  · rw [hout]
    exact hh.ready.retired
  · have hstate := hh.frame.trace
    have hbase : out.base = closed.base := by rw [hout]; exact hh.frame.base
    have hmarkers : out.trace.markers = closed.trace.markers := by rw [hout]; exact hh.frame.markers
    have hcount : out.trace.nextDirection = closed.trace.nextDirection := by rw [hout]; exact hh.frame.directionCount
    have hcomplete : out.completed = closed.completed := by rw [hout]; exact hh.frame.completed
    refine ⟨?_, ?_, ?_, ?_, hb, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcount, hcomplete]
      exact ht.count
    · rw [hbase]
      exact ht.baseBound.trans_le hstate.stateCount
    · rw [hmarkers, hbase]
      exact ht.baseMarker
    · rw [hbase, hout]
      change (last.1.trace.states closed.base).history = _
      rw [hstate.oldState _ ht.baseBound]
      exact ht.baseHistory
    · intro i d hd
      exact (hmem i d).2 ⟨.inl i, rfl, ht.nodePrefix (.inl i) hd⟩
    · intro i d hd
      rw [hcount]
      obtain ⟨a, _, ha⟩ := (hmem i d).1 hd
      exact ht.nodePast a ha
    · intro i j hij
      ext d
      rw [mem_inter, hmem i d, hmem j d]
      constructor
      · rintro ⟨⟨a, ha, hd₁⟩, ⟨b, hb, hd₂⟩⟩
        have hne : color layout a ≠ color layout b := fun he => hij (ha.symm.trans (he.trans hb))
        rw [← ht.outside a b hne]
        exact mem_inter.mpr ⟨hd₁, hd₂⟩
      · intro h
        exact ⟨⟨.inl i, rfl, ht.nodePrefix (.inl i) h⟩,
          ⟨.inl j, rfl, ht.nodePrefix (.inl j) h⟩⟩
    · intro d hd
      rw [hcount] at hd
      rcases ht.covered d hd with h | ⟨g, hg⟩
      · exact Or.inl h
      · exact Or.inr ⟨layout.cluster g, (hmem _ d).2 ⟨.inr g, rfl, hg⟩⟩
    · intro n hlo hhi
      rw [hcount] at hhi
      rw [hout]
      change Finset.range start ⊆ (last.1.trace.directions n).history ∧
        (last.1.trace.directions n).history ⊆ Finset.range n ∧
        (last.1.trace.directions n).refresh = 1 ∧ (last.1.trace.directions n).movement = move ∧
        (last.1.trace.directions n).raw.length = B
      rw [hh.frame.directions]
      exact ht.direction n hlo hhi
  · intro w j hj
    rw [hp w] at hj
    contradiction
  · intro w v j k hj hk hne
    rw [hp w] at hj
    contradiction

end LongTails.Proofs.BirchCollectionNestedExport
