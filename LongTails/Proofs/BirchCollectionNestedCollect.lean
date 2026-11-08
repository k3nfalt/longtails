import LongTails.Proofs.BirchCollectionNestedShape

namespace LongTails.Proofs.BirchCollectionNestedCollect

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionGroupReady
open LongTails.Proofs.BirchCollectionNestedShape
open LongTails.Proofs.BirchCollectionPublication

structure MergeFrame {m : ℕ} (s t : Round m) : Prop where
  trace : Extends s.trace t.trace
  base : t.base = s.base
  head : t.head = s.head
  completed : t.completed = s.completed
  directionCount : t.trace.nextDirection = s.trace.nextDirection
  directions : t.trace.directions = s.trace.directions
  markers : t.trace.markers = s.trace.markers
  pending : t.pending = s.pending

lemma MergeFrame.refl {m : ℕ} (s : Round m) : MergeFrame s s :=
  ⟨extends_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma MergeFrame.trans {m : ℕ} {s t u : Round m} (h : MergeFrame s t) (h' : MergeFrame t u) :
    MergeFrame s u :=
  ⟨h.trace.trans h'.trace, h'.base.trans h.base, h'.head.trans h.head,
    h'.completed.trans h.completed, h'.directionCount.trans h.directionCount,
    h'.directions.trans h.directions, h'.markers.trans h.markers, h'.pending.trans h.pending⟩

lemma MergeFrame.step {m : ℕ} (s : Round m) (owner left right base : ℕ) :
    MergeFrame s (s.append [.merge owner left right base]) :=
  ⟨extends_step s.trace (.merge owner left right base), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma MergeFrame.shape {m start B : ℕ} {layout : Layout m} {s : State m} {t : Round m} {move : ℝ}
    (hs : Shape layout s start B move) (h : MergeFrame s.outer t) :
    Shape layout {s with outer := t} start B move :=
  shape_extend hs h.trace h.base (fun a => by cases a with
    | inl c => rfl
    | inr g => exact congrFun h.head g) h.completed h.directionCount h.directions h.markers

def select {m : ℕ} (s : State m) (i : Fin m) (t : Round m × ℕ) (g : Fin m) : Round m × ℕ :=
  (t.1.append [.merge (i.val + 1) t.2 (s.outer.head g) (s.cluster i).point], t.1.trace.nextState)

structure Collected {m : ℕ} (layout : Layout m) (s : State m) (i : Fin m)
    (t : Round m × ℕ) (seen : List (Fin m)) (start B : ℕ) (move : ℝ) : Prop where
  frame : MergeFrame s.outer t.1
  ready : Ready layout.group t.1 start B move
  head : t.2 < t.1.trace.nextState
  history : ∀ d, d ∈ (t.1.trace.states t.2).history ↔
    d ∈ hist s (.inl i) ∨ ∃ g ∈ seen, d ∈ hist s (.inr g)

lemma collect_step {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (i : Fin m)
    (t : Round m × ℕ) (seen : List (Fin m)) (g : Fin m)
    (hs : Shape layout s start B move) (ht : Collected layout s i t seen start B move)
    (hseen : ∀ u ∈ seen, layout.cluster u = i) (hg : layout.cluster g = i) (hne : g ∉ seen) :
    Collected layout s i (select s i t g) (seen ++ [g]) start B move := by
  let right := s.outer.head g
  let base := (s.cluster i).point
  let e := Event.merge (i.val + 1) t.2 right base
  have hr : right < t.1.trace.nextState := (hs.nodeBound (.inr g)).trans_le ht.frame.trace.stateCount
  have hb : base < t.1.trace.nextState := (hs.nodeBound (.inl i)).trans_le ht.frame.trace.stateCount
  have hright : (t.1.trace.states right).history = hist s (.inr g) :=
    congrArg StateRecord.history (ht.frame.trace.oldState _ (hs.nodeBound (.inr g)))
  have hbase : (t.1.trace.states base).history = hist s (.inl i) :=
    congrArg StateRecord.history (ht.frame.trace.oldState _ (hs.nodeBound (.inl i)))
  have he : e.Valid (m + 1) t.1.trace := by
    refine ⟨Nat.succ_lt_succ i.isLt, ht.head, hr, hb, ?_⟩
    rw [hbase, hright]
    ext d
    rw [mem_inter, ht.history d]
    constructor
    · intro h
      exact ⟨Or.inl h, hs.common g (hg.symm ▸ h)⟩
    · rintro ⟨hb | ⟨u, hu, hd⟩, hg'⟩
      · exact hb
      · have hu' := hseen u hu
        have hne' : u ≠ g := fun h => hne (h ▸ hu)
        rw [← hu', ← hs.inside u g hne' (hu'.trans hg.symm)]
        exact mem_inter.mpr ⟨hd, hg'⟩
  have hs' := ht.frame.shape hs
  refine ⟨ht.frame.trans (MergeFrame.step _ _ _ _ _), ready_merge _ _ _ _ _ ht.ready hs'.heads he,
    Nat.lt_succ_self _, ?_⟩
  intro d
  change d ∈ ((step t.1.trace e).states t.1.trace.nextState).history ↔ _
  rw [(merge_data t.1.trace (i.val + 1) t.2 right base).newState]
  simp only [mem_union, ht.history, hright]
  constructor
  · rintro ((h | ⟨u, hu, hd⟩) | hg')
    · exact Or.inl h
    · exact Or.inr ⟨u, List.mem_append.mpr (Or.inl hu), hd⟩
    · exact Or.inr ⟨g, by simp, hg'⟩
  · rintro (hb' | ⟨u, hu, hd⟩)
    · exact Or.inl (Or.inl hb')
    · rcases List.mem_append.mp hu with hu | hu
      · exact Or.inl (Or.inr ⟨u, hu, hd⟩)
      · have he : u = g := by simpa using hu
        exact Or.inr (he ▸ hd)

lemma collect_fold {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (i : Fin m)
    (t : Round m × ℕ) (seen gs : List (Fin m)) (hs : Shape layout s start B move)
    (ht : Collected layout s i t seen start B move)
    (hseen : ∀ u ∈ seen, layout.cluster u = i) (hgs : ∀ u ∈ gs, layout.cluster u = i)
    (hn : gs.Nodup) (hne : ∀ u ∈ gs, u ∉ seen) :
    Collected layout s i (gs.foldl (select s i) t) (seen ++ gs) start B move := by
  induction gs generalizing t seen with
  | nil => simpa only [List.foldl_nil, List.append_nil] using ht
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have ht' := collect_step layout s i t seen g hs ht hseen hg (hne g (by simp))
    have hs' (u : Fin m) (hu : u ∈ seen ++ [g]) : layout.cluster u = i := by
      rcases List.mem_append.mp hu with hu | hu
      · exact hseen u hu
      · have h : u = g := by simpa using hu
        simpa [h] using hg
    have hsep (u : Fin m) (hu : u ∈ gs) : u ∉ seen ++ [g] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · exact hne u (List.mem_cons_of_mem _ hu) h
      · have he : u = g := by simpa using h
        exact (List.nodup_cons.mp hn).1 (he ▸ hu)
    have h := ih (select s i t g) (seen ++ [g]) ht' hs'
      (fun u hu => hgs u (List.mem_cons_of_mem _ hu)) (List.nodup_cons.mp hn).2 hsep
    simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using h

lemma collect_data {m start B : ℕ} {move : ℝ} (layout : Layout m) (s : State m) (i : Fin m)
    (hs : Shape layout s start B move) (hr : Ready layout.group s.outer start B move) :
    Collected layout s i (collectCluster layout s.outer i (s.cluster i).point) (groups layout i)
      start B move := by
  have h : Collected layout s i (s.outer, (s.cluster i).point) [] start B move := by
    refine ⟨MergeFrame.refl _, hr, hs.nodeBound (.inl i), ?_⟩
    intro d
    simp [hist, point]
  have hu := collect_fold layout s i (s.outer, (s.cluster i).point) [] (groups layout i) hs h
    (by simp) (by simp [groups]) ((List.nodup_finRange m).filter _) (by simp)
  simp only [List.nil_append] at hu
  exact hu

end LongTails.Proofs.BirchCollectionNestedCollect
