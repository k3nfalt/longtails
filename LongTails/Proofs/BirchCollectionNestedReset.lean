import LongTails.Proofs.BirchCollectionNestedCollect

namespace LongTails.Proofs.BirchCollectionNestedReset

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionGroupReady
open LongTails.Proofs.BirchCollectionNestedShape
open LongTails.Proofs.BirchCollectionNestedCollect

def resetCluster {m : ℕ} (layout : Layout m) (s : State m) (i : Fin m)
    (collected : Round m × ℕ) : State m :=
  { outer := {collected.1 with head := fun g => if layout.cluster g = i then collected.2 else collected.1.head g}
    cluster := Function.update s.cluster i ⟨collected.2, 0⟩ }

lemma cluster_member {m : ℕ} (layout : Layout m) (i g : Fin m) :
    g ∈ groups layout i ↔ layout.cluster g = i := by simp [groups]

lemma worker_member {m : ℕ} (layout : Layout m) (i w : Fin m) :
    w ∈ workers layout i ↔ layout.cluster (layout.group w) = i := by simp [workers]

lemma collected_cross {m start B : ℕ} {move : ℝ} {layout : Layout m} {s : State m} {i : Fin m}
    {pair : Round m × ℕ} (hs : Shape layout s start B move)
    (hc : Collected layout s i pair (groups layout i) start B move)
    (a : Node m) (ha : color layout a ≠ i) :
    (pair.1.trace.states pair.2).history ∩ hist s a = range start := by
  ext d
  rw [mem_inter, hc.history d]
  constructor
  · rintro ⟨h | ⟨g, hg, h⟩, hda⟩
    · rw [← hs.outside (.inl i) a (Ne.symm ha)]
      exact mem_inter.mpr ⟨h, hda⟩
    · have hcol : color layout (.inr g) = i := (cluster_member layout i g).1 hg
      rw [← hs.outside (.inr g) a (fun he => ha (he.symm.trans hcol))]
      exact mem_inter.mpr ⟨h, hda⟩
  · intro h
    exact ⟨Or.inl (hs.nodePrefix (.inl i) h), hs.nodePrefix a h⟩

lemma reset_shape {m start B : ℕ} {move : ℝ} {layout : Layout m} {s : State m} {i : Fin m}
    {pair : Round m × ℕ} (hs : Shape layout s start B move)
    (hc : Collected layout s i pair (groups layout i) start B move) :
    Shape layout (resetCluster layout s i pair) start B move := by
  let t := resetCluster layout s i pair
  let H := (pair.1.trace.states pair.2).history
  have hp (a : Node m) : point t a = if color layout a = i then pair.2 else point s a := by
    cases a with
    | inl j =>
      change (Function.update s.cluster i ⟨pair.2, 0⟩ j).point =
        if j = i then pair.2 else (s.cluster j).point
      by_cases h : j = i
      · subst j
        simp
      · simp [h]
    | inr g =>
      change (if layout.cluster g = i then pair.2 else pair.1.head g) =
        if layout.cluster g = i then pair.2 else s.outer.head g
      rw [hc.frame.head]
  have ht (a : Node m) : hist t a = if color layout a = i then H else hist s a := by
    unfold hist
    rw [hp a]
    by_cases h : color layout a = i
    · simp [h, H, t, resetCluster]
    · simp only [ite_eq_right h]
      exact congrArg StateRecord.history (hc.frame.trace.oldState _ (hs.nodeBound a))
  have hprefix : range start ⊆ H := fun d hd => (hc.history d).2 (Or.inl (hs.nodePrefix (.inl i) hd))
  have hpast : H ⊆ range s.outer.trace.nextDirection := by
    intro d hd
    rcases (hc.history d).1 hd with hd | ⟨g, _, hd⟩
    · exact hs.nodePast (.inl i) hd
    · exact hs.nodePast (.inr g) hd
  have hmono (g : Fin m) : hist s (.inr g) ⊆ hist t (.inr g) := by
    rw [ht]
    change hist s (.inr g) ⊆ if layout.cluster g = i then H else hist s (.inr g)
    by_cases h : layout.cluster g = i
    · rw [ite_eq_left h]
      intro d hd
      exact (hc.history d).2 (Or.inr ⟨g, (cluster_member layout i g).2 h, hd⟩)
    · rw [ite_eq_right h]
  have hframe := hc.frame
  change Shape layout t start B move
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change pair.1.trace.nextDirection = start + pair.1.completed
    rw [hframe.directionCount, hframe.completed]
    exact hs.count
  · change pair.1.base < pair.1.trace.nextState
    rw [hframe.base]
    exact hs.baseBound.trans_le hframe.trace.stateCount
  · change pair.1.trace.markers.getLast?.getD 0 = pair.1.base
    rw [hframe.markers, hframe.base]
    exact hs.baseMarker
  · change (pair.1.trace.states pair.1.base).history = range start
    rw [hframe.base, hframe.trace.oldState _ hs.baseBound]
    exact hs.baseHistory
  · intro a
    rw [hp]
    by_cases h : color layout a = i
    · rw [ite_eq_left h]
      exact hc.head
    · rw [ite_eq_right h]
      exact (hs.nodeBound a).trans_le hframe.trace.stateCount
  · intro a
    rw [ht]
    by_cases h : color layout a = i
    · rwa [ite_eq_left h]
    · rw [ite_eq_right h]
      exact hs.nodePrefix a
  · intro a
    change hist t a ⊆ range pair.1.trace.nextDirection
    rw [ht, hframe.directionCount]
    by_cases h : color layout a = i
    · rwa [ite_eq_left h]
    · rw [ite_eq_right h]
      exact hs.nodePast a
  · intro g
    rw [ht (.inl _), ht (.inr _)]
    by_cases h : layout.cluster g = i
    · simp [color, h]
    · simpa [color, h] using hs.common g
  · intro a b hab
    rw [ht a, ht b]
    by_cases ha : color layout a = i
    · have hb : color layout b ≠ i := fun hb => hab (ha.trans hb.symm)
      rw [ite_eq_left ha, ite_eq_right hb]
      exact collected_cross hs hc b hb
    · by_cases hb : color layout b = i
      · rw [ite_eq_right ha, ite_eq_left hb, inter_comm]
        exact collected_cross hs hc a ha
      · rw [ite_eq_right ha, ite_eq_right hb]
        exact hs.outside a b hab
  · intro g j hne he
    rw [ht (.inr g), ht (.inr j), ht (.inl _)]
    by_cases h : layout.cluster g = i
    · simp [color, h, he.symm]
    · simpa [color, h, he.symm] using hs.inside g j hne he
  · intro d hd
    change d ∈ range pair.1.trace.nextDirection at hd
    rw [hframe.directionCount] at hd
    rcases hs.covered d hd with hb | ⟨g, hg⟩
    · exact Or.inl hb
    · exact Or.inr ⟨g, hmono g hg⟩
  · intro n hn hlt
    change n < pair.1.trace.nextDirection at hlt
    rw [hframe.directionCount] at hlt
    simpa only [t, resetCluster, hframe.directions] using hs.direction n hn hlt

end LongTails.Proofs.BirchCollectionNestedReset
