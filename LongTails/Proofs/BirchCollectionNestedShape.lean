import LongTails.Algorithms.BirchCollectionNested
import LongTails.Proofs.BirchCollectionGroupReady

namespace LongTails.Proofs.BirchCollectionNestedShape

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested
open LongTails.Proofs.BirchCollectionGroupReady
open LongTails.Proofs.BirchCollectionLocalTrace (ForestStep)

abbrev Node (m : ℕ) := Sum (Fin m) (Fin m)

def color {m : ℕ} (layout : Layout m) : Node m → Fin m
  | .inl c => c
  | .inr g => layout.cluster g

def point {m : ℕ} (s : State m) : Node m → ℕ
  | .inl c => (s.cluster c).point
  | .inr g => s.outer.head g

def hist {m : ℕ} (s : State m) (a : Node m) : Finset ℕ :=
  (s.outer.trace.states (point s a)).history

structure Shape {m : ℕ} (layout : Layout m) (s : State m) (start B : ℕ) (move : ℝ) : Prop where
  count : s.outer.trace.nextDirection = start + s.outer.completed
  baseBound : s.outer.base < s.outer.trace.nextState
  baseMarker : s.outer.trace.markers.getLast?.getD 0 = s.outer.base
  baseHistory : (s.outer.trace.states s.outer.base).history = range start
  nodeBound : ∀ a, point s a < s.outer.trace.nextState
  nodePrefix : ∀ a, range start ⊆ hist s a
  nodePast : ∀ a, hist s a ⊆ range s.outer.trace.nextDirection
  common : ∀ g, hist s (.inl (layout.cluster g)) ⊆ hist s (.inr g)
  outside : ∀ a b, color layout a ≠ color layout b → hist s a ∩ hist s b = range start
  inside : ∀ g h, g ≠ h → layout.cluster g = layout.cluster h →
    hist s (.inr g) ∩ hist s (.inr h) = hist s (.inl (layout.cluster g))
  covered : ∀ d ∈ range s.outer.trace.nextDirection, d ∈ range start ∨ ∃ g, d ∈ hist s (.inr g)
  direction : ∀ n, start ≤ n → n < s.outer.trace.nextDirection →
    range start ⊆ (s.outer.trace.directions n).history ∧
      (s.outer.trace.directions n).history ⊆ range n ∧ (s.outer.trace.directions n).refresh = 1 ∧
      (s.outer.trace.directions n).movement = move ∧ (s.outer.trace.directions n).raw.length = B

lemma Shape.heads {m start B : ℕ} {move : ℝ} {layout : Layout m} {s : State m}
    (h : Shape layout s start B move) : Heads s.outer start :=
  ⟨fun g => h.nodeBound (.inr g), fun g => h.nodePrefix (.inr g), fun g => h.nodePast (.inr g)⟩

lemma shape_initial {m start B : ℕ} {move : ℝ} (layout : Layout m) (trace : TraceState)
    (events : List Event)
    (hc : trace.nextDirection = start)
    (hb : trace.markers.getLast?.getD 0 < trace.nextState)
    (hh : (trace.states (trace.markers.getLast?.getD 0)).history = range start) :
    Shape layout ⟨Round.initial m trace events, fun _ => ⟨trace.markers.getLast?.getD 0, 0⟩⟩
      start B move := by
  let s : State m := ⟨Round.initial m trace events, fun _ => ⟨trace.markers.getLast?.getD 0, 0⟩⟩
  have hp (a : Node m) : point s a = trace.markers.getLast?.getD 0 := by cases a <;> rfl
  have h (a : Node m) : hist s a = range start := by
    unfold hist
    rw [hp]
    exact hh
  change Shape layout s start B move
  refine ⟨by simpa [s, Round.initial] using hc, hb, rfl, hh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hp]
    exact hb
  · intro a
    rw [h]
  · intro a
    rw [h]
    change range start ⊆ range trace.nextDirection
    rw [hc]
  · intro g
    rw [h, h]
  · intro a b _
    rw [h, h, inter_self]
  · intro g j _ _
    rw [h, h, h, inter_self]
  · intro d hd
    change d ∈ range trace.nextDirection at hd
    exact Or.inl (hc ▸ hd)
  · intro n hlo hhi
    change n < trace.nextDirection at hhi
    rw [hc] at hhi
    exact (not_lt_of_ge hlo hhi).elim

lemma shape_frame {m start B : ℕ} {move : ℝ} {layout : Layout m} {s t : State m}
    (hs : Shape layout s start B move) (hf : CaptureFrame s.outer t.outer)
    (hcluster : ∀ c, (t.cluster c).point = (s.cluster c).point) : Shape layout t start B move := by
  have hp (a : Node m) : point t a = point s a := by
    cases a with
    | inl c => exact hcluster c
    | inr g => exact congrFun hf.heads g
  have h (a : Node m) : hist t a = hist s a := by
    unfold hist
    rw [hp, hf.states]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.directionCount, hf.completed]
    exact hs.count
  · rw [hf.base, hf.stateCount]
    exact hs.baseBound
  · rw [hf.markers, hf.base]
    exact hs.baseMarker
  · rw [hf.states, hf.base]
    exact hs.baseHistory
  · intro a
    rw [hp, hf.stateCount]
    exact hs.nodeBound a
  · intro a
    rw [h]
    exact hs.nodePrefix a
  · intro a
    rw [h, hf.directionCount]
    exact hs.nodePast a
  · intro g
    rw [h, h]
    exact hs.common g
  · intro a b hab
    rw [h, h]
    exact hs.outside a b hab
  · intro g j hne he
    rw [h, h, h]
    exact hs.inside g j hne he
  · intro d hd
    rw [hf.directionCount] at hd
    rcases hs.covered d hd with hbase | ⟨g, hg⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨g, h (.inr g) ▸ hg⟩
  · rw [hf.directions, hf.directionCount]
    exact hs.direction

lemma shape_reply {m start B : ℕ} {move : ℝ} {layout : Layout m} {s t : State m}
    (g : Fin m) (hs : Shape layout s start B move) (hf : ForestStep s.outer t.outer g start B move)
    (hcluster : ∀ c, (t.cluster c).point = (s.cluster c).point) : Shape layout t start B move := by
  let n := s.outer.trace.nextDirection
  have hnew : hist t (.inr g) = insert n (hist s (.inr g)) := hf.newHistory
  have hpoint (a : Node m) (ha : a ≠ .inr g) : point t a = point s a := by
    cases a with
    | inl c => exact hcluster c
    | inr w => exact hf.otherHead w (fun h => ha (congrArg Sum.inr h))
  have hold (a : Node m) (ha : a ≠ .inr g) : hist t a = hist s a := by
    unfold hist
    rw [hpoint a ha, hf.oldState _ (hs.nodeBound a)]
  have hnot (a : Node m) : n ∉ hist s a := fun h =>
    Nat.lt_irrefl n (mem_range.mp (hs.nodePast a h))
  have hmono (a : Node m) : hist s a ⊆ hist t a := by
    by_cases ha : a = .inr g
    · rw [ha, hnew]
      exact subset_insert _ _
    · rw [hold a ha]
  have hinter (a b : Node m) (hne : a ≠ b) : hist t a ∩ hist t b = hist s a ∩ hist s b := by
    by_cases ha : a = .inr g
    · rw [ha, hnew, hold b (fun hb => hne (ha.trans hb.symm))]
      ext d
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hd, hb⟩
        · exact (hnot b hb).elim
        · exact ⟨hd, hb⟩
      · rintro ⟨hd, hb⟩
        exact ⟨Or.inr hd, hb⟩
    · rw [hold a ha]
      by_cases hb : b = .inr g
      · rw [hb, hnew]
        ext d
        simp only [mem_inter, mem_insert]
        constructor
        · rintro ⟨hd, rfl | hb'⟩
          · exact (hnot a hd).elim
          · exact ⟨hd, hb'⟩
        · rintro ⟨hd, hb'⟩
          exact ⟨hd, Or.inr hb'⟩
      · rw [hold b hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => (hs.nodePrefix a).trans (hmono a),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.nextDirection, hs.count, hf.completed, Nat.add_assoc]
  · rw [hf.base]
    exact hs.baseBound.trans_le hf.stateCount
  · rw [hf.markers, hf.base]
    exact hs.baseMarker
  · rw [hf.base, hf.oldState _ hs.baseBound]
    exact hs.baseHistory
  · intro a
    by_cases ha : a = .inr g
    · rw [ha]
      exact hf.headBound
    · rw [hpoint a ha]
      exact (hs.nodeBound a).trans_le hf.stateCount
  · intro a
    rw [hf.nextDirection]
    by_cases ha : a = .inr g
    · rw [ha, hnew]
      exact insert_subset (mem_range.mpr (Nat.lt_succ_self _))
        ((hs.nodePast (.inr g)).trans (range_mono (Nat.le_succ _)))
    · rw [hold a ha]
      exact (hs.nodePast a).trans (range_mono (Nat.le_succ _))
  · intro w
    rw [hold (.inl _) (by simp)]
    exact (hs.common w).trans (hmono (.inr w))
  · intro a b hab
    rw [hinter a b (fun he => hab (congrArg (color layout) he))]
    exact hs.outside a b hab
  · intro v w hne hcolor
    rw [hinter (.inr v) (.inr w) (by simpa using hne), hold (.inl _) (by simp)]
    exact hs.inside v w hne hcolor
  · intro d hd
    rw [hf.nextDirection] at hd
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ (mem_range.mp hd)) with rfl | hlt
    · exact Or.inr ⟨g, by rw [hnew]; exact mem_insert_self _ _⟩
    · rcases hs.covered d (mem_range.mpr hlt) with hb | ⟨v, hv⟩
      · exact Or.inl hb
      · exact Or.inr ⟨v, hmono (.inr v) hv⟩
  · intro d hd hlt
    rw [hf.nextDirection] at hlt
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
    · exact hf.newDirection
    · rw [hf.oldDirection _ hlt']
      exact hs.direction d hd hlt'

lemma shape_extend {m start B : ℕ} {move : ℝ} {layout : Layout m} {s t : State m}
    (hs : Shape layout s start B move)
    (he : LongTails.Proofs.BirchCollectionPublication.Extends s.outer.trace t.outer.trace)
    (hb : t.outer.base = s.outer.base) (hp : ∀ a, point t a = point s a)
    (hcompleted : t.outer.completed = s.outer.completed)
    (hcount : t.outer.trace.nextDirection = s.outer.trace.nextDirection)
    (hdirs : t.outer.trace.directions = s.outer.trace.directions)
    (hmark : t.outer.trace.markers = s.outer.trace.markers) :
    Shape layout t start B move := by
  have hh (a : Node m) : hist t a = hist s a := by
    unfold hist
    rw [hp a, he.oldState _ (hs.nodeBound a)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcount, hcompleted]
    exact hs.count
  · rw [hb]
    exact hs.baseBound.trans_le he.stateCount
  · rw [hmark, hb]
    exact hs.baseMarker
  · rw [hb, he.oldState _ hs.baseBound]
    exact hs.baseHistory
  · intro a
    rw [hp]
    exact (hs.nodeBound a).trans_le he.stateCount
  · intro a
    rw [hh]
    exact hs.nodePrefix a
  · intro a
    rw [hh, hcount]
    exact hs.nodePast a
  · intro g
    rw [hh, hh]
    exact hs.common g
  · intro a b h
    rw [hh, hh]
    exact hs.outside a b h
  · intro g j hne hi
    rw [hh, hh, hh]
    exact hs.inside g j hne hi
  · intro d hd
    rw [hcount] at hd
    rcases hs.covered d hd with hp | ⟨g, hg⟩
    · exact Or.inl hp
    · exact Or.inr ⟨g, hh (.inr g) ▸ hg⟩
  · rw [hdirs, hcount]
    exact hs.direction

end LongTails.Proofs.BirchCollectionNestedShape
