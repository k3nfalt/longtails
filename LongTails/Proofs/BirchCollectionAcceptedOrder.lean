import LongTails.Proofs.BirchCollectionScaledReset

namespace LongTails.Proofs.BirchCollectionAcceptedOrder

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionOrdering

def labelPrefix (o : LongTails.Setups.BirchCollections.Ordering) (n : ℕ) : Finset ℕ :=
  (o.labels.take n).toFinset

lemma mem_labelPrefix (o : LongTails.Setups.BirchCollections.Ordering) (n q : ℕ) :
    q ∈ labelPrefix o n ↔ ∃ j < n, j < o.labels.length ∧ o.label j = q := by
  simp only [labelPrefix, List.mem_toFinset, List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    have hlt : j < n := by
      by_contra hn
      rw [List.getElem?_take_eq_none (Nat.le_of_not_gt hn)] at hj
      contradiction
    rw [List.getElem?_take, ite_eq_left hlt] at hj
    have hlen := List.getElem?_eq_some_iff.mp hj
    refine ⟨j, hlt, hlen.1, ?_⟩
    simp [Ordering.label, hj]
  · rintro ⟨j, hj, hlen, hq⟩
    refine ⟨j, ?_⟩
    rw [List.getElem?_take, ite_eq_left hj, List.getElem?_eq_getElem hlen,
      ← label_eq_getElem o j hlen, hq]

lemma labelPrefix_image (o : LongTails.Setups.BirchCollections.Ordering) (n : ℕ)
    (hn : n ≤ o.labels.length) : labelPrefix o n = (range n).image o.label := by
  ext q
  rw [mem_labelPrefix, mem_image]
  constructor
  · rintro ⟨j, hj, _, he⟩
    exact ⟨j, mem_range.mpr hj, he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, mem_range.mp hj, (mem_range.mp hj).trans_le hn, he⟩

lemma labelPrefix_included (o : LongTails.Setups.BirchCollections.Ordering)
    (s : TraceState) (n f : ℕ) (hn : n < o.labels.length) (hf : f ≤ n)
    (hp : labelPrefix o f ⊆ (s.directions (o.label n)).history) :
    range f ⊆ o.history s n := by
  intro j hj
  have hjf := mem_range.mp hj
  have hjl := (hjf.trans_le hf).trans hn
  exact (ordering_history_mem s o n j hn).2 ⟨hjl,
    hp ((mem_labelPrefix o f (o.label j)).2 ⟨j, hjf, hjl, rfl⟩)⟩

lemma history_before (o : LongTails.Setups.BirchCollections.Ordering)
    (s : TraceState) (n : ℕ) (hn : n < o.labels.length) (hd : o.labels.Nodup)
    (hp : (s.directions (o.label n)).history ⊆ labelPrefix o n) :
    o.history s n ⊆ range n := by
  intro j hj
  obtain ⟨hjl, hjp⟩ := (ordering_history_mem s o n j hn).1 hj
  obtain ⟨i, hi, hil, he⟩ := (mem_labelPrefix o n (o.label j)).1 (hp hjp)
  have h := label_injective o hd hil hjl he
  subst j
  exact mem_range.mpr hi

structure LogData (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K window : ℕ) :
    Prop where
  nonempty : 0 < o.labels.length
  distinct : o.labels.Nodup
  markers : s.markers.length = K + 1
  cut_zero : o.cut 0 = 0
  cut_end : o.cut K = o.labels.length
  cut_step : ∀ k < K, o.cut k < o.cut (k + 1)
  cut_bound : ∀ k ≤ K, o.cut k ≤ o.labels.length
  labels : ∀ n < o.labels.length, o.label n < s.nextDirection
  marker_data : ∀ k ≤ K, (s.states (s.markers[k]?.getD 0)).history = labelPrefix o (o.cut k)
  before : ∀ n < o.labels.length, (s.directions (o.label n)).history ⊆ labelPrefix o n
  frontier_data : ∀ n < o.labels.length, o.frontier n ≤ n ∧ n - o.frontier n ≤ window ∧
    labelPrefix o (o.frontier n) ⊆ (s.directions (o.label n)).history

lemma LogData.valid {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K window : ℕ}
    (h : LogData s o K window) : o.Valid s K := by
  refine ⟨h.nonempty, h.distinct, h.markers, h.cut_zero, h.cut_end, h.cut_step, h.labels, ?_, ?_⟩
  · intro k hk
    rw [h.marker_data k hk, labelPrefix_image o _ (h.cut_bound k hk)]
  · intro n
    by_cases hn : n < o.labels.length
    · exact history_before o s n hn h.distinct (h.before n hn)
    · rw [Ordering.history, ite_eq_right hn]

lemma LogData.frontier {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K window : ℕ}
    (h : LogData s o K window) (n : ℕ) (hn : n < o.labels.length) :
    o.frontier n ≤ n ∧ n - o.frontier n ≤ window ∧ range (o.frontier n) ⊆ o.history s n := by
  obtain ⟨h₁, h₂, h₃⟩ := h.frontier_data n hn
  exact ⟨h₁, h₂, labelPrefix_included o s n _ hn h₁ h₃⟩

end LongTails.Proofs.BirchCollectionAcceptedOrder
