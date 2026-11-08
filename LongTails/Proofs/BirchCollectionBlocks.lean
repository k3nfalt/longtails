import LongTails.Proofs.BirchCollectionWeights
import LongTails.Proofs.BirchRetainedEnergy

namespace LongTails.Proofs.BirchCollectionBlocks

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionSampling (CollectionOrdering)
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionWeights
open LongTails.Proofs.BirchRetainedTransport
open LongTails.Proofs.BirchCausalTransport (transportMass transportMass_bounds)

lemma cut_mono (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ K) : o.cut i ≤ o.cut j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
      exact (ih (by omega)).trans (ho.2.2.2.2.2.1 j (by omega)).le

lemma interval_exists (cut : ℕ → ℕ) (hzero : cut 0 = 0) (K n : ℕ)
    (hn : n < cut K) : ∃ k, k < K ∧ cut k ≤ n ∧ n < cut (k + 1) := by
  induction K with
  | zero => simp [hzero] at hn
  | succ K ih =>
      by_cases h : n < cut K
      · obtain ⟨k, hk, hlo, hhi⟩ := ih h
        exact ⟨k, by omega, hlo, hhi⟩
      · exact ⟨K, by omega, by omega, hn⟩

noncomputable def owner (o : CollectionOrdering) (K n : ℕ) : ℕ :=
  if h : ∃ k, k < K ∧ o.cut k ≤ n ∧ n < o.cut (k + 1) then Classical.choose h else 0

lemma owner_bounds (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (n : ℕ) (hn : n < o.labels.length) :
    owner o K n < K ∧ o.cut (owner o K n) ≤ n ∧ n < o.cut (owner o K n + 1) := by
  have h : ∃ k, k < K ∧ o.cut k ≤ n ∧ n < o.cut (k + 1) :=
    interval_exists o.cut ho.2.2.2.1 K n (by simpa only [ho.2.2.2.2.1] using hn)
  simp only [owner, dite_eq_left h]
  exact Classical.choose_spec h

lemma interval_unique (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (n i j : ℕ) (hi : i < K) (hj : j < K)
    (hilo : o.cut i ≤ n) (hihi : n < o.cut (i + 1))
    (hjlo : o.cut j ≤ n) (hjhi : n < o.cut (j + 1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := cut_mono s o K ho (i + 1) j (by omega) hj.le
    omega
  · exact h
  · have := cut_mono s o K ho (j + 1) i (by omega) hi.le
    omega

lemma owner_eq_iff (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (n k : ℕ) (hn : n < o.labels.length) (hk : k < K) :
    owner o K n = k ↔ n ∈ Ico (o.cut k) (o.cut (k + 1)) := by
  have hb := owner_bounds s o K ho n hn
  constructor
  · intro he
    simpa only [he, mem_Ico] using hb.2
  · intro h
    exact interval_unique s o K ho n _ k hb.1 hk hb.2.1 hb.2.2
      (mem_Ico.mp h).1 (mem_Ico.mp h).2

lemma owner_filter (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (k : ℕ) (hk : k < K) :
    (range o.labels.length).filter (fun n => owner o K n = k) =
      Ico (o.cut k) (o.cut (k + 1)) := by
  ext n
  constructor
  · intro hn
    exact (owner_eq_iff s o K ho n k (mem_range.mp (mem_filter.mp hn).1) hk).mp
      (mem_filter.mp hn).2
  · intro hn
    have hhi := cut_mono s o K ho (k + 1) K (by omega) le_rfl
    rw [ho.2.2.2.2.1] at hhi
    have hnN := (mem_Ico.mp hn).2.trans_le hhi
    exact mem_filter.mpr ⟨mem_range.mpr hnN, (owner_eq_iff s o K ho n k hnN hk).mpr hn⟩

noncomputable def start (o : CollectionOrdering) (K n : ℕ) : ℕ :=
  if n < o.labels.length then o.cut (owner o K n) else n

def frontier (o : CollectionOrdering) (n : ℕ) : ℕ :=
  if n < o.labels.length then o.frontier n else n

noncomputable def mass (s : TraceState) (o : CollectionOrdering) (k : ℕ) : ℝ :=
  ∑ n ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s n

lemma start_le (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (n : ℕ) : start o K n ≤ n := by
  by_cases hn : n < o.labels.length
  · simpa only [start, hn, ite_true] using (owner_bounds s o K ho n hn).2.1
  · simp [start, hn]

lemma main_window (s : TraceState) (o : CollectionOrdering) (c : Controls) (K B : ℕ)
    (hp : CollectionParameters s) (hc : CompletedLedger s) (hs : Structural s o c K B)
    (n : ℕ) (hn : n < o.labels.length) :
    work (o.movement s) n - work (o.movement s) (start o K n) ≤ c.upperMass := by
  have hb := owner_bounds s o K hs.1 n hn
  have hw := ordering_parameters s o K hp hc hs.1
  simp only [start, hn, ite_true]
  rw [← work_interval _ _ _ hb.2.1]
  apply le_trans _ (hs.2.2.2.2.2.1 _ hb.1)
  exact sum_le_sum_of_subset_of_nonneg
    (Ico_subset_Ico_right hb.2.2.le) (fun j _ _ => (hw j).1)

lemma same_block (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) (n t : ℕ) (hn : n < o.labels.length) (htn : t < n)
    (hst : start o K n ≤ t) : owner o K n = owner o K t := by
  have hb := owner_bounds s o K ho n hn
  have ht := owner_bounds s o K ho t (htn.trans hn)
  simp only [start, hn, ite_true] at hst
  exact interval_unique s o K ho t _ _ hb.1 ht.1 hst (htn.trans hb.2.2) ht.2.1 ht.2.2

lemma block_window (s : TraceState) (o : CollectionOrdering) (c : Controls) (K B : ℕ)
    (hp : CollectionParameters s) (hc : CompletedLedger s) (hs : Structural s o c K B)
    (t : ℕ) (ht : t < o.labels.length) :
    (∑ n ∈ range o.labels.length, if start o K n ≤ t ∧ t < n then o.movement s n else 0) ≤
      c.upperMass := by
  have hw := ordering_parameters s o K hp hc hs.1
  have hb := owner_bounds s o K hs.1 t ht
  rw [← sum_filter]
  apply le_trans _ (hs.2.2.2.2.2.1 (owner o K t) hb.1)
  apply sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => (hw j).1)
  intro n hn
  obtain ⟨hn, hlo, hhi⟩ := mem_filter.mp hn
  exact (owner_eq_iff s o K hs.1 n _ (mem_range.mp hn) hb.1).mp
    (same_block s o K hs.1 n t (mem_range.mp hn) hhi hlo)

lemma structural_transport (s : TraceState) (o : CollectionOrdering) (c : Controls) (K B : ℕ)
    (hp : CollectionParameters s) (hc : CompletedLedger s) (hh : Histories s)
    (hs : Structural s o c K B) :
    let W := row s o hs.1.2.2.2.2.2.2.2.2
    let C := fun n t => o.movement s t *
      transportMass (o.history s) (start o K n) n t 0 (W n)
    (∀ n t, 0 ≤ C n t) ∧
      ∀ t ∈ range o.labels.length,
        (∑ n ∈ range o.labels.length, o.movement s n *
          (∑ j ∈ range o.labels.length, C n j) * C n t) ≤ 5 ^ 2 * o.movement s t := by
  have hw := ordering_parameters s o K hp hc hs.1
  have hr := structural_row_bounds s o c K B hp hc hh hs
  have hcontrols := hs.2.1
  dsimp only
  constructor
  · intro n t
    exact mul_nonneg (hw t).1 (transportMass_bounds _ _ _ _ _ _ (by norm_num)
      (hr.1 n) (by simpa only [zero_add] using hr.2.2.1 n)).1
  · apply transport_certificate (o.history s) (frontier o) (start o K)
      (o.movement s) (o.refresh s) (row s o hs.1.2.2.2.2.2.2.2.2)
      o.labels.length (1 / 4) c.upperMass 2 1 5 hs.1.2.2.2.2.2.2.2.2
    · intro q
      by_cases hq : q < o.labels.length
      · simpa only [frontier, hq, ite_true] using (hs.2.2.2.1 q hq).1
      · simp [frontier, hq]
    · intro q
      by_cases hq : q < o.labels.length
      · simpa only [frontier, hq, ite_true] using (hs.2.2.2.1 q hq).2.1
      · simp [frontier, Ordering.history, hq]
    · exact start_le s o K hs.1
    · exact fun j => (hw j).1
    · exact fun j => (hw j).2.1
    · exact fun j => (hw j).1.trans (hw j).2.1
    · exact fun j => (hw j).2.2
    · norm_num
    · exact hcontrols.1.le.trans hcontrols.2.1
    · norm_num
    · exact fun j _ => (hw j).2.1.trans (hw j).2.2
    · exact hr.1
    · exact hr.2.2.1
    · exact hr.2.2.2
    · intro q hq
      simp only [frontier, hq, ite_true]
      rw [← work_interval _ _ _ (hs.2.2.2.1 q hq).1]
      exact (hs.2.2.2.1 q hq).2.2
    · exact main_window s o c K B hp hc hs
    · exact block_window s o c K B hp hc hs
    · have hH0 := hcontrols.1.le.trans hcontrols.2.1
      have hH1 := hcontrols.2.2.1
      nlinarith [sq_nonneg (1 - c.upperMass)]

lemma positive_horizon (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) : 0 < K := by
  by_contra h
  have hK : K = 0 := by omega
  have hzero := ho.2.2.2.1
  have hend := ho.2.2.2.2.1
  have hN := ho.1
  rw [hK, hzero] at hend
  omega

lemma total_mass (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (ho : o.Valid s K) :
    (∑ n ∈ range o.labels.length, o.movement s n) = ∑ k ∈ range K, mass s o k := by
  simpa only [mul_one] using LongTails.Proofs.BirchRetainedEnergy.partition_owner_sum
    (range o.labels.length) (owner o K) (o.movement s) (mass s o) K
    (fun n hn => (owner_bounds s o K ho n (mem_range.mp hn)).1)
    (fun k hk => by rw [owner_filter s o K ho k hk]; rfl) (fun _ => 1)

lemma total_mass_bound (s : TraceState) (o : CollectionOrdering) (c : Controls) (K B : ℕ)
    (hs : Structural s o c K B) :
    (∑ n ∈ range o.labels.length, o.movement s n) ≤ (K : ℝ) * c.upperMass := by
  rw [total_mass s o K hs.1]
  calc
    _ ≤ ∑ _ ∈ range K, c.upperMass := sum_le_sum (fun k hk => hs.2.2.2.2.2.1 k (mem_range.mp hk))
    _ = _ := by simp

end LongTails.Proofs.BirchCollectionBlocks
