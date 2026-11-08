import LongTails.Proofs.BirchCollectionRetainedQuotaStructure
import LongTails.Algorithms.BirchResourceNative

namespace LongTails.Proofs.BirchResourceNativeCertificate

open Finset LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionPolicies (variable_phase_gate)

open LongTails.Algorithms.BirchResourceNative (controls)

structure PacketProfile (s : TraceState) (o : LongTails.Setups.BirchCollections.Ordering) (K B : ℕ) : Prop where
  ordered : o.Valid s K
  anchor : ∀ n, o.anchor n = 0
  scale : ∀ n j, o.scale n j = if j = 0 then 1 else 2
  renewal : ∀ n j, o.renewalFrontier n j = o.frontier j
  resetRefresh : o.refresh s 0 = 1
  resetMove : o.movement s 0 = 1 / 8
  resetRaw : (o.raw s 0).card = B
  phase : ∀ j < o.labels.length, ∃ k < K,
    o.frontier j = o.cut k ∧ o.cut k ≤ j ∧ j < o.cut (k + 1)
  init : o.cut 1 = 1
  start : ∀ j < o.labels.length, range (o.frontier j) ⊆ o.history s j
  priorReset : ∀ j < o.labels.length, 0 < j → 0 < o.frontier j
  quota : ∀ k < K, ∑ j ∈ Ico (o.cut k) (o.cut (k + 1)), (o.raw s j).card = B
  retained : ∀ j < o.labels.length, 0 < j →
    o.refresh s j = ((o.raw s j).card : ℝ) / (8 * B) ∧ o.movement s j = o.refresh s j

lemma raw_le {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ} (h : PacketProfile s o K B)
    (j : ℕ) (hj : j < o.labels.length) : (o.raw s j).card ≤ B := by
  obtain ⟨k, hk, _, hlo, hhi⟩ := h.phase j hj
  rw [← h.quota k hk]
  exact single_le_sum (f := fun i => (o.raw s i).card) (fun _ _ => Nat.zero_le _) (mem_Ico.mpr ⟨hlo, hhi⟩)

lemma movement_nonneg {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ}
    (h : PacketProfile s o K B) (j : ℕ) (hj : j < o.labels.length) : 0 ≤ o.movement s j := by
  by_cases hz : j = 0
  · subst j
    rw [h.resetMove]
    norm_num
  · rw [(h.retained j hj (Nat.pos_of_ne_zero hz)).2, (h.retained j hj (Nat.pos_of_ne_zero hz)).1]
    positivity

lemma cut_mono {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ} (h : PacketProfile s o K B)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ K) : o.cut k ≤ o.cut l := by
  induction l with
  | zero =>
    have he : k = 0 := by omega
    rw [he]
  | succ l ih =>
    by_cases he : k = l + 1
    · simp [he]
    · exact (ih (by omega) (by omega)).trans (h.ordered.2.2.2.2.2.1 l (by omega)).le

lemma phase_mass {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ}
    (h : PacketProfile s o K B) (hB : 0 < B) (k : ℕ) (hk : k < K) :
    ∑ j ∈ Ico (o.cut k) (o.cut (k + 1)), o.movement s j = 1 / 8 := by
  by_cases hz : k = 0
  · subst k
    rw [h.ordered.2.2.2.1, h.init]
    simpa using h.resetMove
  have hk' : 1 ≤ o.cut k := by rw [← h.init]; exact cut_mono h (by omega) hk.le
  have hu : o.cut (k + 1) ≤ o.labels.length := by
    rw [← h.ordered.2.2.2.2.1]
    exact cut_mono h (by omega) le_rfl
  calc
    _ = ∑ j ∈ Ico (o.cut k) (o.cut (k + 1)), ((o.raw s j).card : ℝ) / (8 * B) := by
      apply sum_congr rfl
      intro j hj
      have hi := mem_Ico.mp hj
      have hb := h.retained j (hi.2.trans_le hu) (by omega)
      exact hb.2.trans hb.1
    _ = 1 / 8 := by
      rw [← sum_div, ← Nat.cast_sum, h.quota k hk]
      field_simp

lemma partial_mass {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ}
    (h : PacketProfile s o K B) (hB : 0 < B) (j : ℕ) (hj : j < o.labels.length) :
    ∑ i ∈ Ico (o.frontier j) j, o.movement s i ≤ 1 / 8 := by
  obtain ⟨k, hk, hf, _, hi⟩ := h.phase j hj
  rw [hf]
  refine (sum_le_sum_of_subset_of_nonneg (fun i hi' => ?_) (fun i hi' _ =>
    movement_nonneg h i ((mem_Ico.mp hi').2.trans_le ?_))).trans (phase_mass h hB k hk).le
  · exact mem_Ico.mpr ⟨(mem_Ico.mp hi').1, (mem_Ico.mp hi').2.trans hi⟩
  · rw [← h.ordered.2.2.2.2.1]
    exact cut_mono h (by omega) le_rfl

lemma gate {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B : ℕ}
    (h : PacketProfile s o K B) (hB : 0 < B) (n j : ℕ) (hj : j < o.labels.length) :
    1 ≤ o.scale n j ∧ o.scale n j ≤ 2 ∧ 0 ≤ 1 - o.refresh s j * o.scale n j ∧
    o.renewalFrontier n j ≤ j ∧
    (∀ i, i < o.renewalFrontier n j → i ∈ o.history s j) ∧
    1 ≤ o.scale n j * ∏ i ∈ range (j - o.renewalFrontier n j),
      (1 - o.refresh s (o.renewalFrontier n j + i) * o.scale n (o.renewalFrontier n j + i)) := by
  rw [h.renewal n j]
  obtain ⟨k, hk, hf, hlo, hhi⟩ := h.phase j hj
  have hfl : o.frontier j ≤ j := hf.symm ▸ hlo
  refine ⟨?_, ?_, ?_, hfl, fun i hi => h.start j hj (mem_range.mpr hi), ?_⟩
  · rw [h.scale]; split <;> norm_num
  · rw [h.scale]; split <;> norm_num
  · by_cases hz : j = 0
    · subst j
      rw [h.resetRefresh, h.scale]
      norm_num
    · rw [h.scale, ite_eq_right hz, (h.retained j hj (Nat.pos_of_ne_zero hz)).1]
      have hb : ((o.raw s j).card : ℝ) ≤ B := Nat.cast_le.mpr (raw_le h j hj)
      have hB' : (0 : ℝ) < B := by exact_mod_cast hB
      have hd : ((o.raw s j).card : ℝ) / (8 * B) ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity)).2
        linarith
      linarith
  · by_cases hz : j = 0
    · subst j
      simp [h.scale]
    · have hp := h.priorReset j hj (Nat.pos_of_ne_zero hz)
      have hsum : (∑ i ∈ range (j - o.frontier j), (o.raw s (o.frontier j + i)).card) ≤ 2 * B := by
        have he : (∑ i ∈ Ico (o.frontier j) j, (o.raw s i).card) =
            ∑ i ∈ range (j - o.frontier j), (o.raw s (o.frontier j + i)).card := by
          rw [sum_Ico_eq_sum_range]
        rw [← he]
        refine (sum_le_sum_of_subset_of_nonneg (t := Ico (o.cut k) (o.cut (k + 1)))
          (fun i hi => ?_) (fun _ _ _ => Nat.zero_le _)).trans ?_
        · exact mem_Ico.mpr ⟨hf ▸ (mem_Ico.mp hi).1, (mem_Ico.mp hi).2.trans hhi⟩
        · rw [h.quota k hk]
          omega
      have hgate := variable_phase_gate (range (j - o.frontier j))
        (fun i => (o.raw s (o.frontier j + i)).card) B hB
        (fun i hi => raw_le h _ (by have := mem_range.mp hi; omega)) hsum
      rw [h.scale, ite_eq_right hz]
      refine hgate.trans_eq ?_
      congr 1
      apply prod_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [h.scale, ite_eq_right (by omega : o.frontier j + i ≠ 0),
        (h.retained _ (by omega) (by omega)).1]
      ring

lemma structural {s : TraceState} {o : LongTails.Setups.BirchCollections.Ordering} {K B D : ℕ} (h : PacketProfile s o K B)
    (hB : 0 < B) (hcost : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤ D) :
    Structural s o (controls D) K B := by
  refine ⟨h.ordered, by norm_num [Controls.Valid, controls], h.resetRefresh, ?_, ?_, ?_,
    ?_, ?_, hcost, ?_⟩
  · intro j hj
    obtain ⟨k, _, hf, hl, _⟩ := h.phase j hj
    exact ⟨hf.symm ▸ hl, h.start j hj, (partial_mass h hB j hj).trans (by norm_num)⟩
  · intro k hk
    exact (phase_mass h hB k hk).ge
  · intro k hk
    exact (phase_mass h hB k hk).le
  · intro j hj
    by_cases hz : j = 0
    · subst j
      rw [h.resetRefresh, h.resetRaw, one_mul]
    · rw [(h.retained j hj (Nat.pos_of_ne_zero hz)).1]
      have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      have he : ((o.raw s j).card : ℝ) / (8 * B) * B = ((o.raw s j).card : ℝ) / 8 := by field_simp
      rw [he]
      have hp : 0 ≤ ((o.raw s j).card : ℝ) := by positivity
      linarith
  · intro j hj
    right
    by_cases hz : j = 0
    · subst j
      rw [h.resetMove, h.resetRaw]
      dsimp [controls]
      ring_nf
      exact le_rfl
    · have hp := h.retained j hj (Nat.pos_of_ne_zero hz)
      rw [hp.2, hp.1]
      dsimp [controls]
      have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      apply le_of_eq
      field_simp
  · intro n hn
    rw [h.anchor]
    simp only [Nat.zero_add, Nat.sub_zero]
    refine ⟨Nat.zero_le _, h.resetRefresh, fun _ => ?_, ?_, fun j hj =>
      gate h hB n j (hj.trans_lt hn)⟩
    · exact subset_antisymm (h.ordered.2.2.2.2.2.2.2.2 0) (by simp)
    · intro j hj hjn
      have hi := hjn.trans_lt hn
      exact (range_mono (h.priorReset j hi hj)).trans (h.start j hi)

end LongTails.Proofs.BirchResourceNativeCertificate
