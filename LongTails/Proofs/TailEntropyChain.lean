import LongTails.Proofs.TailEntropyConjugate
import LongTails.Proofs.KnownGapChainWeights

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Finset
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.TailEntropyChain

open TailEntropyCurvature TailEntropyDual TailEntropyConjugate CompactConjugate
open GeneralizedSmoothHardDual (radial radial_nonneg feasible feasible_zero feasible_compact
  feasible_norm_bound)
open KnownGapChainWeights (weight peak weight_pos peak_pos weight_le_peak weight_lower weight_ratio)

lemma entropyTerm_zero (T : ℝ) : entropyTerm 0 T = 0 := by simp [entropyTerm]

lemma entropyTerm_self (x : ℝ) : entropyTerm x x = 0 := by
  unfold entropyTerm
  by_cases hx : x = 0
  · simp [hx]
  · simp [div_self hx]

lemma entropyTerm_antitone (x T T' : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T) (hTT : T ≤ T') :
    entropyTerm x T' ≤ entropyTerm x T := by
  unfold entropyTerm
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp
  · apply mul_le_mul_of_nonneg_left _ hpos.le
    have hT : 0 < T := lt_of_lt_of_le hpos hxT
    apply Real.log_le_log (div_pos hpos (lt_of_lt_of_le hT hTT))
    exact div_le_div_of_nonneg_left hpos.le hT hTT

lemma neg_entropyTerm_le (x T : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T) : -entropyTerm x T ≤ T - x := by
  unfold entropyTerm
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp; linarith
  · have hT : 0 < T := lt_of_lt_of_le hpos hxT
    have hl := Real.log_le_sub_one_of_pos (div_pos hT hpos)
    have hinv : Real.log (x / T) = -Real.log (T / x) := by rw [← Real.log_inv, inv_div]
    rw [hinv]
    have he : x * (T / x - 1) = T - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl hpos.le]

lemma tail_split (p : ℕ → ℝ) {k j m : ℕ} (hkj : k ≤ j) (hj : j < m) :
    tail p m k = (∑ i ∈ Ico k j, p i) + p j + tail p m (j + 1) := by
  unfold tail
  rw [← Finset.sum_Ico_consecutive p hkj hj.le, Finset.sum_eq_sum_Ico_succ_bot hj]
  ring

lemma tail_sum_identity (p : ℕ → ℝ) (j m : ℕ) :
    ∑ k ∈ Ico j m, tail p m (k + 1) = ∑ i ∈ Ico (j + 1) m, ((i : ℝ) - j) * p i := by
  unfold tail
  rw [Finset.sum_comm' (t' := Ico (j + 1) m) (s' := fun i => Ico j i)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hji : j ≤ i := by simp at hi; omega
    rw [Nat.cast_sub hji]
  · intro k i
    simp only [Finset.mem_Ico]
    omega

lemma entropy_move (p q : ℕ → ℝ) (m j : ℕ) (hj : j < m) (hp : ∀ k < m, 0 ≤ p k) (c : ℝ)
    (hc : tail p m (j + 1) ≤ c) (hq1 : ∀ k < j, q k = p k) (hqj : q j = p j + c)
    (hq2 : ∀ k, j < k → k < m → q k = 0) :
    ∑ k ∈ range m, entropyTerm (q k) (tail q m k) -
      ∑ k ∈ range m, entropyTerm (p k) (tail p m k) ≤
      ∑ i ∈ Ico (j + 1) m, ((i : ℝ) - j) * p i := by
  have hqtail_later : tail q m (j + 1) = 0 := by
    unfold tail
    exact Finset.sum_eq_zero (fun i hi => by simp at hi; exact hq2 i (by omega) hi.2)
  have hqtail (k : ℕ) (hk : k ≤ j) : tail q m k = tail p m k - tail p m (j + 1) + c := by
    rw [tail_split q hk hj, tail_split p hk hj, hqtail_later, hqj]
    have hs : ∑ i ∈ Ico k j, q i = ∑ i ∈ Ico k j, p i :=
      Finset.sum_congr rfl (fun i hi => hq1 i (by simp at hi; omega))
    rw [hs]; ring
  rw [← Finset.sum_range_add_sum_Ico _ hj.le, ← Finset.sum_range_add_sum_Ico _ hj.le]
  have hfirst : ∑ k ∈ range j, entropyTerm (q k) (tail q m k) ≤
      ∑ k ∈ range j, entropyTerm (p k) (tail p m k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < j := Finset.mem_range.mp hk
    rw [hq1 k hk']
    apply entropyTerm_antitone _ _ _ (hp k (by omega)) (tail_le p (by omega) hp)
    rw [hqtail k hk'.le]; linarith
  have hsecond : ∑ k ∈ Ico j m, entropyTerm (q k) (tail q m k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_Ico] at hk
    rcases hk.1.eq_or_lt with he | hlt
    · rw [← he]
      have ht : tail q m j = q j := by rw [tail_succ q hj, hqtail_later, add_zero]
      rw [ht, entropyTerm_self]
    · rw [hq2 k hlt hk.2, entropyTerm_zero]
  have hthird : -∑ k ∈ Ico j m, entropyTerm (p k) (tail p m k) ≤ ∑ k ∈ Ico j m, tail p m (k + 1) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have h := neg_entropyTerm_le (p k) (tail p m k) (hp k hk.2) (tail_le p hk.2 hp)
    rw [tail_succ p hk.2] at h ⊢
    linarith
  rw [hsecond, ← tail_sum_identity]
  linarith

lemma fin_later_sum {m : ℕ} (j : Fin m) (g : ℕ → ℝ → ℝ) (u : EuclideanSpace ℝ (Fin m)) :
    ∑ l : Fin m, (if j < l then g l.val (u l) else 0) =
      ∑ k ∈ Ico (j.val + 1) m, g k (ext u k) := by
  calc ∑ l : Fin m, (if j < l then g l.val (u l) else 0)
      = ∑ l : Fin m, (fun k => if j.val < k then g k (ext u k) else 0) l.val := by
        apply Finset.sum_congr rfl
        intro l _
        simp only [Fin.lt_def, ext_fin]
    _ = ∑ k ∈ range m, (if j.val < k then g k (ext u k) else 0) :=
        Fin.sum_univ_eq_sum_range (fun k => if j.val < k then g k (ext u k) else 0) m
    _ = ∑ k ∈ (range m).filter (fun k => j.val < k), g k (ext u k) :=
        (Finset.sum_filter _ _).symm
    _ = ∑ k ∈ Ico (j.val + 1) m, g k (ext u k) := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega

end LongTails.Proofs.TailEntropyChain
