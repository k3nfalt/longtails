import LongTails.Proofs.BirchNonEuclideanSharedTransport

namespace LongTails.Proofs.BirchNonEuclideanSharedSchur

open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanShared
open LongTails.Proofs.BirchNonEuclideanSharedTransport

lemma damped_linear_power (α : ℝ) (n : ℕ) (hα1 : α ≤ 1) :
    (1 + (n : ℝ) * α) * (1 - α) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hb : (1 + ((n : ℝ) + 1) * α) * (1 - α) ≤ 1 + (n : ℝ) * α := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg α)]
      calc
        _ = ((1 + ((n : ℝ) + 1) * α) * (1 - α)) * (1 - α) ^ n := by
          rw [pow_succ, Nat.cast_add, Nat.cast_one]
          ring
        _ ≤ (1 + (n : ℝ) * α) * (1 - α) ^ n :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith) _)
        _ ≤ _ := ih

lemma ema_inverse_sharp (H B : ℕ) (hH : 0 < H) (hB : 2 * H ≤ B) :
    0 < 1 - (1 - 1 / (B : ℝ)) ^ H ∧
      1 / (1 - (1 - 1 / (B : ℝ)) ^ H) ≤ 1 + (B : ℝ) / H := by
  have hB0 : 0 < B := by omega
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hBr : 0 < (B : ℝ) := Nat.cast_pos.mpr hB0
  have hl := (LongTails.Proofs.BirchDelayedCoefficients.ema_inverse_le H B hH hB).1
  refine ⟨hl, (div_le_iff₀ hl).mpr ?_⟩
  have hb := damped_linear_power (1 / (B : ℝ)) H
    ((div_le_one hBr).mpr (by exact_mod_cast hB0))
  have hmul := mul_le_mul_of_nonneg_left hb hBr.le
  have he : (B : ℝ) * ((1 + H * (1 / (B : ℝ))) * (1 - 1 / (B : ℝ)) ^ H) =
      (B + H) * (1 - 1 / (B : ℝ)) ^ H := by field_simp
  rw [he, mul_one] at hmul
  calc
    1 ≤ ((H + (B : ℝ)) * (1 - (1 - 1 / (B : ℝ)) ^ H)) / H :=
      (le_div_iff₀ hHr).mpr (by nlinarith)
    _ = _ := by field_simp

lemma strict_geometric_row (ρ : ℝ) (K k : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk : k < K) :
    (∑ j ∈ Finset.range K, if j < k then ρ ^ (k - j - 1) else 0) ≤ 1 / (1 - ρ) := by
  have he : (∑ j ∈ Finset.range k, if j < k then ρ ^ (k - j - 1) else 0) =
      ∑ j ∈ Finset.range K, if j < k then ρ ^ (k - j - 1) else 0 := by
    apply Finset.sum_subset (Finset.range_mono hk.le)
    intro j _ hj
    simp [show ¬j < k by simpa only [Finset.mem_range] using hj]
  rw [← he]
  have hf : (∑ j ∈ Finset.range k, if j < k then ρ ^ (k - j - 1) else 0) =
      ∑ j ∈ Finset.range k, ρ ^ (k - 1 - j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (Finset.mem_range.mp hj)]
    congr 1
    omega
  rw [hf, Finset.sum_range_reflect]
  exact LongTails.Proofs.BirchDelayedCoefficients.geometric_sum_le ρ k hρ hρ1

lemma strict_geometric_column (ρ : ℝ) (K j : ℕ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hj : j < K) :
    (∑ k ∈ Finset.range K, if j < k then ρ ^ (k - j - 1) else 0) ≤ 1 / (1 - ρ) := by
  have he : K = (j + 1) + (K - j - 1) := by omega
  conv_lhs => rw [he]
  rw [Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range (j + 1), if j < k then ρ ^ (k - j - 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [show ¬j < k by have := Finset.mem_range.mp hk; omega]
  rw [hz, zero_add]
  have hs : (∑ k ∈ Finset.range (K - j - 1), if j < j + 1 + k then ρ ^ (j + 1 + k - j - 1) else 0) =
      ∑ k ∈ Finset.range (K - j - 1), ρ ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  rw [hs]
  exact LongTails.Proofs.BirchDelayedCoefficients.geometric_sum_le ρ _ hρ hρ1

noncomputable def kernel (m H B k i h j v : ℕ) : ℝ :=
  if j < k then (1 - 1 / (B : ℝ)) ^ h * (1 / ((m : ℝ) * H)) *
    ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) * (2 - (1 - 1 / (B : ℝ)) ^ H)
  else if j = k ∧ i = v then 1 / (H : ℝ) else 0

lemma queryTransport_envelope (workers m H B K k i h j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hB : 0 < B) (hη : 0 < η) (hk : k < K) (hi : i < m) (hh : h < H)
    (hv : v < m) (hl : l < H) :
    queryTransport m H B K η k i h j v l ≤ kernel m H B k i h j v := by
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB)).mpr (by exact_mod_cast hB)
  have hρ0 : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  have hρ1 : (1 - 1 / (B : ℝ)) ^ H ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold kernel
  by_cases hjk : j < k
  · rw [ite_eq_left hjk]
    apply (queryTransport_historical workers m H B K k i h j v l η ht hw0 hw hm hB hη hk hv hl hjk).trans
    have hp : (1 - 1 / (B : ℝ)) ^ (h + 1) ≤ (1 - 1 / (B : ℝ)) ^ h :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    gcongr
    linarith
  · rw [ite_eq_right hjk]
    by_cases he : j = k ∧ i = v
    · rw [ite_eq_left he]
      exact queryTransport_le workers m H B K k i h j v l η ht hw0 hw hm hB hη hk hi hh hv hl
    · rw [ite_eq_right he]
      by_cases hjk' : j = k
      · subst j
        rw [queryTransport_current_other workers m H B K k i h v l η ht hw0 hw hm hi hh hv hl
          (by intro heq; exact he ⟨rfl, heq⟩)]
      · rw [queryTransport_later_zero workers m H B K k i h j v l η ht hw0 hw hm hi hh hv hl (by omega)]

lemma kernel_row_sum (m H B K k i h : ℕ) (hm : 0 < m) (hH : 0 < H) (hk : k < K) (hi : i < m) :
    (∑ j ∈ Finset.range K, ∑ v ∈ Finset.range m, ∑ _l ∈ Finset.range H, kernel m H B k i h j v) =
      (1 - 1 / (B : ℝ)) ^ h * (2 - (1 - 1 / (B : ℝ)) ^ H) *
        (∑ j ∈ Finset.range K, if j < k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) else 0) + 1 := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have he (j : ℕ) :
      (∑ v ∈ Finset.range m, ∑ _l ∈ Finset.range H, kernel m H B k i h j v) =
        (1 - 1 / (B : ℝ)) ^ h * (2 - (1 - 1 / (B : ℝ)) ^ H) *
          (if j < k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) else 0) +
            if j = k then 1 else 0 := by
    by_cases hjk : j < k
    · simp [kernel, hjk, show j ≠ k by omega]
      field_simp
    · by_cases hjk' : j = k
      · simp [kernel, hjk', hi, hHr]
      · simp [kernel, hjk, hjk']
  rw [Finset.sum_congr rfl (fun j _ => he j), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hk]

lemma kernel_row_bound (m H B K k i h : ℕ) (hm : 0 < m) (hH : 0 < H)
    (hB : 2 * H ≤ B) (hk : k < K) (hi : i < m) :
    (∑ j ∈ Finset.range K, ∑ v ∈ Finset.range m, ∑ _l ∈ Finset.range H, kernel m H B k i h j v) ≤
      2 + 2 * (B : ℝ) / H := by
  have hB0 : 0 < B := by omega
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB0)).mpr (by exact_mod_cast hB0)
  have hρ0 : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  have hρ1 : (1 - 1 / (B : ℝ)) ^ H < 1 := by
    have := (ema_inverse_sharp H B hH hB).1
    linarith
  have hden : 0 < 1 - (1 - 1 / (B : ℝ)) ^ H := by linarith
  have hpow : (1 - 1 / (B : ℝ)) ^ h ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hg := strict_geometric_row ((1 - 1 / (B : ℝ)) ^ H) K k hρ0 hρ1 hk
  have hBH : 1 ≤ (B : ℝ) / H := (one_le_div hHr).mpr (by exact_mod_cast (show H ≤ B by omega))
  have he (r : ℝ) (hr : 1 - r ≠ 0) : 1 * (2 - r) * (1 / (1 - r)) + 1 =
      2 + 1 / (1 - r) := by field_simp; ring
  rw [kernel_row_sum m H B K k i h hm hH hk hi]
  calc
    _ ≤ 1 * (2 - (1 - 1 / (B : ℝ)) ^ H) * (1 / (1 - (1 - 1 / (B : ℝ)) ^ H)) + 1 := by
      gcongr <;> linarith
    _ = 2 + 1 / (1 - (1 - 1 / (B : ℝ)) ^ H) := he _ hden.ne'
    _ ≤ 3 + (B : ℝ) / H := by linarith [(ema_inverse_sharp H B hH hB).2]
    _ ≤ _ := by rw [mul_div_assoc]; linarith

lemma transport_row (workers m H B K k i h : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hH : 0 < H) (hB : 2 * H ≤ B) (hη : 0 < η)
    (hk : k < K) (hi : i < m) (hh : h < H) :
    (∑ j ∈ Finset.range K, ∑ v ∈ Finset.range m, ∑ l ∈ Finset.range H,
      queryTransport m H B K η k i h j v l) ≤ 2 + 2 * (B : ℝ) / H := by
  apply le_trans _ (kernel_row_bound m H B K k i h hm hH hB hk hi)
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro l hl
  exact queryTransport_envelope workers m H B K k i h j v l η ht hw0 hw hm (by omega) hη hk hi hh
    (Finset.mem_range.mp hv) (Finset.mem_range.mp hl)

lemma ema_sum (H B : ℕ) (hB : 0 < B) :
    (∑ h ∈ Finset.range H, (1 - 1 / (B : ℝ)) ^ h) =
      (B : ℝ) * (1 - (1 - 1 / (B : ℝ)) ^ H) := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have he := geom_sum_mul_neg (1 - 1 / (B : ℝ)) H
  have hd : 1 - (1 - 1 / (B : ℝ)) = 1 / (B : ℝ) := by ring
  rw [hd] at he
  have hf := congrArg (fun x : ℝ => x * B) he
  simpa [hb, mul_assoc, mul_comm (B : ℝ)] using hf

lemma kernel_column_sum (m H B K j v : ℕ) (hm : 0 < m) (hH : 0 < H)
    (hj : j < K) (hv : v < m) :
    (∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, kernel m H B k i h j v) =
      ((∑ h ∈ Finset.range H, (1 - 1 / (B : ℝ)) ^ h) * (2 - (1 - 1 / (B : ℝ)) ^ H) / H) *
        (∑ k ∈ Finset.range K, if j < k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) else 0) + 1 := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have he (k : ℕ) :
      (∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, kernel m H B k i h j v) =
        ((∑ h ∈ Finset.range H, (1 - 1 / (B : ℝ)) ^ h) * (2 - (1 - 1 / (B : ℝ)) ^ H) / H) *
          (if j < k then ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1) else 0) +
            if k = j then 1 else 0 := by
    rw [Finset.sum_comm]
    by_cases hjk : j < k
    · have hh (h : ℕ) : (∑ i ∈ Finset.range m, kernel m H B k i h j v) =
          (1 - 1 / (B : ℝ)) ^ h *
            ((2 - (1 - 1 / (B : ℝ)) ^ H) / H * ((1 - 1 / (B : ℝ)) ^ H) ^ (k - j - 1)) := by
        simp [kernel, hjk]
        field_simp
      rw [Finset.sum_congr rfl (fun h _ => hh h), ← Finset.sum_mul]
      simp only [ite_eq_left hjk, ite_eq_right (show k ≠ j by omega), add_zero]
      ring
    · by_cases hkj : k = j
      · simp [kernel, hkj, hv, hHr]
      · simp [kernel, hjk, hkj, Ne.symm hkj]
  rw [Finset.sum_congr rfl (fun k _ => he k), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hj]

lemma kernel_column_bound (m H B K j v : ℕ) (hm : 0 < m) (hH : 0 < H)
    (hB : 2 * H ≤ B) (hj : j < K) (hv : v < m) :
    (∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, kernel m H B k i h j v) ≤
      2 + 2 * (B : ℝ) / H := by
  have hB0 : 0 < B := by omega
  have hHr : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hα0 : 0 ≤ 1 / (B : ℝ) := by positivity
  have hα1 : 1 / (B : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hB0)).mpr (by exact_mod_cast hB0)
  have hρ0 : 0 ≤ (1 - 1 / (B : ℝ)) ^ H := pow_nonneg (by linarith) _
  have hden := (ema_inverse_sharp H B hH hB).1
  have hρ1 : (1 - 1 / (B : ℝ)) ^ H < 1 := by linarith
  have hg := strict_geometric_column ((1 - 1 / (B : ℝ)) ^ H) K j hρ0 hρ1 hj
  have hc : 0 ≤ (B : ℝ) * (1 - (1 - 1 / (B : ℝ)) ^ H) *
      (2 - (1 - 1 / (B : ℝ)) ^ H) / H := by
    apply div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) hden.le) (by linarith)) hHr.le
  have he (b r z : ℝ) (hr : 1 - r ≠ 0) :
      b * (1 - r) * (2 - r) / z * (1 / (1 - r)) = (2 - r) * (b / z) := by field_simp
  rw [kernel_column_sum m H B K j v hm hH hj hv, ema_sum H B hB0]
  calc
    _ ≤ ((B : ℝ) * (1 - (1 - 1 / (B : ℝ)) ^ H) * (2 - (1 - 1 / (B : ℝ)) ^ H) / H) *
        (1 / (1 - (1 - 1 / (B : ℝ)) ^ H)) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hg hc) le_rfl
    _ = (2 - (1 - 1 / (B : ℝ)) ^ H) * ((B : ℝ) / H) + 1 := by rw [he _ _ _ hden.ne']
    _ ≤ _ := by
      rw [mul_div_assoc]
      have hz : 0 ≤ (B : ℝ) / H := by positivity
      nlinarith

lemma transport_column (workers m H B K j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hH : 0 < H) (hB : 2 * H ≤ B) (hη : 0 < η)
    (hj : j < K) (hv : v < m) (hl : l < H) :
    (∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
      queryTransport m H B K η k i h j v l) ≤ 2 + 2 * (B : ℝ) / H := by
  apply le_trans _ (kernel_column_bound m H B K j v hm hH hB hj hv)
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro h hh
  exact queryTransport_envelope workers m H B K k i h j v l η ht hw0 hw hm (by omega) hη
    (Finset.mem_range.mp hk) (Finset.mem_range.mp hi) (Finset.mem_range.mp hh) hv hl

lemma sharpSet_sum {α : Type*} [AddCommMonoid α] (m H B K : ℕ) (f : ℕ → α) :
    (∑ e ∈ sharpSet m H B K, f e) =
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, f (sharpIndex m H B k i h) := by
  have he : sharpSet m H B K = ((Finset.range K) ×ˢ ((Finset.range m) ×ˢ (Finset.range H))).image
      (fun z => sharpIndex m H B z.1 z.2.1 z.2.2) := by
    ext e
    constructor
    · intro he
      obtain ⟨k, hk, i, hi, h, hh, he⟩ := by
        simpa only [sharpSet, roundSharps, Finset.mem_biUnion, Finset.mem_image] using he
      exact Finset.mem_image.mpr ⟨(k, i, h), Finset.mem_product.mpr
        ⟨hk, Finset.mem_product.mpr ⟨hi, hh⟩⟩, he⟩
    · intro he
      obtain ⟨⟨k, i, h⟩, hmem, he⟩ := Finset.mem_image.mp he
      obtain ⟨hk, hi, hh⟩ := by simpa only [Finset.mem_product] using hmem
      exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_image.mpr ⟨h, hh, he⟩⟩⟩
  rw [he, Finset.sum_image]
  · simp only [Finset.sum_product]
  · intro x hx y hy he
    obtain ⟨hxk, hxi, hxh⟩ := by simpa only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] using hx
    obtain ⟨hyk, hyi, hyh⟩ := by simpa only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] using hy
    obtain ⟨hk, hi, hh⟩ := sharpIndex_injective m H B x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 hxi hyi hxh hyh he
    exact Prod.ext hk (Prod.ext hi hh)

def owner (m H B e : ℕ) : ℕ := (e - (m * B + 6)) / (m * (4 * H + 5) + 3)

lemma owner_sharp (m H B k i h : ℕ) (hi : i < m) (hh : h < H) :
    owner m H B (sharpIndex m H B k i h) = k := by
  have he : sharpIndex m H B k i h - (m * B + 6) =
      i * (4 * H + 5) + 4 * h + (m * (4 * H + 5) + 3) * k := by
    dsimp [sharpIndex, queryIndex]
    rw [Nat.mul_comm (m * (4 * H + 5) + 3) k]
    omega
  have hsmall : i * (4 * H + 5) + 4 * h < m * (4 * H + 5) + 3 := by
    have hx := Nat.mul_le_mul_right (4 * H + 5) (show i + 1 ≤ m by omega)
    rw [Nat.add_mul, Nat.one_mul] at hx
    omega
  dsimp only [owner]
  rw [he, Nat.add_mul_div_left _ _ (by omega : 0 < m * (4 * H + 5) + 3),
    Nat.div_eq_of_lt hsmall, Nat.zero_add]

lemma sharpSet_fiber_sum {α : Type*} [AddCommMonoid α] (m H B K k : ℕ)
    (hk : k < K) (f : ℕ → α) :
    (∑ e ∈ (sharpSet m H B K).filter (fun e => owner m H B e = k), f e) =
      ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, f (sharpIndex m H B k i h) := by
  rw [Finset.sum_filter, sharpSet_sum]
  have he : (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
      if owner m H B (sharpIndex m H B j i h) = k then f (sharpIndex m H B j i h) else 0) =
      ∑ j ∈ Finset.range K, if j = k then
        ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, f (sharpIndex m H B j i h) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H,
          if j = k then f (sharpIndex m H B j i h) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro h hh
        rw [owner_sharp m H B j i h (Finset.mem_range.mp hi) (Finset.mem_range.mp hh)]
      _ = _ := by by_cases hj : j = k <;> simp [hj]
  rw [he]
  simp [Finset.mem_range.mpr hk]

lemma transport_schur (workers m H B K j v l : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (hw0 : 0 < workers) (hw : m < workers)
    (hm : 0 < m) (hH : 0 < H) (hB : 2 * H ≤ B) (hη : 0 < η)
    (hj : j < K) (hv : v < m) (hl : l < H) :
    (∑ k ∈ Finset.range K, ∑ i ∈ Finset.range m, ∑ h ∈ Finset.range H, (1 / ((m : ℝ) * H)) *
      (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range m, ∑ c ∈ Finset.range H,
        queryTransport m H B K η k i h a b c) * queryTransport m H B K η k i h j v l) ≤
      (2 + 2 * (B : ℝ) / H) ^ 2 * (1 / ((m : ℝ) * H)) := by
  let s := (Finset.range K) ×ˢ ((Finset.range m) ×ˢ (Finset.range H))
  let C := fun (x y : ℕ × ℕ × ℕ) => queryTransport m H B K η x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2
  let D := 2 + 2 * (B : ℝ) / H
  have hrow : ∀ x ∈ s, ∑ y ∈ s, C x y ≤ D := by
    intro x hx
    obtain ⟨hk, hi, hh⟩ := by simpa only [s, Finset.mem_product, Finset.mem_range] using hx
    simpa only [s, C, D, Finset.sum_product] using
      transport_row workers m H B K x.1 x.2.1 x.2.2 η ht hw0 hw hm hH hB hη hk hi hh
  have hcol : ∀ y ∈ s, ∑ x ∈ s, C x y ≤ D := by
    intro y hy
    obtain ⟨hk, hi, hh⟩ := by simpa only [s, Finset.mem_product, Finset.mem_range] using hy
    simpa only [s, C, D, Finset.sum_product] using
      transport_column workers m H B K y.1 y.2.1 y.2.2 η ht hw0 hw hm hH hB hη hk hi hh
  have he := LongTails.Proofs.BirchDelayedCoefficients.weighted_schur s C (1 / ((m : ℝ) * H)) D D
    (by positivity) (by dsimp [D]; positivity) le_rfl
    (fun x _ y _ => queryTransport_nonneg m H B K η x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2)
    hrow hcol (j, v, l) (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_product.mpr ⟨Finset.mem_range.mpr hv, Finset.mem_range.mpr hl⟩⟩)
  simpa only [s, C, D, Finset.sum_product] using he

end LongTails.Proofs.BirchNonEuclideanSharedSchur
