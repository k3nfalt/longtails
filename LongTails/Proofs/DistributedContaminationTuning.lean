import LongTails.Algorithms.ContaminatedParallelDescent

namespace LongTails.Proofs.DistributedContaminationTuning

open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution)
open LongTails.Setups.DistributedContaminatedSmoothNonconvex

lemma radius_bounds {σ η cap : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hη' : η ≤ 1 / 16)
    (hcap : 0 < cap) (hfloor : 24 * σ ≤ cap) :
    let B := clipRadius σ η cap
    24 * σ ≤ B ∧ B ≤ cap ∧
      2 * σ ^ 2 / B + η * (3 * B / 2) ≤ 13 * σ * Real.sqrt η + 2 * σ ^ 2 / cap ∧
      σ ^ 2 + η * (3 * B / 2) ^ 2 ≤ 145 * σ ^ 2 := by
  have hs := Real.sq_sqrt hη
  have hsr := Real.sqrt_nonneg η
  rcases hη.eq_or_lt with hz | hp
  · subst η
    simp [clipRadius, hfloor]
    nlinarith [sq_nonneg σ]
  have hspos := Real.sqrt_pos.mpr hp
  have hroot : Real.sqrt η ≤ 1 / 4 := by nlinarith
  have hsmall : 24 * σ ≤ 8 * σ / Real.sqrt η := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot hσ]
  let B := min (8 * σ / Real.sqrt η) cap
  have hb : 24 * σ ≤ B := le_min hsmall hfloor
  have hbu : B ≤ cap := min_le_right _ _
  have hb0 : 0 ≤ B := by linarith
  have hbroot : B * Real.sqrt η ≤ 8 * σ := (le_div_iff₀ hspos).mp (min_le_left _ _)
  have hm : η * (3 * B / 2) ≤ 12 * σ * Real.sqrt η := by
    have hh := mul_le_mul_of_nonneg_right hbroot hsr
    nlinarith only [hh, congrArg (fun z => B * z) hs]
  have hv : σ ^ 2 + η * (3 * B / 2) ^ 2 ≤ 145 * σ ^ 2 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hb0 hsr) hbroot 2
    rw [mul_pow, hs] at hh
    nlinarith
  have hclean : 2 * σ ^ 2 / B ≤ σ * Real.sqrt η + 2 * σ ^ 2 / cap := by
    dsimp only [B]
    rw [min_def]
    split_ifs
    · rcases hσ.eq_or_lt with hz | hpos
      · subst σ; simp
      have he : 2 * σ ^ 2 / (8 * σ / Real.sqrt η) = σ * Real.sqrt η / 4 := by
        field_simp; ring
      rw [he]
      linarith [mul_nonneg hσ hsr, div_nonneg (show 0 ≤ 2 * σ ^ 2 by positivity) hcap.le]
    · linarith [mul_nonneg hσ hsr]
  simp only [clipRadius, ite_eq_left hp]
  exact ⟨hb, hbu, by dsimp only [B] at *; linarith, hv⟩

lemma fresh_lower (p : Params) (q : ℕ) (i : Fin p.n) :
    16777216 * (q : ℝ) * (1 + (∑ j, (p.h j : ℝ) * p.σ j ^ 2) /
      ((p.n : ℝ) ^ 2 * resolution (network p) ^ 2 * (p.h i : ℝ))) ≤ freshCount p q i := by
  unfold freshCount
  push_cast
  exact (mul_le_mul_of_nonneg_left (add_le_add_right (Nat.le_ceil _) 1) (by positivity)).trans
    (le_max_right _ _)

lemma fresh_geometry {S a h σ q m : ℝ} (ha : 0 < a) (hh : 0 < h) (hσ : 0 ≤ σ)
    (hq : 0 < q) (hS : h * σ ^ 2 ≤ S) (hm : 16777216 * q * (1 + S / (a ^ 2 * h)) ≤ m) :
    24 * σ ≤ a * m / (2048 * q) := by
  have hratio : (σ / a) ^ 2 ≤ S / (a ^ 2 * h) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos ha) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hS (sq_nonneg a)]
  have hbase : σ / a ≤ 1 + S / (a ^ 2 * h) := by
    nlinarith [sq_nonneg (σ / a - 1)]
  have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 16777216 * q by positivity)
  have hlow : 49152 * q * (σ / a) ≤ m := by
    nlinarith [mul_nonneg hq.le (div_nonneg hσ ha.le)]
  apply (le_div_iff₀ (by positivity)).mpr
  have he := mul_le_mul_of_nonneg_right hlow ha.le
  field_simp at he
  linarith

lemma pooled_variance {ι : Type*} [Fintype ι] (h σ m : ι → ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i)
    (hbatch : ∀ i, 16777216 * q * (1 + (∑ j, h j * σ j ^ 2) / (a ^ 2 * h i)) ≤ m i) :
    (∑ i, σ i ^ 2 / m i) ≤ a ^ 2 / (16777216 * q) := by
  classical
  let S := ∑ j, h j * σ j ^ 2
  have hnon (i) : 0 ≤ h i * σ i ^ 2 := mul_nonneg (hh i).le (sq_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hnon i)
  rcases hS.eq_or_lt with hz | hp
  · have he (i) : σ i = 0 := by
      have hi : h i * σ i ^ 2 ≤ S := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
      have hn := le_antisymm (hi.trans hz.ge) (hnon i)
      exact pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp ((mul_eq_zero.mp hn).resolve_left (hh i).ne')
    simp [he, div_nonneg (sq_nonneg a) (show 0 ≤ 16777216 * q by positivity)]
  have hpoint (i) : σ i ^ 2 / m i ≤ (h i * σ i ^ 2) * (a ^ 2 / (16777216 * q * S)) := by
    have hsmall : 16777216 * q * (S / (a ^ 2 * h i)) ≤ m i := by
      apply le_trans _ (hbatch i)
      dsimp only [S]
      gcongr
      linarith
    have hmul : 16777216 * q * S ≤ m i * (a ^ 2 * h i) := by
      apply (div_le_iff₀ (mul_pos (sq_pos_of_pos ha) (hh i))).mp
      simpa only [mul_div_assoc] using hsmall
    apply (div_le_iff₀ (hm i)).mpr
    rw [show h i * σ i ^ 2 * (a ^ 2 / (16777216 * q * S)) * m i =
      (m i * (a ^ 2 * h i) * σ i ^ 2) / (16777216 * q * S) by ring]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hmul (sq_nonneg (σ i))]
  apply (Finset.sum_le_sum (fun i _ => hpoint i)).trans_eq
  rw [← Finset.sum_mul]
  change S * (a ^ 2 / (16777216 * q * S)) = _
  field_simp

lemma pooled_bias {ι : Type*} [Fintype ι] {s n q : ℝ} (hs : 0 < s) (hn : 0 < n)
    (hq : 0 < q) (σ η m : ι → ℝ) (hm : ∀ i, 0 < m i)
    (hfloor : 512 * (∑ i, σ i * Real.sqrt (η i)) ≤ n * s)
    (hvar : (∑ i, σ i ^ 2 / m i) ≤ (n * s) ^ 2 / (16777216 * q)) :
    (∑ i, (13 * σ i * Real.sqrt (η i) + 2 * σ i ^ 2 / (n * s * m i / (2048 * q))) / n) ≤ s / 4 := by
  have he (i) : (13 * σ i * Real.sqrt (η i) + 2 * σ i ^ 2 / (n * s * m i / (2048 * q))) / n =
      (13 / n) * (σ i * Real.sqrt (η i)) + (4096 * q / (n ^ 2 * s)) * (σ i ^ 2 / m i) := by
    field_simp [ne_of_gt (hm i)]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : (13 / n) * (∑ i, σ i * Real.sqrt (η i)) ≤ 13 * s / 512 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 4096*q/(n^2*s) by positivity)
  have he' : 4096*q/(n^2*s) * ((n*s)^2/(16777216*q)) = s / 4096 := by
    field_simp
    ring
  rw [he'] at h2
  linarith

lemma sum_repetitions {ι : Type*} [Fintype ι] (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    {n : ℝ} (hn : 0 < n) (v : ι → ℝ) :
    (∑ z : (i : ι) × Fin (m i), (n * (m z.1 : ℝ))⁻¹ * v z.1) = ∑ i, v i / n := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (0 : ℝ) < m i := by exact_mod_cast hm i
  field_simp

lemma sum_square_weights {ι : Type*} [Fintype ι] (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    {n : ℝ} (hn : 0 < n) (v : ι → ℝ) :
    (∑ z : (i : ι) × Fin (m i), (n * (m z.1 : ℝ))⁻¹ ^ 2 * v z.1) =
      (∑ i, v i / (m i : ℝ)) / n ^ 2 := by
  rw [Fintype.sum_sigma, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (0 : ℝ) < m i := by exact_mod_cast hm i
  field_simp

end LongTails.Proofs.DistributedContaminationTuning
