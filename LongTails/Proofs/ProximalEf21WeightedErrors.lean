import LongTails.Proofs.ProximalEf21Geometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21WeightedErrors

open LongTails.Proofs.ProximalEf21Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_cauchy_schwarz {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (u : ι → E) :
    ‖∑ i, u i‖ ^ 2 ≤ (∑ i, (w i)⁻¹) * ∑ i, w i * ‖u i‖ ^ 2 := by
  classical
  let a : ℝ := ∑ i, (w i)⁻¹
  have ha : 0 < a := by
    exact Finset.sum_pos (fun i _ => inv_pos.mpr (hw i)) Finset.univ_nonempty
  let z : E := a⁻¹ • ∑ i, u i
  have hs :
      2 * ⟪∑ i, u i, z⟫_ℝ ≤
        (∑ i, w i * ‖u i‖ ^ 2) + a * ‖z‖ ^ 2 := by
    calc
      2 * ⟪∑ i, u i, z⟫_ℝ = ∑ i, 2 * ⟪u i, z⟫_ℝ := by
        simp only [sum_inner, Finset.mul_sum]
      _ ≤ ∑ i, (w i * ‖u i‖ ^ 2 + (w i)⁻¹ * ‖z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact twice_inner_young (w i) (hw i) (u i) z
      _ = (∑ i, w i * ‖u i‖ ^ 2) + a * ‖z‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, a]
  have hiz : ⟪∑ i, u i, z⟫_ℝ = a⁻¹ * ‖∑ i, u i‖ ^ 2 := by
    simp only [z, real_inner_smul_right, inner_self_eq]
  have hnz : ‖z‖ ^ 2 = (a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2 := by
    exact square_smul a⁻¹ (∑ i, u i)
  rw [hiz, hnz] at hs
  have hbase :
      2 * a⁻¹ * ‖∑ i, u i‖ ^ 2 - a * ((a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2) ≤
        ∑ i, w i * ‖u i‖ ^ 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt ha)
  have hcancel :
      a * (2 * a⁻¹ * ‖∑ i, u i‖ ^ 2 -
        a * ((a⁻¹) ^ 2 * ‖∑ i, u i‖ ^ 2)) = ‖∑ i, u i‖ ^ 2 := by
    field_simp [ne_of_gt ha]
    <;> ring
  rw [hcancel] at hscaled
  exact hscaled

lemma weighted_cauchy_schwarz_mean {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (u : Fin n → E) :
    ‖(n : ℝ)⁻¹ • ∑ i, u i‖ ^ 2 ≤
      ((n : ℝ)⁻¹ * ∑ i, (w i)⁻¹) *
        ((n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := weighted_cauchy_schwarz w hw u
  rw [square_smul]
  have hs := mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ)⁻¹))
  calc
    (n : ℝ)⁻¹ ^ 2 * ‖∑ i, u i‖ ^ 2 ≤
        (n : ℝ)⁻¹ ^ 2 * ((∑ i, (w i)⁻¹) * ∑ i, w i * ‖u i‖ ^ 2) := hs
    _ = ((n : ℝ)⁻¹ * ∑ i, (w i)⁻¹) *
        ((n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2) := by ring

lemma weight_properties {M l : ℝ} (hM : 0 < M) (hl : 0 ≤ l) :
    0 < M / (M + l) ∧ M / (M + l) ≤ 1 ∧
      M / (M + l) * l ≤ M ∧ (M / (M + l))⁻¹ = 1 + l / M := by
  have hden : 0 < M + l := by linarith
  refine ⟨div_pos hM hden, ?_, ?_, ?_⟩
  · exact (div_le_one hden).2 (by linarith)
  · apply (mul_le_mul_right hden).mp
    have heq : M / (M + l) * l * (M + l) = M * l := by
      field_simp [ne_of_gt hden]
      <;> ring
    rw [heq]
    nlinarith [sq_nonneg M]
  · field_simp [ne_of_gt hM, ne_of_gt hden]
    <;> ring

lemma inverse_weight_average {n : ℕ} (hn : 0 < n)
    {M : ℝ} (hM : 0 < M) (l : Fin n → ℝ)
    (hl : ∀ i, 0 ≤ l i)
    (hmean : (n : ℝ)⁻¹ * ∑ i, l i ≤ M) :
    (n : ℝ)⁻¹ * ∑ i, (M / (M + l i))⁻¹ ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hid :
      (n : ℝ)⁻¹ * ∑ i, (M / (M + l i))⁻¹ =
        1 + ((n : ℝ)⁻¹ * ∑ i, l i) / M := by
    simp_rw [(weight_properties hM (hl _)).2.2.2]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← Finset.sum_div]
    field_simp [ne_of_gt hnR, ne_of_gt hM]
    <;> ring
  rw [hid]
  have hq : ((n : ℝ)⁻¹ * ∑ i, l i) / M ≤ 1 :=
    (div_le_one hM).2 hmean
  linarith

lemma aggregate_error_bound {n : ℕ} (hn : 0 < n)
    {M : ℝ} (hM : 0 < M) (l : Fin n → ℝ)
    (hl : ∀ i, 0 ≤ l i)
    (hmean : (n : ℝ)⁻¹ * ∑ i, l i ≤ M) (u : Fin n → E) :
    ‖(n : ℝ)⁻¹ • ∑ i, u i‖ ^ 2 ≤
      2 * ((n : ℝ)⁻¹ * ∑ i, M / (M + l i) * ‖u i‖ ^ 2) := by
  have hw : ∀ i, 0 < M / (M + l i) := fun i => (weight_properties hM (hl i)).1
  have hcs := weighted_cauchy_schwarz_mean hn (fun i => M / (M + l i)) hw u
  have hinv := inverse_weight_average hn hM l hl hmean
  have hsum : 0 ≤ (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * ‖u i‖ ^ 2 := by
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hw i)) (sq_nonneg ‖u i‖)
  exact hcs.trans (mul_le_mul_of_nonneg_right hinv hsum)

lemma weighted_local_interpolation {n : ℕ} (hn : 0 < n)
    {M gap : ℝ} (hM : 0 < M)
    (l d q : Fin n → ℝ) (hl : ∀ i, 0 ≤ l i) (hd : ∀ i, 0 ≤ d i)
    (hlocal : ∀ i, q i ≤ 2 * l i * d i)
    (hgap : (n : ℝ)⁻¹ * ∑ i, d i ≤ gap) :
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * q i ≤ 2 * M * gap := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpoint : ∀ i, M / (M + l i) * q i ≤ 2 * M * d i := by
    intro i
    obtain ⟨hw, _, hwl, _⟩ := weight_properties hM (hl i)
    have h₁ := mul_le_mul_of_nonneg_left (hlocal i) (le_of_lt hw)
    have h₂ := mul_le_mul_of_nonneg_right hwl (hd i)
    nlinarith
  calc
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * q i ≤
        (n : ℝ)⁻¹ * ∑ i, 2 * M * d i := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hnR))
      exact Finset.sum_le_sum (fun i hi => hpoint i)
    _ = 2 * M * ((n : ℝ)⁻¹ * ∑ i, d i) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * M * gap := mul_le_mul_of_nonneg_left hgap (by positivity)

lemma weighted_variance_bound {n : ℕ} {M variance : ℝ}
    (hM : 0 < M) (hvariance : 0 ≤ variance)
    (l noise : Fin n → ℝ) (hl : ∀ i, 0 ≤ l i)
    (hnoise : ∀ i, noise i ≤ variance) :
    (n : ℝ)⁻¹ * ∑ i, M / (M + l i) * noise i ≤ variance := by
  by_cases hn : n = 0
  · subst n
    simpa using hvariance
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpoint : ∀ i, M / (M + l i) * noise i ≤ variance := by
    intro i
    obtain ⟨hw, hw1, _, _⟩ := weight_properties hM (hl i)
    calc
      M / (M + l i) * noise i ≤ M / (M + l i) * variance :=
        mul_le_mul_of_nonneg_left (hnoise i) (le_of_lt hw)
      _ ≤ 1 * variance := mul_le_mul_of_nonneg_right hw1 hvariance
      _ = variance := one_mul _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (le_of_lt hnR))
  simpa [ne_of_gt hnR] using hm

lemma momentum_square_bound (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (m g gstar b : E) :
    ‖((1 - α) • m + α • (g + b)) - gstar‖ ^ 2 ≤
      (1 - α) * ‖m - gstar‖ ^ 2 + 2 * α * ‖g - gstar‖ ^ 2 +
        2 * α * ‖b‖ ^ 2 := by
  have hv : ((1 - α) • m + α • (g + b)) - gstar =
      (1 - α) • (m - gstar) + α • ((g - gstar) + b) := by
    simp only [smul_sub, smul_add, sub_smul, one_smul]
    abel
  rw [hv]
  have h₁ := square_convex_combination α hα hα1 (m - gstar) ((g - gstar) + b)
  have h₂ := mul_le_mul_of_nonneg_left (square_two (g - gstar) b) hα
  nlinarith [h₁, h₂]

lemma compressor_split (δ α : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (u z : E) :
    (1 - δ) * ‖u + α • z‖ ^ 2 ≤
      (1 - δ / 2) * ‖u‖ ^ 2 + 2 * α ^ 2 / δ * ‖z‖ ^ 2 := by
  have hy := twice_inner_young (δ / 2) (by positivity) u (α • z)
  rw [square_smul] at hy
  have hbase : ‖u + α • z‖ ^ 2 ≤
      (1 + δ / 2) * ‖u‖ ^ 2 + (1 + 2 / δ) * α ^ 2 * ‖z‖ ^ 2 := by
    have hinv : (δ / 2)⁻¹ = 2 / δ := by field_simp; ring
    rw [hinv] at hy
    rw [square_add]
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hδ1)
  have hc₁ : (1 - δ) * (1 + δ / 2) ≤ 1 - δ / 2 := by nlinarith [sq_nonneg δ]
  have hc₂ : (1 - δ) * (1 + 2 / δ) ≤ 2 / δ := by
    apply (mul_le_mul_right hδ).mp
    field_simp [ne_of_gt hδ]
    <;> nlinarith [sq_nonneg δ]
  have ht₁ := mul_le_mul_of_nonneg_right hc₁ (sq_nonneg ‖u‖)
  have ht₂ := mul_le_mul_of_nonneg_right hc₂
    (mul_nonneg (sq_nonneg α) (sq_nonneg ‖z‖))
  nlinarith [hs, ht₁, ht₂]

lemma compression_square_bound (δ α : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (m v g gstar b : E) :
    (1 - δ) * ‖m - v + α • (g - m + b)‖ ^ 2 ≤
      (1 - δ / 2) * ‖v - m‖ ^ 2 +
        6 * α ^ 2 / δ * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2) := by
  have hs := compressor_split δ α hδ hδ1 (m - v) (g - m + b)
  have hv : g - m + b = -(m - gstar) + (g - gstar) + b := by abel
  have ht : ‖g - m + b‖ ^ 2 ≤
      3 * (‖m - gstar‖ ^ 2 + ‖g - gstar‖ ^ 2 + ‖b‖ ^ 2) := by
    rw [hv]
    simpa only [norm_neg] using square_three (-(m - gstar)) (g - gstar) b
  rw [norm_sub_rev m v] at hs
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 2 * α ^ 2 / δ by positivity)
  nlinarith

end LongTails.Proofs.ProximalEf21WeightedErrors
