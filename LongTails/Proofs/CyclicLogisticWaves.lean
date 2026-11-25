import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
import LongTails.Proofs.CyclicLogisticCoordinates

open scoped RealInnerProductSpace
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features ones shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Setups.CyclicLogisticFeatureLearning (sumFeature diffFeature)

namespace LongTails.Proofs.CyclicLogisticWaves

abbrev half (m : ℕ) := 2 * (m + 1)
abbrev dim (m : ℕ) := half m + half m

noncomputable def wave (m : ℕ) : Features (dim m) := WithLp.toLp 2
  fun i => if i.val < half m then (1 : ℝ) else -1

noncomputable def alternating (m : ℕ) : Features (dim m) := WithLp.toLp 2
  fun i => if i.val % 2 = 0 then (1 : ℝ) else -1

private lemma previous (m : ℕ) (i : Fin (dim m)) :
    ((finRotate (dim m)).symm i).val = if i.val = 0 then dim m - 1 else i.val - 1 := by
  have : NeZero (dim m) := ⟨by unfold dim half; omega⟩
  by_cases h : i = 0
  · subst i
    rw [finRotate_symm_apply, Fin.val_sub]
    simp only [Fin.val_zero, ↓reduceIte, Nat.add_zero]
    have h₁ : (1 : Fin (dim m)).val = 1 := by
      change (1 : ℕ) % dim m = 1
      apply Nat.mod_eq_of_lt; unfold dim half; omega
    rw [h₁, Nat.mod_eq_of_lt (by unfold dim half; omega)]
  · have hv : i.val ≠ (0 : ℕ) := fun e => h (Fin.ext e)
    rw [coe_finRotate_symm_of_ne_zero h, ite_eq_right hv]

lemma shift_alternating (m : ℕ) : shift (alternating m) = -(alternating m) := by
  ext i
  change (if ((finRotate _).symm i).val % 2 = 0 then (1 : ℝ) else -1) =
    -(if i.val % 2 = 0 then 1 else -1)
  rw [previous]
  unfold dim half
  split_ifs <;> norm_num <;> omega

lemma self_wave (m : ℕ) : ⟪wave m, wave m⟫ = (dim m : ℝ) := by
  rw [inner_eq_sum]
  calc
    _ = ∑ _ : Fin (dim m), (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
      change (if i.val < half m then (1 : ℝ) else -1) * _ = 1
      split <;> simp_all [wave]
    _ = _ := by simp

lemma self_alternating (m : ℕ) : ⟪alternating m, alternating m⟫ = (dim m : ℝ) := by
  rw [inner_eq_sum]
  calc
    _ = ∑ _ : Fin (dim m), (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
      change (if i.val % 2 = 0 then (1 : ℝ) else -1) * _ = 1
      split <;> simp_all [alternating]
    _ = _ := by simp

lemma dc_wave (m : ℕ) : ⟪ones (dim m), wave m⟫ = 0 := by
  rw [inner_eq_sum, Fin.sum_univ_add]
  have hl (i : Fin (half m)) : wave m (i.castAdd (half m)) = 1 := ite_eq_left i.isLt
  have hr (i : Fin (half m)) : wave m (Fin.natAdd (half m) i) = -1 :=
    ite_eq_right (by change ¬ half m + i.val < half m; omega)
  simp [ones_apply, hl, hr]

lemma dc_alternating (m : ℕ) : ⟪ones (dim m), alternating m⟫ = 0 := by
  have h := inner_shift_shift (ones (dim m)) (alternating m)
  rw [shift_ones, shift_alternating, inner_neg_right] at h
  linarith

lemma wave_alternating (m : ℕ) : ⟪wave m, alternating m⟫ = 0 := by
  rw [inner_eq_sum, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hl : wave m (i.castAdd (half m)) = 1 := ite_eq_left i.isLt
  have hr : wave m (Fin.natAdd (half m) i) = -1 := ite_eq_right (by change ¬ half m + i.val < half m; omega)
  have ha : alternating m (i.castAdd (half m)) = alternating m (Fin.natAdd (half m) i) := by
    change (if i.val % 2 = 0 then _ else _) = (if (half m + i.val) % 2 = 0 then _ else _)
    rw [show (half m + i.val) % 2 = i.val % 2 by unfold half; omega]
  rw [hl, hr, ha]; ring

lemma wave_difference (m : ℕ) : ‖wave m - shift (wave m)‖ ^ 2 = 8 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  let a : Fin (dim m) := ⟨0, by unfold dim half; omega⟩
  let b : Fin (dim m) := ⟨half m, by unfold dim half; omega⟩
  have hp (i : Fin (dim m)) : (wave m - shift (wave m)) i =
      (if i = a then 2 else 0) + (if i = b then -2 else 0) := by
    change (if i.val < half m then (1 : ℝ) else -1) -
      (if ((finRotate _).symm i).val < half m then 1 else -1) = _
    rw [previous]
    simp only [Fin.ext_iff, a, b]
    unfold dim half
    split_ifs <;> norm_num <;> omega
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b,half] at this; omega
  calc
    _ = ∑ i : Fin (dim m), ((if i = a then (4 : ℝ) else 0) + (if i = b then 4 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hp]; split_ifs <;> simp_all <;> norm_num
    _ = _ := by simp [Finset.sum_add_distrib]; norm_num

noncomputable def amplitude (m : ℕ) : ℝ := (Real.sqrt (dim m))⁻¹
noncomputable def dc (m : ℕ) := amplitude m • ones (dim m)
noncomputable def square (m : ℕ) := amplitude m • wave m
noncomputable def nyquist (m : ℕ) := amplitude m • alternating m

lemma amplitude_pos (m : ℕ) : 0 < amplitude m := by
  unfold amplitude dim half
  positivity

lemma amplitude_sq (m : ℕ) : amplitude m ^ 2 * dim m = 1 := by
  have hd : (0 : ℝ) < dim m := by unfold dim half; positivity
  rw [amplitude, inv_pow, Real.sq_sqrt hd.le, inv_mul_cancel₀ hd.ne']

lemma amplitude_le (m : ℕ) : amplitude m ≤ 1 / 2 := by
  rw [amplitude, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
  apply Real.le_sqrt_of_sq_le
  norm_num [dim, half]
  linarith [Nat.cast_nonneg m (α := ℝ)]

lemma modes (m : ℕ) : ⟪dc m, dc m⟫ = 1 ∧ ⟪square m, square m⟫ = 1 ∧
    ⟪nyquist m, nyquist m⟫ = 1 ∧ ⟪dc m, square m⟫ = 0 ∧ ⟪dc m, nyquist m⟫ = 0 ∧
    ⟪square m, nyquist m⟫ = 0 := by
  simp only [dc, square, nyquist, real_inner_smul_left, real_inner_smul_right, inner_ones_ones,
    self_wave, self_alternating, dc_wave, dc_alternating, wave_alternating, mul_zero,
    ← mul_assoc, ← sq, amplitude_sq, and_self]

lemma dc_shift (m : ℕ) : shift (dc m) = dc m := by rw [dc, shift_smul, shift_ones]
lemma nyquist_shift (m : ℕ) : shift (nyquist m) = -nyquist m := by
  rw [nyquist, shift_smul, shift_alternating, smul_neg]

lemma square_diff (m : ℕ) : ‖diffFeature (square m)‖ = 2 * amplitude m := by
  have hd := wave_difference m
  have h : 0 ≤ amplitude m := (amplitude_pos m).le
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂' := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  unfold diffFeature square
  rw [shift_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr h₂'.le), abs_of_nonneg h]
  have he : ‖wave m - shift (wave m)‖ = 2 * Real.sqrt 2 := by
    nlinarith [norm_nonneg (wave m - shift (wave m))]
  rw [he]; field_simp

lemma feature_add {d : ℕ} (a b : Features d) :
    sumFeature (a+b) = sumFeature a + sumFeature b ∧ diffFeature (a+b) = diffFeature a + diffFeature b := by
  unfold sumFeature diffFeature
  rw [shift_add]
  constructor <;> module

lemma feature_smul {d : ℕ} (c : ℝ) (a : Features d) :
    sumFeature (c • a) = c • sumFeature a ∧ diffFeature (c • a) = c • diffFeature a := by
  unfold sumFeature diffFeature
  rw [shift_smul]
  constructor <;> module

lemma feature_eigen (m : ℕ) : sumFeature (dc m) = Real.sqrt 2 • dc m ∧
    diffFeature (dc m) = 0 ∧ sumFeature (nyquist m) = 0 ∧ diffFeature (nyquist m) = Real.sqrt 2 • nyquist m := by
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂' := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hc : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by field_simp; nlinarith
  simp [sumFeature, diffFeature, dc_shift, nyquist_shift, sub_neg_eq_add, ← two_smul ℝ, smul_smul, hc]

lemma norm_square_sum (m : ℕ) : 1 ≤ ‖sumFeature (square m)‖ ∧ ‖sumFeature (square m)‖ ≤ 2 := by
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂' := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hsq := (modes m).2.1
  rw [real_inner_self_eq_norm_sq] at hsq
  have h : ‖sumFeature (square m)‖ ^ 2 + ‖diffFeature (square m)‖ ^ 2 = 2 := by
    simp only [sumFeature, diffFeature, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h₂'),
      mul_pow, inv_pow, h₂, norm_add_sq_real, norm_sub_sq_real, norm_shift, hsq]
    ring
  rw [square_diff] at h
  have hd := amplitude_le m
  have ha := amplitude_pos m
  constructor <;> nlinarith [sq_nonneg (amplitude m),
    mul_nonneg (sub_nonneg.mpr hd) (show 0 ≤ 1 / 2 + amplitude m by linarith),
    norm_nonneg (sumFeature (square m))]

lemma orthogonal_modes (m : ℕ) :
    ⟪dc m, sumFeature (square m)⟫ = 0 ∧ ⟪dc m, diffFeature (square m)⟫ = 0 ∧
    ⟪sumFeature (square m), nyquist m⟫ = 0 ∧ ⟪diffFeature (square m), nyquist m⟫ = 0 ∧
    ⟪sumFeature (square m), diffFeature (square m)⟫ = 0 := by
  obtain ⟨_,_,_,hzc,_,hcv⟩ := modes m
  have h₁ := inner_shift_shift (dc m) (square m)
  rw [dc_shift, hzc] at h₁
  have h₂ := inner_shift_shift (square m) (nyquist m)
  rw [nyquist_shift, inner_neg_right, hcv] at h₂
  have he : ⟪shift (square m),nyquist m⟫ = 0 := by linarith
  simp only [sumFeature, diffFeature, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_left, inner_add_right, inner_sub_right, hzc, h₁, hcv, he,
    inner_shift_shift, real_inner_comm (shift (square m)) (square m)]
  norm_num
  ring

end LongTails.Proofs.CyclicLogisticWaves
