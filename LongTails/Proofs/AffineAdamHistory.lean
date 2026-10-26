import LongTails.Proofs.AdaptiveHistoryTracking

namespace LongTails.Proofs.AffineAdamHistory

open AdaptiveHistoryTracking AdaptiveHistoryFinite

lemma scalar_alignment {g m s M em ev : ℝ} (hs : 0 < s)
    (hem : 0 ≤ em) (hm : |m - g| ≤ em)
    (hv : s ≤ |g| + ev) (hbounded : |m| ≤ M * s) :
    |g| - (M + 2) * em - ev ≤ g * m / s := by
  have hmg : |g| ≤ |m| + em := by
    have h := abs_add_le m (g - m)
    rw [add_sub_cancel, abs_sub_comm g m] at h
    linarith
  have hmain : (|g| - 2 * em - ev) * s ≤ m ^ 2 := by
    by_cases hsign : |g| - 2 * em - ev ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hsign hs.le).trans (sq_nonneg m)
    have ha : 0 ≤ |g| - em := by linarith
    have hsq : (|g| - em) ^ 2 ≤ m ^ 2 := by
      have hab : |g| - em ≤ |m| := by linarith
      nlinarith [sq_abs m]
    have hmul := mul_le_mul_of_nonneg_left hv (by linarith : 0 ≤ |g| - 2 * em - ev)
    nlinarith [sq_nonneg (em + ev)]
  have herr : -em * (M * s) ≤ (g - m) * m := by
    have hprod := neg_abs_le ((g - m) * m)
    rw [abs_mul, abs_sub_comm g m] at hprod
    have hmul := mul_le_mul hm hbounded (abs_nonneg m) hem
    nlinarith
  apply (le_div_iff₀ hs).mpr
  nlinarith


lemma weighted_root_difference {ι : Type*} [Fintype ι] (b z w : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) :
    |Real.sqrt (∑ i, b i * z i ^ 2) - Real.sqrt (∑ i, b i * w i ^ 2)| ≤
      ∑ i, Real.sqrt (b i) * |z i - w i| := by
  have h := abs_norm_sub_norm_le (weightedVector b z) (weightedVector b w)
  rw [weightedVector_sub, weightedVector_norm b z hb, weightedVector_norm b w hb,
    weightedVector_norm b (fun i => z i - w i) hb] at h
  exact h.trans (weightedRoot_le b (fun i => z i - w i) hb)

lemma rms_transport {v z g old θ r : ℝ} (hv : 0 ≤ v)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr : Real.sqrt θ ≤ r) :
    |Real.sqrt (θ * v + (1 - θ) * z ^ 2) - (|g|)| ≤
      r * |Real.sqrt v - (|old|)| + r * |g - old| + |z - g| := by
  have h := weighted_root_difference (ι := Fin 2) ![θ, 1 - θ]
    ![Real.sqrt v, z] ![|g|, g] (by intro i; fin_cases i <;> simp <;> linarith)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sq_sqrt hv, sq_abs] at h
  rw [show θ * g ^ 2 + (1 - θ) * g ^ 2 = g ^ 2 by ring, Real.sqrt_sq_eq_abs] at h
  have hroot : Real.sqrt (1 - θ) ≤ 1 := (Real.sqrt_le_left (by norm_num)).mpr (by linarith)
  have htri : |Real.sqrt v - (|g|)| ≤ |Real.sqrt v - (|old|)| + |g - old| := by
    have hh := abs_sub_le (Real.sqrt v) |old| |g|
    have he := abs_abs_sub_abs_le_abs_sub old g
    rw [abs_sub_comm old g] at he
    linarith
  have hh := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg θ)
  have ht := mul_le_mul_of_nonneg_right hr
    (add_nonneg (abs_nonneg (Real.sqrt v - |old|)) (abs_nonneg (g - old)))
  have hz := mul_le_mul_of_nonneg_right hroot (abs_nonneg (z - g))
  nlinarith

lemma contraction_sum (E N D : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hE : ∀ t, 0 ≤ E t) (hinit : E 0 = 0)
    (hstep : ∀ t, E (t + 1) ≤ r * E t + r * D t + N t) (T : ℕ) :
    (∑ t ∈ Finset.range T, E (t + 1)) ≤
      (r * (∑ t ∈ Finset.range T, D t) + ∑ t ∈ Finset.range T, N t) / (1 - r) := by
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hstep t)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht := Finset.sum_range_succ' E T
  rw [Finset.sum_range_succ, hinit, add_zero] at ht
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  nlinarith [mul_nonneg hr (hE T)]

end LongTails.Proofs.AffineAdamHistory
