import LongTails.Proofs.RelativeHessianGate

namespace LongTails.Proofs.EscapeChainProfiles

open RelativeHessianGate

noncomputable def unit (t : ℝ) : ℝ := spline 4 t / 24
noncomputable def unit1 (t : ℝ) : ℝ := spline 3 t / 6
noncomputable def unit2 (t : ℝ) : ℝ := spline 2 t / 2
noncomputable def unit3 (t : ℝ) : ℝ := spline 1 t

lemma unit_contDiff : ContDiff ℝ 3 unit := by
  have hs := spline_contDiff 3
  unfold unit
  fun_prop

lemma unit_hasDerivAt (t : ℝ) : HasDerivAt unit (unit1 t) t := by
  have h := (spline_hasDerivAt 2 t).div_const 24
  convert h using 1
  · rfl
  · unfold unit1
    norm_num
    ring

lemma unit1_hasDerivAt (t : ℝ) : HasDerivAt unit1 (unit2 t) t := by
  have h := (spline_hasDerivAt 1 t).div_const 6
  convert h using 1
  · rfl
  · unfold unit2
    norm_num
    ring

lemma unit2_hasDerivAt (t : ℝ) : HasDerivAt unit2 (unit3 t) t := by
  have h := (spline_hasDerivAt 0 t).div_const 2
  convert h using 1
  · rfl
  · unfold unit3
    norm_num

lemma unit_flat {t : ℝ} (ht : t ≤ 0) :
    unit t = 0 ∧ unit1 t = 0 ∧ unit2 t = 0 ∧ unit3 t = 0 := by
  simp [unit, unit1, unit2, unit3, spline_zero (by norm_num : 4 ≠ 0) ht,
    spline_zero (by norm_num : 3 ≠ 0) ht, spline_zero (by norm_num : 2 ≠ 0) ht,
    spline_zero (by norm_num : 1 ≠ 0) ht]

lemma unit_full {t : ℝ} (ht : 4 ≤ t) :
    unit t = 1 ∧ unit1 t = 0 ∧ unit2 t = 0 ∧ unit3 t = 0 := by
  have h := spline_tail ht
  simp [unit, unit1, unit2, unit3, h.1, h.2.1, h.2.2.1, h.2.2.2]

lemma piece0 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    unit t = t ^ 4 / 24 ∧ unit1 t = t ^ 3 / 6 ∧ unit2 t = t ^ 2 / 2 ∧ unit3 t = t := by
  simp only [unit, unit1, unit2, unit3, spline, positivePower, max_eq_left h0,
    max_eq_right (show t - 1 ≤ 0 by linarith), max_eq_right (show t - 2 ≤ 0 by linarith),
    max_eq_right (show t - 3 ≤ 0 by linarith), max_eq_right (show t - 4 ≤ 0 by linarith)]
  norm_num

lemma piece1 {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) :
    unit t = (t ^ 4 - 4 * (t - 1) ^ 4) / 24 ∧ unit1 t = (t ^ 3 - 4 * (t - 1) ^ 3) / 6 ∧
      unit2 t = (t ^ 2 - 4 * (t - 1) ^ 2) / 2 ∧ unit3 t = t - 4 * (t - 1) := by
  simp only [unit, unit1, unit2, unit3, spline, positivePower, max_eq_left (show 0 ≤ t by linarith),
    max_eq_left (show 0 ≤ t - 1 by linarith), max_eq_right (show t - 2 ≤ 0 by linarith),
    max_eq_right (show t - 3 ≤ 0 by linarith), max_eq_right (show t - 4 ≤ 0 by linarith)]
  norm_num

lemma piece2 {t : ℝ} (h2 : 2 ≤ t) (h3 : t ≤ 3) :
    unit t = (t ^ 4 - 4 * (t - 1) ^ 4 + 6 * (t - 2) ^ 4) / 24 ∧
      unit1 t = (t ^ 3 - 4 * (t - 1) ^ 3 + 6 * (t - 2) ^ 3) / 6 ∧
      unit2 t = (t ^ 2 - 4 * (t - 1) ^ 2 + 6 * (t - 2) ^ 2) / 2 ∧
      unit3 t = t - 4 * (t - 1) + 6 * (t - 2) := by
  simp only [unit, unit1, unit2, unit3, spline, positivePower, max_eq_left (show 0 ≤ t by linarith),
    max_eq_left (show 0 ≤ t - 1 by linarith), max_eq_left (show 0 ≤ t - 2 by linarith),
    max_eq_right (show t - 3 ≤ 0 by linarith), max_eq_right (show t - 4 ≤ 0 by linarith)]
  norm_num

lemma piece3 {t : ℝ} (h3 : 3 ≤ t) (h4 : t ≤ 4) :
    unit t = (t ^ 4 - 4 * (t - 1) ^ 4 + 6 * (t - 2) ^ 4 - 4 * (t - 3) ^ 4) / 24 ∧
      unit1 t = (t ^ 3 - 4 * (t - 1) ^ 3 + 6 * (t - 2) ^ 3 - 4 * (t - 3) ^ 3) / 6 ∧
      unit2 t = (t ^ 2 - 4 * (t - 1) ^ 2 + 6 * (t - 2) ^ 2 - 4 * (t - 3) ^ 2) / 2 ∧
      unit3 t = t - 4 * (t - 1) + 6 * (t - 2) - 4 * (t - 3) := by
  simp only [unit, unit1, unit2, unit3, spline, positivePower, max_eq_left (show 0 ≤ t by linarith),
    max_eq_left (show 0 ≤ t - 1 by linarith), max_eq_left (show 0 ≤ t - 2 by linarith),
    max_eq_left (show 0 ≤ t - 3 by linarith), max_eq_right (show t - 4 ≤ 0 by linarith)]
  norm_num

lemma unit1_nonneg (t : ℝ) : 0 ≤ unit1 t := by
  unfold unit1
  have := spline_three_nonneg t
  positivity

lemma unit_monotone : Monotone unit :=
  monotone_of_hasDerivAt_nonneg unit_hasDerivAt unit1_nonneg

lemma unit_bounds (t : ℝ) : 0 ≤ unit t ∧ unit t ≤ 1 := by
  constructor
  · have h := unit_monotone (show min t 0 ≤ t from min_le_left _ _)
    rwa [(unit_flat (min_le_right t 0)).1] at h
  · have h := unit_monotone (show t ≤ max t 4 from le_max_left _ _)
    rwa [(unit_full (le_max_right t 4)).1] at h

lemma jets_bound (t : ℝ) : unit1 t ≤ 2 / 3 ∧ |unit2 t| ≤ 2 / 3 ∧ |unit3 t| ≤ 2 := by
  rcases le_or_gt t 0 with h0 | h0
  · obtain ⟨-, h1, h2, h3⟩ := unit_flat h0
    rw [h1, h2, h3]; norm_num
  rcases le_or_gt t 1 with h1 | h1
  · obtain ⟨-, e1, e2, e3⟩ := piece0 h0.le h1
    rw [e1, e2, e3, abs_le, abs_le]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [pow_le_one₀ h0.le h1 (n := 3)]
  rcases le_or_gt t 2 with h2 | h2
  · obtain ⟨-, e1, e2, e3⟩ := piece1 h1.le h2
    rw [e1, e2, e3, abs_le, abs_le]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (t - 4 / 3), sq_nonneg (t - 2),
      mul_pos (sub_pos.2 h1) (sub_pos.2 h1), sq_nonneg (t - 1)]
  rcases le_or_gt t 3 with h3 | h3
  · obtain ⟨-, e1, e2, e3⟩ := piece2 h2.le h3
    rw [e1, e2, e3, abs_le, abs_le]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (t - 8 / 3), sq_nonneg (t - 2),
      mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 h3), sq_nonneg (t - 3)]
  rcases le_or_gt t 4 with h4 | h4
  · obtain ⟨-, e1, e2, e3⟩ := piece3 h3.le h4
    rw [e1, e2, e3, abs_le, abs_le]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (t - 4), sq_nonneg (t - 3),
      mul_nonneg (sub_nonneg.2 h3.le) (sub_nonneg.2 h4)]
  · obtain ⟨-, e1, e2, e3⟩ := unit_full h4.le
    rw [e1, e2, e3]; norm_num

lemma curvature_ratio {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ 19 / 10) : unit1 t ≤ 4 * unit2 t := by
  rcases le_or_gt t 1 with h1 | h1
  · obtain ⟨-, e1, e2, -⟩ := piece0 h0 h1
    rw [e1, e2]
    nlinarith [sq_nonneg t]
  · obtain ⟨-, e1, e2, -⟩ := piece1 h1.le (by linarith)
    rw [e1, e2]
    nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h1), sq_nonneg (t - 1),
      mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h1.le), mul_nonneg (mul_nonneg (sub_nonneg.2 h)
        (sub_nonneg.2 h1.le)) (sub_nonneg.2 h1.le)]

lemma slope_ratio {t : ℝ} (h : 19 / 10 ≤ t) : 5 * unit1 t ≤ 8 * unit t := by
  rcases le_or_gt t 2 with h2 | h2
  · obtain ⟨e0, e1, -, -⟩ := piece1 (by linarith) h2
    rw [e0, e1]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h2), sq_nonneg (t - 1),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h2)) (sq_nonneg (t - 1))]
  rcases le_or_gt t 3 with h3 | h3
  · obtain ⟨e0, e1, -, -⟩ := piece2 h2.le h3
    rw [e0, e1]
    nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 h3), sq_nonneg (t - 2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 h3)) (sq_nonneg (t - 2)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2.le) (sub_nonneg.2 h2.le)) (sub_nonneg.2 h3)]
  rcases le_or_gt t 4 with h4 | h4
  · obtain ⟨e0, e1, -, -⟩ := piece3 h3.le h4
    rw [e0, e1]
    nlinarith [mul_nonneg (sub_nonneg.2 h3.le) (sub_nonneg.2 h4), sq_nonneg (t - 4),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h3.le) (sub_nonneg.2 h4)) (sq_nonneg (t - 4)),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h4)) (sub_nonneg.2 h4)]
  · obtain ⟨e0, e1, -, -⟩ := unit_full h4.le
    rw [e0, e1]; norm_num

lemma unit_at_eight_tenths : 1 / 60 ≤ unit (4 / 5) := by
  rw [(piece0 (by norm_num) (by norm_num)).1]; norm_num

lemma unit_at_nineteen_tenths : 2 / 5 ≤ unit (19 / 10) := by
  rw [(piece1 (by norm_num) (by norm_num)).1]; norm_num

end LongTails.Proofs.EscapeChainProfiles
