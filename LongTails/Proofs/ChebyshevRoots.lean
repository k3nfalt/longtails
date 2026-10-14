import LongTails.Algorithms.BatchedChebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace OracleTemplate.BatchedChebyshev

lemma angle_nonneg (T i : ℕ) :
    0 ≤ (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1) := by positivity

lemma angle_lt_half_pi {T i : ℕ} (hi : i ≤ T) :
    (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1) < Real.pi / 2 := by
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (T : ℝ) + 1)).mpr
  have hi' : (i : ℝ) ≤ T := by exact_mod_cast hi
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hi' Real.pi_pos.le]

lemma root_pos {T i : ℕ} (hi : 0 < i) (hiT : i ≤ T) : 0 < root T i := by
  apply sq_pos_of_pos
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos (by exact_mod_cast hi) Real.pi_pos) (by positivity)
  · exact (angle_lt_half_pi hiT).trans (by linarith [Real.pi_pos])

lemma root_nonneg (T i : ℕ) : 0 ≤ root T i := sq_nonneg _

lemma root_le_one (T i : ℕ) : root T i ≤ 1 := by
  have h := Real.abs_sin_le_one ((i : ℝ) * Real.pi / (2 * (T : ℝ) + 1))
  have := abs_le.mp h
  dsimp [root]
  nlinarith

lemma root_strictMono {T i j : ℕ} (hij : i < j) (hj : j ≤ T) :
    root T i < root T j := by
  have hi := angle_nonneg T i
  have hj' := angle_lt_half_pi hj
  have ha : (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1) <
      (j : ℝ) * Real.pi / (2 * (T : ℝ) + 1) := by
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) Real.pi_pos
  have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤
      (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1)) hj'.le ha
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hi
    ((angle_lt_half_pi (hij.le.trans hj)).le.trans (by linarith [Real.pi_pos]))
  dsimp [root]
  nlinarith

lemma root_lower {T i : ℕ} (hi : i ≤ T) :
    4 * (i : ℝ) ^ 2 / (2 * (T : ℝ) + 1) ^ 2 ≤ root T i := by
  have h := Real.mul_le_sin (angle_nonneg T i) (angle_lt_half_pi hi).le
  have heq : 2 / Real.pi * ((i : ℝ) * Real.pi / (2 * (T : ℝ) + 1)) =
      2 * (i : ℝ) / (2 * (T : ℝ) + 1) := by field_simp
  rw [heq] at h
  have hl : 0 ≤ 2 * (i : ℝ) / (2 * (T : ℝ) + 1) := by positivity
  have hs := sq_le_sq₀ hl (hl.trans h)
  have hh := hs.mpr h
  dsimp [root]
  convert hh using 1; simp only [div_pow, mul_pow]; norm_num

lemma root_upper {T i : ℕ} (hi : i ≤ T) :
    root T i ≤ 16 * (i : ℝ) ^ 2 / (2 * (T : ℝ) + 1) ^ 2 := by
  have hs := Real.sin_le (angle_nonneg T i)
  have hpi : (i : ℝ) * Real.pi / (2 * (T : ℝ) + 1) ≤
      4 * (i : ℝ) / (2 * (T : ℝ) + 1) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.pi_lt_four, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg T i)
    ((angle_lt_half_pi hi).le.trans (by linarith [Real.pi_pos]))
  have hh := (sq_le_sq₀ hs0 (show 0 ≤ 4 * (i : ℝ) /
    (2 * (T : ℝ) + 1) by positivity)).mpr (hs.trans hpi)
  dsimp [root]
  convert hh using 1; simp only [div_pow, mul_pow]; norm_num

lemma root_le_mul_root {T i j : ℕ} (hi : i ≤ T) (hj : j ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (hij : 4 * (i : ℝ) ^ 2 ≤ C * (j : ℝ) ^ 2) :
    root T i ≤ C * root T j := by
  have hm : 0 < (2 * (T : ℝ) + 1) ^ 2 := by positivity
  have hupper := (le_div_iff₀ hm).mp (root_upper hi)
  have hlower := (div_le_iff₀ hm).mp (root_lower hj)
  have hscale := mul_le_mul_of_nonneg_left hlower hC
  apply (mul_le_mul_iff_of_pos_right hm).mp
  nlinarith

end OracleTemplate.BatchedChebyshev
