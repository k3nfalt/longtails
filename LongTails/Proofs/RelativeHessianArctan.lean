import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

namespace LongTails.Proofs.RelativeHessianArctan

noncomputable def profile (t : ℝ) : ℝ := Real.pi / 2 + Real.arctan t
noncomputable def density (t : ℝ) : ℝ := 1 / (1 + t ^ 2)
noncomputable def densitySlope (t : ℝ) : ℝ := -2 * t / (1 + t ^ 2) ^ 2
noncomputable def densityCurvature (t : ℝ) : ℝ := (6 * t ^ 2 - 2) / (1 + t ^ 2) ^ 3
noncomputable def slope (a t : ℝ) : ℝ := a * t - density t

lemma profile_contDiff : ContDiff ℝ 3 profile := contDiff_const.add Real.contDiff_arctan

lemma profile_derivative (t : ℝ) : HasDerivAt profile (density t) t :=
  (Real.hasDerivAt_arctan t).const_add _

lemma density_derivative (t : ℝ) : HasDerivAt density (densitySlope t) t := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_id t).pow 2 |>.const_add 1) ht using 1
  · funext x; rfl
  · simp [densitySlope, Pi.pow_apply]

lemma densitySlope_derivative (t : ℝ) : HasDerivAt densitySlope (densityCurvature t) t := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  convert ((hasDerivAt_id t).const_mul (-2)).div
    (((hasDerivAt_id t).pow 2 |>.const_add 1).pow 2) (pow_ne_zero 2 ht) using 1
  · rfl
  · simp only [densityCurvature, Pi.pow_apply, id_eq]
    field_simp
    ring

lemma profile_bounds (t : ℝ) : 0 < profile t ∧ profile t < Real.pi := by
  have h := Real.neg_pi_div_two_lt_arctan t
  have h' := Real.arctan_lt_pi_div_two t
  unfold profile
  constructor <;> linarith

lemma density_bounds (t : ℝ) : 0 < density t ∧ density t ≤ 1 := by
  unfold density
  refine ⟨by positivity, ?_⟩
  apply (div_le_one (by positivity : 0 < 1 + t ^ 2)).mpr
  nlinarith [sq_nonneg t]

lemma slope_factor {a b : ℝ} (hab : a * b * (1 + b ^ 2) = 1) (t : ℝ) :
    slope a t = a * (t - b) * (t ^ 2 + b * t + b ^ 2 + 1) / (1 + t ^ 2) := by
  unfold slope density
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp
  nlinarith [hab]

lemma curvature_factor {b : ℝ} (hb : b ^ 2 = 1 / 3) (t : ℝ) :
    densityCurvature t = 6 * (t - b) * (t + b) / (1 + t ^ 2) ^ 3 := by
  unfold densityCurvature
  congr 1
  nlinarith [hb]

lemma relative_curvature {a b : ℝ} (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb : b ^ 2 = 1 / 3) (hab : a * b * (1 + b ^ 2) = 1) (t : ℝ) :
    |densityCurvature t| ≤ 12 * |slope a t| := by
  have ht0 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have ht : 0 < 1 + t ^ 2 := by linarith
  have ha0 : 0 < a := by linarith
  have hQ : 1 ≤ t ^ 2 + b * t + b ^ 2 + 1 := by nlinarith [sq_nonneg (t + b / 2), sq_nonneg b]
  have habs : |t + b| ≤ 2 * (1 + t ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  rw [curvature_factor hb, slope_factor hab]
  simp only [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
    abs_of_nonneg ha0.le, abs_of_nonneg ht.le, abs_of_nonneg (show 0 ≤ t ^ 2 + b * t + b ^ 2 + 1 by linarith), abs_pow]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos ht 3) ht).mpr
  have hm := mul_le_mul_of_nonneg_left habs (show 0 ≤ 6 * |t - b| * (1 + t ^ 2) by positivity)
  have hprod : 1 ≤ a * (t ^ 2 + b * t + b ^ 2 + 1) * (1 + t ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hQ) ht0
  have hm2 := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 12 * |t - b| * (1 + t ^ 2) ^ 2 by positivity)
  nlinarith

noncomputable def balance : ℝ := Real.sqrt 3 / 3
noncomputable def coefficient : ℝ := 3 * Real.sqrt 3 / 4

lemma balance_parameters : 1 ≤ coefficient ∧ 0 ≤ balance ∧ balance ≤ 1 ∧
    balance ^ 2 = 1 / 3 ∧ coefficient * balance * (1 + balance ^ 2) = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  unfold coefficient balance
  refine ⟨by nlinarith, by positivity, by nlinarith, ?_, ?_⟩
  · nlinarith
  · have hb : (Real.sqrt 3 / 3) ^ 2 = (1 / 3 : ℝ) := by nlinarith
    rw [hb]
    nlinarith

lemma balanced_relative (t : ℝ) : |densityCurvature t| ≤ 12 * |slope coefficient t| := by
  obtain ⟨ha, hb0, hb1, hb, hab⟩ := balance_parameters
  exact relative_curvature ha hb0 hb1 hb hab t

lemma small_gradient {t : ℝ} (ht : |t| ≤ 1 / 5) : coefficient * t - density t ≤ -7 / 10 := by
  have ht' := abs_le.mp ht
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hco : 0 ≤ coefficient ∧ coefficient ≤ 13 / 10 := by unfold coefficient; constructor <;> nlinarith
  have hts : t ^ 2 ≤ 1 / 25 := by nlinarith
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hq : (25 / 26 : ℝ) ≤ density t := by
    unfold density
    apply (le_div_iff₀ hden).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_left ht'.2 hco.1
  nlinarith

lemma density_neg (t : ℝ) : density (-t) = density t := by simp [density]
lemma densitySlope_neg (t : ℝ) : densitySlope (-t) = -densitySlope t := by simp [densitySlope]; ring
lemma densityCurvature_neg (t : ℝ) : densityCurvature (-t) = densityCurvature t := by simp [densityCurvature]
lemma profile_neg (t : ℝ) : profile (-t) = Real.pi - profile t := by simp [profile]; ring

lemma profile_jet_bounds (t : ℝ) : |density t| ≤ 1 ∧ |densitySlope t| ≤ 2 ∧
    |densityCurvature t| ≤ 8 := by
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hab : |t| ≤ 1 + t ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hu : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  refine ⟨by rw [abs_of_pos (density_bounds t).1]; exact (density_bounds t).2, ?_, ?_⟩
  · unfold densitySlope
    rw [abs_div, abs_mul, abs_pow, abs_of_pos ht]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (pow_pos ht 2)).mpr
    nlinarith [sq_nonneg (t ^ 2)]
  · unfold densityCurvature
    rw [abs_div, abs_pow, abs_of_pos ht]
    apply (div_le_iff₀ (pow_pos ht 3)).mpr
    rw [abs_le]
    have h3 : (1 : ℝ) ≤ (1 + t ^ 2) ^ 3 := one_le_pow₀ hu
    have h23 : (1 + t ^ 2) ≤ (1 + t ^ 2) ^ 3 := le_self_pow₀ hu (by norm_num)
    constructor <;> nlinarith [sq_nonneg t]

end LongTails.Proofs.RelativeHessianArctan
