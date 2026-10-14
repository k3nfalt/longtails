import LongTails.Algorithms.Clipping
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.GeneralNormClipping

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_le {B : ℝ} (hB : 0 ≤ B) (v : E) : ‖clip B v‖ ≤ B := by
  unfold clip
  split_ifs with h
  · exact h
  · have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hv.ne']

lemma residual_norm {B : ℝ} (hB : 0 ≤ B) (v : E) :
    ‖v - clip B v‖ = max 0 (‖v‖ - B) := by
  unfold clip
  split_ifs with h
  · simp [max_eq_left (sub_nonpos.mpr h)]
  · have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
    rw [show v - (B / ‖v‖) • v = (1 - B / ‖v‖) • v by
      rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by
      rw [sub_nonneg, div_le_iff₀ hv]
      simpa using (lt_of_not_ge h).le), max_eq_right (by linarith)]
    field_simp

lemma difference_ordered {B : ℝ} (hB : 0 ≤ B) (v w : E)
    (hvw : ‖v‖ ≤ ‖w‖) : ‖clip B v - clip B w‖ ≤ 2 * ‖v - w‖ := by
  by_cases hw : ‖w‖ ≤ B
  · simp only [clip, ite_eq_left hw, ite_eq_left (hvw.trans hw)]
    linarith [norm_nonneg (v - w)]
  have hwpos : 0 < ‖w‖ := lt_of_le_of_lt hB (lt_of_not_ge hw)
  by_cases hv : ‖v‖ ≤ B
  · rw [clip, ite_eq_left hv]
    have ht := norm_add_le (v - w) (w - clip B w)
    rw [sub_add_sub_cancel, residual_norm hB,
      max_eq_right (by linarith : 0 ≤ ‖w‖ - B)] at ht
    have hn := norm_sub_norm_le w v
    rw [norm_sub_rev w v] at hn
    linarith
  have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge hv)
  have hr : 0 ≤ B / ‖v‖ - B / ‖w‖ :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left hB hvpos hvw)
  have he : clip B v - clip B w = (B / ‖w‖) • (v - w) +
      (B / ‖v‖ - B / ‖w‖) • v := by
    simp only [clip, ite_eq_right hv, ite_eq_right hw]
    rw [smul_sub, sub_smul]
    abel
  rw [he]
  have ht := norm_add_le ((B / ‖w‖) • (v - w))
    ((B / ‖v‖ - B / ‖w‖) • v)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hB hwpos.le), abs_of_nonneg hr] at ht
  have heq : (B / ‖v‖ - B / ‖w‖) * ‖v‖ =
      (B / ‖w‖) * (‖w‖ - ‖v‖) := by
    field_simp

  rw [heq] at ht
  have hn := norm_sub_norm_le w v
  rw [norm_sub_rev w v] at hn
  have hs := mul_le_mul_of_nonneg_left hn (div_nonneg hB hwpos.le)
  have hc : B / ‖w‖ ≤ 1 := (div_le_one hwpos).mpr (lt_of_not_ge hw).le
  have hd := mul_le_mul_of_nonneg_right hc (norm_nonneg (v - w))
  linarith

lemma difference {B : ℝ} (hB : 0 ≤ B) (v w : E) :
    ‖clip B v - clip B w‖ ≤ 2 * ‖v - w‖ := by
  rcases le_total ‖v‖ ‖w‖ with h | h
  · exact difference_ordered hB v w h
  · simpa only [norm_sub_rev] using difference_ordered hB w v h

lemma difference_capped {B : ℝ} (hB : 0 ≤ B) (v w : E) :
    ‖clip B v - clip B w‖ ≤ 2 * min ‖v - w‖ B := by
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact le_min (difference hB v w)
    ((norm_sub_le _ _).trans (by linarith [norm_le hB v, norm_le hB w]))

lemma norm_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → E}
    (hF : Integrable F P) (hF2 : Integrable (fun ω => ‖F ω‖ ^ 2) P) :
    ‖∫ ω, F ω ∂P‖ ^ 2 ≤ ∫ ω, ‖F ω‖ ^ 2 ∂P := by
  let m := ∫ ω, ‖F ω‖ ∂P
  have hm : 0 ≤ m := integral_nonneg (fun _ => norm_nonneg _)
  have hvar : 0 ≤ (∫ ω, (‖F ω‖ ^ 2 - 2 * m * ‖F ω‖ + m ^ 2) ∂P) :=
    integral_nonneg (fun ω => by
      change 0 ≤ ‖F ω‖ ^ 2 - 2 * m * ‖F ω‖ + m ^ 2
      nlinarith [sq_nonneg (‖F ω‖ - m)])
  have hi : Integrable (fun ω => ‖F ω‖ ^ 2 - 2 * m * ‖F ω‖) P :=
    hF2.sub (hF.norm.const_mul (2 * m))
  rw [integral_add hi (integrable_const (m ^ 2)),
    integral_sub hF2 (hF.norm.const_mul (2 * m)), integral_const_mul,
    integral_const] at hvar
  simp only [probReal_univ, smul_eq_mul, one_mul] at hvar
  have hnorm := norm_integral_le_integral_norm (μ := P) F
  change ‖∫ ω, F ω ∂P‖ ≤ m at hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  change 0 ≤ (∫ ω, ‖F ω‖ ^ 2 ∂P) - 2 * m * m + m ^ 2 at hvar
  nlinarith

lemma difference_sq_score {B : ℝ} (hB : 0 < B) (v w : E) :
    ‖clip B v - clip B w‖ ^ 2 ≤ 4 * B ^ 2 * min 1 (‖v - w‖ ^ 2 / B ^ 2) := by
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  by_cases hd : ‖v - w‖ ≤ B
  · have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [min_eq_right ((div_le_one hB2).mpr hd2)]
    have h := pow_le_pow_left₀ (norm_nonneg _) (difference hB.le v w) 2
    calc
      _ ≤ 4 * ‖v - w‖ ^ 2 := by nlinarith
      _ = _ := by field_simp
  · have hd2 : B ^ 2 ≤ ‖v - w‖ ^ 2 :=
      pow_le_pow_left₀ hB.le (lt_of_not_ge hd).le 2
    rw [min_eq_left ((le_div_iff₀ hB2).mpr (by simpa using hd2)), mul_one]
    have hb : ‖clip B v - clip B w‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [norm_le hB.le v, norm_le hB.le w])
    have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith

variable [SecondCountableTopology E]

lemma measurable_clip [MeasurableSpace E] [BorelSpace E] (B : ℝ) :
    Measurable (clip (E := E) B) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    ((measurable_const.div measurable_norm).smul measurable_id)

lemma integrable_clip {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → E} (hG : Measurable G)
    {B : ℝ} (hB : 0 ≤ B) : Integrable (fun ω => clip B (G ω)) P :=
  Integrable.of_bound ((measurable_clip B).comp hG).aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun ω => norm_le hB (G ω)))

lemma clipped_centered_sq_le_twin {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → E} (hG : Measurable G)
    {B : ℝ} (hB : 0 < B) (v : E) :
    ‖clip B v - ∫ ω, clip B (G ω) ∂P‖ ^ 2 ≤
      4 * B ^ 2 * ∫ ω, min 1 (‖v - G ω‖ ^ 2 / B ^ 2) ∂P := by
  have hclip := integrable_clip (P := P) hG hB.le
  have hd : Integrable (fun ω => clip B v - clip B (G ω)) P :=
    (integrable_const _).sub hclip
  have hdm : Measurable (fun ω => clip B v - clip B (G ω)) :=
    measurable_const.sub ((measurable_clip B).comp hG)
  have hb (ω : Ω) : ‖clip B v - clip B (G ω)‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [norm_le hB.le v, norm_le hB.le (G ω)])
  have hd2 : Integrable (fun ω => ‖clip B v - clip B (G ω)‖ ^ 2) P := by
    apply Integrable.of_bound (hdm.norm.pow_const 2).aestronglyMeasurable (4 * B ^ 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2
    nlinarith
  have hsm : Measurable (fun ω => min 1 (‖v - G ω‖ ^ 2 / B ^ 2)) := by fun_prop
  have hs : Integrable (fun ω => min 1 (‖v - G ω‖ ^ 2 / B ^ 2)) P := by
    apply Integrable.of_bound hsm.aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact min_le_left _ _
  have hj := norm_integral_sq_le hd hd2
  rw [integral_sub (integrable_const _) hclip, integral_const] at hj
  simp only [probReal_univ, one_smul] at hj
  have hp := integral_mono hd2 (hs.const_mul (4 * B ^ 2))
    (fun ω => difference_sq_score hB v (G ω))
  rw [integral_const_mul] at hp
  exact hj.trans hp

lemma capped_square_le_rpow {a B p : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    B ^ 2 * min 1 (a ^ 2 / B ^ 2) ≤ B ^ (2 - p) * a ^ p := by
  have hr : 0 ≤ a / B := div_nonneg ha hB.le
  have hs : min 1 (a ^ 2 / B ^ 2) ≤ (a / B) ^ p := by
    by_cases h : a ≤ B
    · have hpow := Real.rpow_le_rpow_of_exponent_ge' hr ((div_le_one hB).mpr h) hp hp2
      have he : a ^ 2 / B ^ 2 = (a / B) ^ (2 : ℝ) := by rw [Real.rpow_two, div_pow]
      exact (min_le_right _ _).trans (he.le.trans hpow)
    · have hpow := Real.rpow_le_rpow_of_exponent_le
        ((one_le_div hB).mpr (le_of_not_ge h)) hp
      simp only [Real.rpow_zero] at hpow
      exact (min_le_left _ _).trans hpow
  have ht := mul_le_mul_of_nonneg_left hs (sq_nonneg B)
  have he : B ^ 2 * (a / B) ^ p = B ^ (2 - p) * a ^ p := by
    rw [Real.div_rpow ha hB.le, Real.rpow_sub hB, Real.rpow_two]
    ring
  exact he ▸ ht

omit [SecondCountableTopology E] in
lemma difference_sq_moment {B p : ℝ} (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (v w : E) :
    ‖clip B v - clip B w‖ ^ 2 ≤ 4 * B ^ (2 - p) * ‖v - w‖ ^ p := by
  have h := mul_le_mul_of_nonneg_left
    (capped_square_le_rpow (norm_nonneg (v - w)) hB hp hp2) (by norm_num : (0 : ℝ) ≤ 4)
  exact (difference_sq_score hB v w).trans (by nlinarith)

end OracleTemplate.GeneralNormClipping
