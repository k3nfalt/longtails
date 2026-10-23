import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.GaussianFacts

open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma sqrt_two_pi_ge : (5 : ℝ) / 2 ≤ Real.sqrt (2 * Real.pi) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [Real.pi_gt_d2]

lemma pdf_le (V : ℝ≥0) (hV : V ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 V x ≤ 2 / 5 / Real.sqrt V := by
  rw [gaussianPDFReal_def]
  have hVpos : (0 : ℝ) < V := by positivity
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have he : Real.exp (-(x - 0) ^ 2 / (2 * V)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - 0) ^ 2 / (2 * V) := by positivity
    linarith [neg_div (2 * (V : ℝ)) ((x - 0) ^ 2)]
  have hsq : Real.sqrt (2 * Real.pi * V) = Real.sqrt (2 * Real.pi) * Real.sqrt V := by
    rw [Real.sqrt_mul (by positivity)]
  have hpos : 0 < Real.sqrt (2 * Real.pi * V) := by positivity
  calc (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * V)) ≤
        (Real.sqrt (2 * Real.pi * V))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hpos.le)
    _ ≤ 2 / 5 / Real.sqrt V := by
          rw [mul_one, hsq, mul_inv, div_eq_mul_inv (2 / 5)]
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hs.le)
          rw [inv_le_comm₀ (by positivity) (by norm_num)]
          have := sqrt_two_pi_ge
          rw [inv_div]
          linarith

lemma small_ball (V : ℝ≥0) (hV : V ≠ 0) (a u : ℝ) (hu : 0 ≤ u) :
    (gaussianReal 0 V).real {y | |a + y| < u} ≤ 4 / 5 * u / Real.sqrt V := by
  have hset : {y : ℝ | |a + y| < u} = Set.Ioo (-a - u) (-a + u) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hV, hset,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo
      (fun x _ => gaussianPDFReal_nonneg _ _ _))]
  calc (∫ x in Set.Ioo (-a - u) (-a + u), gaussianPDFReal 0 V x) ≤
        ∫ _x in Set.Ioo (-a - u) (-a + u), 2 / 5 / Real.sqrt V :=
          setIntegral_mono_on (integrable_gaussianPDFReal 0 V).integrableOn
            (by simp) measurableSet_Ioo (fun x _ => pdf_le V hV x)
    _ = 4 / 5 * u / Real.sqrt V := by
          rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul]
          ring

lemma large_prob (V : ℝ≥0) (hV : V ≠ 0) (a u : ℝ) (hu : 0 ≤ u) :
    1 - 4 / 5 * u / Real.sqrt V ≤ (gaussianReal 0 V).real {y | u ≤ |a + y|} := by
  have hc : {y : ℝ | u ≤ |a + y|} = {y | |a + y| < u}ᶜ := by
    ext y; simp
  rw [hc, measureReal_compl (by
    have : Measurable (fun y : ℝ => |a + y|) := by fun_prop
    exact measurableSet_lt this measurable_const), probReal_univ]
  linarith [small_ball V hV a u hu]

lemma inv_max_interval {b σ : ℝ} (hb : 0 < b) (hbσ : b ≤ σ) :
    (∫ u in (-σ)..σ, 1 / max |u| b) = 2 + 2 * Real.log (σ / b) := by
  have heven : (∫ u in (-σ)..0, 1 / max |u| b) = ∫ u in (0 : ℝ)..σ, 1 / max |u| b := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := σ) (fun u : ℝ => 1 / max |u| b)
    simp only [abs_neg, neg_zero] at h
    exact h.symm
  have hcont : Continuous (fun u : ℝ => 1 / max |u| b) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro u
    exact (lt_max_of_lt_right hb).ne'
  have hi (x y : ℝ) : IntervalIntegrable (fun u : ℝ => 1 / max |u| b) volume x y :=
    hcont.intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-σ) 0) (hi 0 σ), heven]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 b) (hi b σ)]
  have h1 : (∫ u in (0 : ℝ)..b, 1 / max |u| b) = 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 1 / b)]
    · simp [hb.ne']
    · intro u hu
      rw [Set.uIcc_of_le hb.le] at hu
      simp only
      rw [max_eq_right (by rw [abs_of_nonneg hu.1]; exact hu.2)]
  have h2 : (∫ u in b..σ, 1 / max |u| b) = Real.log (σ / b) := by
    rw [intervalIntegral.integral_congr (g := fun u => u⁻¹)]
    · exact integral_inv_of_pos hb (hb.trans_le hbσ)
    · intro u hu
      rw [Set.uIcc_of_le hbσ] at hu
      simp only
      rw [max_eq_left (by rw [abs_of_nonneg (hb.le.trans hu.1)]; exact hu.1),
        abs_of_nonneg (hb.le.trans hu.1), one_div]
  rw [h1, h2]
  ring

lemma inv_max_integral (V : ℝ≥0) (hV : V ≠ 0) (a b : ℝ) (hb : 0 < b)
    (hbσ : b ≤ Real.sqrt V) :
    Integrable (fun y => 1 / max |a + y| b) (gaussianReal 0 V) ∧
    (∫ y, 1 / max |a + y| b ∂gaussianReal 0 V) ≤ (2 + Real.log (Real.sqrt V / b)) / Real.sqrt V := by
  set σ := Real.sqrt V with hσ
  have hσpos : 0 < σ := hb.trans_le hbσ
  have hmax (y : ℝ) : 0 < max |a + y| b := lt_max_of_lt_right hb
  have hcont : Continuous (fun y : ℝ => 1 / max |a + y| b) :=
    Continuous.div continuous_const (by fun_prop) (fun y => (hmax y).ne')
  have hbdd (y : ℝ) : 1 / max |a + y| b ≤ 1 / b :=
    one_div_le_one_div_of_le hb (le_max_right _ _)
  have hint : Integrable (fun y => 1 / max |a + y| b) (gaussianReal 0 V) :=
    Integrable.of_bound hcont.aestronglyMeasurable (1 / b) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hbdd y)
  refine ⟨hint, ?_⟩
  let S := Set.Icc (-σ) σ
  let g := fun u : ℝ => 1 / max |u| b
  have hsplit (y : ℝ) : 1 / max |a + y| b ≤ 1 / σ + S.indicator g (a + y) := by
    by_cases hy : a + y ∈ S
    · rw [Set.indicator_of_mem hy]
      have : 0 ≤ 1 / σ := by positivity
      linarith
    · rw [Set.indicator_of_notMem hy]
      have hy' : σ < |a + y| := by
        simp only [S, Set.mem_Icc, not_and_or, not_le] at hy
        rcases hy with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      have : 1 / max |a + y| b ≤ 1 / σ :=
        one_div_le_one_div_of_le hσpos (le_trans hy'.le (le_max_left _ _))
      linarith
  have hgc : Continuous g := Continuous.div continuous_const (by fun_prop)
    (fun u => (lt_max_of_lt_right hb).ne')
  have hgS : Integrable (S.indicator g) :=
    (hgc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hgSm : Measurable (S.indicator g) := hgc.measurable.indicator measurableSet_Icc
  have hgSshift : Integrable (fun y => S.indicator g (a + y)) (gaussianReal 0 V) := by
    apply Integrable.of_bound (hgSm.comp (measurable_const_add a)).aestronglyMeasurable (1 / b)
    exact Filter.Eventually.of_forall fun y => by
      show ‖S.indicator g (a + y)‖ ≤ 1 / b
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (by positivity)]
        exact one_div_le_one_div_of_le hb (le_max_right _ _)
      · rw [Set.indicator_of_notMem hy, norm_zero]; positivity
  have hstep1 := integral_mono hint ((integrable_const (1 / σ)).add hgSshift) hsplit
  simp only [Pi.add_apply] at hstep1
  rw [integral_add (integrable_const _) hgSshift, integral_const, probReal_univ, one_smul]
    at hstep1
  have hstep2 : (∫ y, S.indicator g (a + y) ∂gaussianReal 0 V) ≤
      2 / 5 / σ * ∫ u, S.indicator g u := by
    rw [integral_gaussianReal_eq_integral_smul hV]
    have hle : ∀ y, gaussianPDFReal 0 V y • S.indicator g (a + y) ≤
        2 / 5 / σ * S.indicator g (a + y) := by
      intro y
      rw [smul_eq_mul]
      apply mul_le_mul_of_nonneg_right (pdf_le V hV y)
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem hy]; positivity
      · rw [Set.indicator_of_notMem hy]
    have hshift : Integrable (fun y => S.indicator g (a + y)) :=
      hgS.comp_add_left a
    calc (∫ y, gaussianPDFReal 0 V y • S.indicator g (a + y)) ≤
          ∫ y, 2 / 5 / σ * S.indicator g (a + y) := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun y => by
                show 0 ≤ gaussianPDFReal 0 V y • S.indicator g (a + y)
                rw [smul_eq_mul]
                apply mul_nonneg (gaussianPDFReal_nonneg _ _ _)
                by_cases hy : a + y ∈ S
                · rw [Set.indicator_of_mem hy]; positivity
                · rw [Set.indicator_of_notMem hy]
            · exact hshift.const_mul _
            · exact Filter.Eventually.of_forall hle
      _ = 2 / 5 / σ * ∫ u, S.indicator g u := by
            rw [integral_const_mul, integral_add_left_eq_self (fun u => S.indicator g u) a]
  have hS : (∫ u, S.indicator g u) = 2 + 2 * Real.log (σ / b) := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
    exact inv_max_interval hb hbσ
  rw [hS] at hstep2
  have hlog : 0 ≤ Real.log (σ / b) := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
  have hfinal : 1 / σ + 2 / 5 / σ * (2 + 2 * Real.log (σ / b)) ≤ (2 + Real.log (σ / b)) / σ := by
    rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hσpos]
    nlinarith
  linarith

end LongTails.Proofs.GaussianFacts
