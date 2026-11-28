import LongTails.Proofs.AbcHardOracle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedHighProbabilityMoments

open LongTails.Proofs.AbcHardOracle

noncomputable def tailRatio (p σ a : ℝ) : ℝ := (σ ^ p / (2 * a ^ p)) ^ (1 / (p - 1))

lemma tailRatio_nonneg (p σ a : ℝ) (hσ : 0 ≤ σ) (ha : 0 ≤ a) : 0 ≤ tailRatio p σ a := by
  unfold tailRatio
  exact Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hσ _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ha _))) _

lemma tailRatio_rpow (p σ a : ℝ) (hp : 1 < p) (hσ : 0 ≤ σ) (ha : 0 < a) :
    tailRatio p σ a ^ (p - 1) * (2 * a ^ p) = σ ^ p := by
  unfold tailRatio
  have hx : 0 ≤ σ ^ p / (2 * a ^ p) :=
    div_nonneg (Real.rpow_nonneg hσ _) (mul_nonneg (by norm_num) (Real.rpow_nonneg ha.le _))
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
  have : 0 < 2 * a ^ p := by have := Real.rpow_pos_of_pos ha p; positivity
  field_simp

lemma tailRatio_ge (p σ a : ℝ) (hp : 1 < p) (hσ : 0 ≤ σ) (ha : 0 < a) :
    (σ / (2 * a)) ^ (p / (p - 1)) ≤ tailRatio p σ a := by
  unfold tailRatio
  have hp1 : 0 < p - 1 := by linarith
  have hb : 0 ≤ σ / (2 * a) := by positivity
  have hrw : (σ / (2 * a)) ^ (p / (p - 1)) = ((σ / (2 * a)) ^ p) ^ (1 / (p - 1)) := by
    rw [← Real.rpow_mul hb]
    congr 1
    field_simp
  rw [hrw]
  refine Real.rpow_le_rpow (Real.rpow_nonneg hb _) ?_ (by positivity)
  rw [Real.div_rpow hσ (by positivity), Real.mul_rpow (by norm_num) ha.le]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hσ _)
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos ha _))
  have h2 : (2 : ℝ) ≤ 2 ^ p := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
      _ ≤ 2 ^ p := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp.le
  have hap := Real.rpow_pos_of_pos ha p
  nlinarith

lemma coin_sub_one_rpow (q p ω : ℝ) :
    |coin q ω - 1| ^ p =
      Set.indicator {ω | ω ≤ q} (fun _ => |1 / q - 1| ^ p) ω +
        Set.indicator {ω | q < ω} (fun _ => (1 : ℝ)) ω := by
  by_cases h : ω ≤ q
  · have h' : ¬ q < ω := not_lt.mpr h
    simp [coin, Set.indicator, h, h']
  · have h' : q < ω := lt_of_not_ge h
    simp [coin, Set.indicator, h, h', Real.one_rpow]

lemma coin_rpow_integrable (q p : ℝ) :
    Integrable (fun ω => |coin q ω - 1| ^ p) unif := by
  have he : (fun ω => |coin q ω - 1| ^ p) = fun ω =>
      Set.indicator {ω | ω ≤ q} (fun _ => |1 / q - 1| ^ p) ω +
        Set.indicator {ω | q < ω} (fun _ => (1 : ℝ)) ω := funext fun ω => coin_sub_one_rpow q p ω
  rw [he]
  exact ((integrable_const _).indicator (setOf_le_measurable q)).add
    ((integrable_const _).indicator (measurableSet_Ioi (a := q)))

lemma coin_rpow_integral (t p : ℝ) (ht : 0 ≤ t) (hp : 1 < p) (hp2 : p ≤ 2) :
    ∫ ω, |coin (1 / (1 + t)) ω - 1| ^ p ∂unif ≤ 2 * t ^ (p - 1) := by
  set q : ℝ := 1 / (1 + t) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  have hp0 : 0 < p := by linarith
  have hinv : 1 / q - 1 = t := by rw [hq]; field_simp; ring
  have he : (fun ω => |coin q ω - 1| ^ p) = fun ω =>
      Set.indicator {ω | ω ≤ q} (fun _ => |1 / q - 1| ^ p) ω +
        Set.indicator {ω | q < ω} (fun _ => (1 : ℝ)) ω := funext fun ω => coin_sub_one_rpow q p ω
  have hlow : unif.real {ω | ω ≤ q} = q := unif_real_le q hq0.le hq1
  have hhigh : unif.real {ω : ℝ | q < ω} = 1 - q := by
    have hc : {ω : ℝ | q < ω} = {ω | ω ≤ q}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [hc, measureReal_compl (setOf_le_measurable q), probReal_univ, hlow]
  rw [he, integral_add ((integrable_const _).indicator (setOf_le_measurable q))
      ((integrable_const _).indicator (measurableSet_Ioi (a := q))),
    integral_indicator (setOf_le_measurable q), integral_indicator (s := {ω : ℝ | q < ω}) measurableSet_Ioi,
    setIntegral_const, setIntegral_const, hlow, hhigh, hinv, abs_of_nonneg ht, smul_eq_mul,
    smul_eq_mul, mul_one]
  have hqt : q * t = 1 - q := by rw [hq]; field_simp; ring
  have htp : t ^ p = t * t ^ (p - 1) := by
    rcases eq_or_lt_of_le ht with h0 | hpos
    · rw [← h0, Real.zero_rpow hp0.ne', Real.zero_rpow (by linarith), mul_zero]
    · rw [← Real.rpow_one_add' hpos.le (by linarith)]
      congr 1; ring
  have hfirst : t ^ p * q ≤ t ^ (p - 1) := by
    have h1 : t ^ p * q = t ^ (p - 1) * (q * t) := by rw [htp]; ring
    rw [h1, hqt]
    have : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg ht _
    nlinarith
  have hsecond : 1 - q ≤ t ^ (p - 1) := by
    rcases le_or_gt t 1 with hle | hgt
    · have h1 : t ≤ t ^ (p - 1) := by
        rcases eq_or_lt_of_le ht with h0 | hpos
        · rw [← h0, Real.zero_rpow (by linarith)]
        · have := Real.rpow_le_rpow_of_exponent_ge hpos hle (show p - 1 ≤ 1 by linarith)
          simpa using this
      have h2 : 1 - q ≤ t := by rw [← hqt]; nlinarith
      linarith
    · have h1 : (1 : ℝ) ≤ t ^ (p - 1) := Real.one_le_rpow hgt.le (by linarith)
      linarith
  linarith

lemma coin_moment (t p a : ℝ) (ht : 0 ≤ t) (hp : 1 < p) (hp2 : p ≤ 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) (hv : ‖v‖ ≤ a) :
    Integrable (fun ω => ‖(coin (1 / (1 + t)) ω - 1) • v‖ ^ p) unif ∧
      ∫ ω, ‖(coin (1 / (1 + t)) ω - 1) • v‖ ^ p ∂unif ≤ 2 * t ^ (p - 1) * a ^ p := by
  have hp0 : 0 < p := by linarith
  have he : (fun ω => ‖(coin (1 / (1 + t)) ω - 1) • v‖ ^ p) =
      fun ω => |coin (1 / (1 + t)) ω - 1| ^ p * ‖v‖ ^ p := by
    funext ω
    rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  rw [he]
  refine ⟨(coin_rpow_integrable _ p).mul_const _, ?_⟩
  rw [integral_mul_const]
  have h1 := coin_rpow_integral t p ht hp hp2
  have h2 : ‖v‖ ^ p ≤ a ^ p := Real.rpow_le_rpow (norm_nonneg _) hv hp0.le
  have h3 : 0 ≤ ∫ ω, |coin (1 / (1 + t)) ω - 1| ^ p ∂unif :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have h4 : 0 ≤ ‖v‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ ω, |coin (1 / (1 + t)) ω - 1| ^ p ∂unif) * ‖v‖ ^ p ≤ 2 * t ^ (p - 1) * ‖v‖ ^ p :=
        mul_le_mul_of_nonneg_right h1 h4
    _ ≤ 2 * t ^ (p - 1) * a ^ p :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) (Real.rpow_nonneg ht _))

end LongTails.Proofs.HeavyTailedHighProbabilityMoments
