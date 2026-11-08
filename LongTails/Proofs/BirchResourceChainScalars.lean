import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.BirchResourceChainScalars

open MeasureTheory Set

noncomputable def gateSlope (x : ℝ) : ℝ := max 0 (min x (1 - x))

noncomputable def gate (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, gateSlope t

noncomputable def payoff (x : ℝ) : ℝ := 2 + Real.arctan x

noncomputable def payoffSlope (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

lemma gateSlope_continuous : Continuous gateSlope :=
  continuous_const.max (continuous_id.min (continuous_const.sub continuous_id))

lemma gateSlope_range (x : ℝ) : 0 ≤ gateSlope x ∧ gateSlope x ≤ 1 / 2 := by
  unfold gateSlope
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  by_cases hx : x ≤ 1 / 2
  · exact (min_le_left _ _).trans hx
  · exact (min_le_right _ _).trans (by linarith)

lemma gateSlope_nonpos {x : ℝ} (hx : x ≤ 0) : gateSlope x = 0 := by
  unfold gateSlope
  exact max_eq_left ((min_le_left _ _).trans hx)

lemma gateSlope_one_le {x : ℝ} (hx : 1 ≤ x) : gateSlope x = 0 := by
  unfold gateSlope
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

lemma gate_deriv (x : ℝ) : HasDerivAt gate (gateSlope x) x := by
  unfold gate
  exact intervalIntegral.integral_hasDerivAt_right
    (gateSlope_continuous.intervalIntegrable _ _)
    gateSlope_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter gateSlope_continuous.continuousAt

lemma payoff_deriv (x : ℝ) : HasDerivAt payoff (payoffSlope x) x := by
  convert (hasDerivAt_const x (2 : ℝ)).add (Real.hasDerivAt_arctan x) using 1
  · rfl
  · simp [payoffSlope]

lemma gate_nonpos {x : ℝ} (hx : x ≤ 0) : gate x = 0 := by
  unfold gate
  have he : Set.EqOn gateSlope (fun _ => 0) (Set.uIcc (0 : ℝ) x) := by
    intro t ht
    rw [uIcc_of_ge hx] at ht
    exact gateSlope_nonpos ht.2
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_zero]

lemma gate_after_one {x : ℝ} (hx : 1 ≤ x) : gate x = gate 1 := by
  have he : (∫ t in (1 : ℝ)..x, gateSlope t) = 0 := by
    have he : Set.EqOn gateSlope (fun _ => 0) (Set.uIcc (1 : ℝ) x) := by
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact gateSlope_one_le ht.1
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_zero]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (gateSlope_continuous.intervalIntegrable (μ := volume) 0 1) (gateSlope_continuous.intervalIntegrable (μ := volume) 1 x)
  rw [he, add_zero] at h
  exact h.symm

lemma gate_mono : Monotone gate :=
  monotone_of_deriv_nonneg (fun x => (gate_deriv x).differentiableAt)
    (fun x => by rw [(gate_deriv x).deriv]; exact (gateSlope_range x).1)

lemma gate_range (x : ℝ) : 0 ≤ gate x ∧ gate x ≤ 1 / 2 := by
  have hz : gate 0 = 0 := gate_nonpos le_rfl
  have ho : gate 1 ≤ 1 / 2 := by
    have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      zero_le_one (gateSlope_continuous.intervalIntegrable (μ := volume) 0 1)
      (continuous_const.intervalIntegrable (μ := volume) 0 1)
      (fun x _ => (gateSlope_range x).2)
    simpa [gate] using h
  constructor
  · by_cases hx : x ≤ 0
    · rw [gate_nonpos hx]
    · exact hz ▸ gate_mono (le_of_not_ge hx)
  · by_cases hx : x ≤ 1
    · exact (gate_mono hx).trans ho
    · rw [gate_after_one (le_of_not_ge hx)]
      exact ho

lemma gate_lb {x : ℝ} (hx : 1 ≤ x) : 1 / 8 ≤ gate x := by
  have hmid : 1 / 8 ≤ ∫ t in (1 / 4 : ℝ)..(3 / 4), gateSlope t := by
    have h := intervalIntegral.integral_mono_on (a := (1 / 4 : ℝ)) (b := (3 / 4 : ℝ))
      (by norm_num) (continuous_const.intervalIntegrable (μ := volume) _ _)
      (gateSlope_continuous.intervalIntegrable _ _)
      (fun t ht => show (1 / 4 : ℝ) ≤ gateSlope t from
        (le_min ht.1 (by linarith [ht.2])).trans (le_max_right _ _))
    norm_num at h ⊢
    exact h
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (gateSlope_continuous.intervalIntegrable (μ := volume) 0 (1 / 4))
    (gateSlope_continuous.intervalIntegrable (μ := volume) (1 / 4) (3 / 4))
  have hquarter := (gate_range (1 / 4)).1
  have hmono := gate_mono (show (3 / 4 : ℝ) ≤ x by linarith)
  change 0 ≤ ∫ t in (0 : ℝ)..(1 / 4), gateSlope t at hquarter
  change (∫ t in (0 : ℝ)..(3 / 4), gateSlope t) ≤ gate x at hmono
  linarith only [hmid, hsum, hquarter, hmono]

lemma payoff_range (x : ℝ) : 0 ≤ payoff x ∧ payoff x ≤ 4 := by
  unfold payoff
  have h₁ := Real.neg_pi_div_two_lt_arctan x
  have h₂ := Real.arctan_lt_pi_div_two x
  constructor <;> linarith [Real.pi_lt_four]

lemma payoffSlope_range (x : ℝ) : 0 ≤ payoffSlope x ∧ payoffSlope x ≤ 1 := by
  unfold payoffSlope
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
  nlinarith

lemma payoffSlope_lb {x : ℝ} (hx : |x| ≤ 1) : 1 / 2 ≤ payoffSlope x := by
  unfold payoffSlope
  apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
  obtain ⟨ha, hb⟩ := abs_le.mp hx
  nlinarith [mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 + x by linarith)]

lemma gate_lip (x y : ℝ) : |gate x - gate y| ≤ |x - y| := by
  have hl : LipschitzWith 1 gate := lipschitzWith_of_nnnorm_deriv_le
    (fun t => (gate_deriv t).differentiableAt) (fun t => by
      rw [(gate_deriv t).deriv]
      exact_mod_cast (show ‖gateSlope t‖ ≤ (1 : ℝ) from by
        rw [Real.norm_eq_abs, abs_of_nonneg (gateSlope_range t).1]
        exact (gateSlope_range t).2.trans (by norm_num)))
  simpa [Real.dist_eq] using hl.dist_le_mul x y

lemma payoff_lip (x y : ℝ) : |payoff x - payoff y| ≤ |x - y| := by
  have hl : LipschitzWith 1 payoff := lipschitzWith_of_nnnorm_deriv_le
    (fun t => (payoff_deriv t).differentiableAt) (fun t => by
      rw [(payoff_deriv t).deriv]
      exact_mod_cast (show ‖payoffSlope t‖ ≤ (1 : ℝ) from by
        rw [Real.norm_eq_abs, abs_of_nonneg (payoffSlope_range t).1]
        exact (payoffSlope_range t).2))
  simpa [Real.dist_eq] using hl.dist_le_mul x y

lemma gateSlope_one_side (x y d : ℝ) (hd : 0 ≤ d)
    (hxy : x ≤ y + d) (hyx : y ≤ x + d) : gateSlope x ≤ gateSlope y + d := by
  unfold gateSlope
  have hm : min x (1 - x) ≤ min y (1 - y) + d := by
    rw [← min_add_add_right]
    exact min_le_min hxy (by linarith only [hyx])
  exact max_le (add_nonneg (le_max_left _ _) hd) (hm.trans (add_le_add (le_max_right _ _) le_rfl))

lemma gateSlope_lip (x y : ℝ) : |gateSlope x - gateSlope y| ≤ |x - y| := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp (le_refl |x - y|)
  have hxy : x ≤ y + |x - y| := by linarith only [h₂]
  have hyx : y ≤ x + |x - y| := by linarith only [h₁]
  have ha := gateSlope_one_side x y |x - y| (abs_nonneg _) hxy hyx
  have hb := gateSlope_one_side y x |x - y| (abs_nonneg _) hyx hxy
  exact abs_le.mpr ⟨by linarith only [hb], by linarith only [ha]⟩

lemma payoffSlope_lip (x y : ℝ) : |payoffSlope x - payoffSlope y| ≤ |x - y| := by
  have hx : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hy : 2 * |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  have hnum : |-(x + y)| ≤ (1 + x ^ 2) * (1 + y ^ 2) := by
    rw [abs_neg]
    refine (abs_add_le x y).trans ?_
    nlinarith only [hx, hy, sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have he : payoffSlope x - payoffSlope y =
      (x - y) * -(x + y) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
    unfold payoffSlope
    field_simp
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (by positivity : 0 < (1 + x ^ 2) * (1 + y ^ 2))]
  exact (div_le_iff₀ (by positivity)).2 (mul_le_mul_of_nonneg_left hnum (abs_nonneg _))

end LongTails.Proofs.BirchResourceChainScalars
