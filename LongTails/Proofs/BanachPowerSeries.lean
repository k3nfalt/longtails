import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators NNReal ENNReal
open Filter

namespace OracleTemplate.MarkovProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
noncomputable def coeffSeries (a : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

omit [CompleteSpace E] in
lemma coeffSeries_coeff (a : ℕ → E) (n : ℕ) : (coeffSeries a).coeff n = a n := by
  simp [FormalMultilinearSeries.coeff, coeffSeries]

omit [CompleteSpace E] in
lemma coeffSeries_sum (a : ℕ → E) (z : ℂ) :
    (coeffSeries a).sum z = ∑' n, z ^ n • a n := by
  simp [FormalMultilinearSeries.sum, coeffSeries]

omit [CompleteSpace E] in
lemma coeffSeries_radius (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) :
    1 ≤ (coeffSeries a).radius := by
  simpa using (coeffSeries a).le_radius_of_bound (r := (1 : ℝ≥0)) C
    (fun n => by simpa [coeffSeries, ContinuousMultilinearMap.norm_mkPiRing] using ha n)

lemma coeffSeries_expansion (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) :
    HasFPowerSeriesOnBall (fun z : ℂ => ∑' n, z ^ n • a n) (coeffSeries a) 0 1 := by
  have hr := coeffSeries_radius a ha
  have h := ((coeffSeries a).hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hr)).mono (by norm_num : (0 : ℝ≥0∞) < 1) hr
  rw [show (coeffSeries a).sum = (fun z : ℂ => ∑' n, z ^ n • a n) from funext (coeffSeries_sum a)] at h
  exact h

lemma coeffSeries_analytic (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, z ^ n • a n) (Metric.ball 0 1) := by
  simpa only [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one] using
    (coeffSeries_expansion a ha).analyticOnNhd

lemma coeffSeries_factorial (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) (n : ℕ) :
    n.factorial • a n = iteratedDeriv n (fun z : ℂ => ∑' k, z ^ k • a k) 0 := by
  have h := (coeffSeries_expansion a ha).factorial_smul 1 n
  simpa [coeffSeries, ← iteratedDeriv_eq_iteratedFDeriv] using h

lemma coeffSeries_deriv_sum (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n)
      (deriv (fun w : ℂ => ∑' n, w ^ n • a n) z) := by
  obtain ⟨r, hzr, hr⟩ := exists_between hz
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hu : Summable (fun n : ℕ => r ^ n * C) :=
    (summable_geometric_of_lt_one hr0 hr).mul_right C
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) r) : ‖w ^ n • a n‖ ≤ r ^ n * C := by
    have hw' : ‖w‖ ≤ r := by
      have hh : ‖w‖ < r := by simpa [dist_zero_right] using hw
      exact hh.le
    rw [norm_smul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg w) hw' n) (ha n) (norm_nonneg _) (pow_nonneg hr0 n)
  have ht := Complex.hasSum_deriv_of_summable_norm hu
    (fun n => (differentiable_id.pow n).smul_const (a n) |>.differentiableOn)
    Metric.isOpen_ball hb (by simpa [dist_zero_right] using hzr)
  convert ht using 1
  funext n
  simpa using (((hasDerivAt_id z).pow n).smul_const (a n)).deriv.symm

lemma coeffSeries_deriv_shift (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℂ) * z ^ n) • a (n + 1))
      (deriv (fun w : ℂ => ∑' n, w ^ n • a n) z) := by
  have h := coeffSeries_deriv_sum a ha hz
  rw [← hasSum_nat_add_iff' 1] at h
  simpa using h

lemma coeffSeries_deriv_bound (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv (fun w : ℂ => ∑' n, w ^ n • a n) z‖ ≤ C / (1 - ‖z‖) ^ 2 := by
  have hg : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖z‖ ^ n * C)
      (C / (1 - ‖z‖) ^ 2) := by
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1
      (by simpa using hz : ‖‖z‖‖ < 1)).mul_right C
    simpa [Nat.choose_one_right, mul_comm, div_eq_mul_inv] using h
  apply (coeffSeries_deriv_shift a ha hz).norm_le_of_bounded hg
  intro n
  simp only [norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (ha (n + 1)) (by positivity)

lemma coeffSeries_second_cauchy (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    {R : ℝ≥0} (hR : 0 < R) (hR1 : (R : ℝ) < 1) (n : ℕ) :
    (cauchyPowerSeries (deriv (deriv (fun z : ℂ => ∑' k, z ^ k • a k))) 0 R).coeff n =
      ((n + 1) * (n + 2)) • a (n + 2) := by
  let f : ℂ → E := fun z => ∑' k, z ^ k • a k
  have hf : AnalyticOnNhd ℂ f (Metric.ball 0 1) := coeffSeries_analytic a ha
  have hg := (hf.deriv.deriv.differentiableOn.mono
    (Metric.closedBall_subset_ball hR1)).hasFPowerSeriesOnBall hR
  have h := hg.factorial_smul 1 n
  change n.factorial • (cauchyPowerSeries (deriv (deriv f)) 0 R).coeff n = _ at h
  rw [← iteratedDeriv_eq_iteratedFDeriv, ← iteratedDeriv_succ', ← iteratedDeriv_succ'] at h
  rw [← coeffSeries_factorial a ha (n + 2)] at h
  have he : (n + 2).factorial = n.factorial * ((n + 1) * (n + 2)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [he, mul_nsmul, smul_comm] at h
  have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi := congrArg (fun v : E => (n.factorial : ℂ)⁻¹ • v) h
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hne] using hi

lemma coeffSeries_second_circle_bound (a : ℕ → E) {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    {R : ℝ≥0} (hR : 0 < R) (hR1 : (R : ℝ) < 1) (n : ℕ) :
    (((n + 1) * (n + 2) : ℕ) : ℝ) * ‖a (n + 2)‖ ≤
      ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi,
        ‖deriv (deriv (fun z : ℂ => ∑' k, z ^ k • a k)) (circleMap 0 R θ)‖) *
      (R : ℝ)⁻¹ ^ n := by
  have h := norm_cauchyPowerSeries_le
    (deriv (deriv (fun z : ℂ => ∑' k, z ^ k • a k))) 0 R n
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeffSeries_second_cauchy a ha hR hR1] at h
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, norm_smul, Complex.norm_natCast, abs_of_nonneg R.coe_nonneg] using h

end OracleTemplate.MarkovProduct

namespace OracleTemplate.MarkovProduct
open Complex Metric
lemma reciprocal_square_circle_average {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Real.circleAverage (fun z : ℂ => 1 / ‖1 - z‖ ^ 2) 0 ρ = 1 / (1 - ρ ^ 2) := by
  let h : ℂ → ℂ := fun z => (1 + z) / (1 - z)
  have hn (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : 1 - z ≠ 0 := by
    have hz' : ‖z‖ ≤ ρ := by simpa [dist_zero_right] using hz
    intro he
    have he' : z = 1 := (sub_eq_zero.mp he).symm
    rw [he'] at hz'
    norm_num at hz'
    linarith
  have hd : DifferentiableOn ℂ h (closedBall 0 ρ) := by
    intro z hz
    exact (((differentiableAt_const 1).add differentiableAt_id).div
      ((differentiableAt_const 1).sub differentiableAt_id) (hn z hz)).differentiableWithinAt
  have hm : Real.circleAverage h 0 ρ = 1 := by
    have hd' : DiffContOnCl ℂ h (ball 0 |ρ|) := by
      simpa only [abs_of_nonneg hρ] using hd.diffContOnCl_ball (Set.Subset.refl _)
    have hm := hd'.circleAverage
    simpa only [abs_of_nonneg hρ, h, zero_add, add_zero, sub_zero, div_one] using hm
  have hi : CircleIntegrable h 0 ρ :=
    (hd.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hρ
  have hr : Real.circleAverage (fun z => (h z).re) 0 ρ = 1 := by
    have hh := Complex.reCLM.circleAverage_comp_comm hi
    simpa only [Function.comp_def, Complex.reCLM_apply, hm, Complex.one_re] using hh
  have he : Real.circleAverage (fun z => (h z).re) 0 ρ =
      (1 - ρ ^ 2) * Real.circleAverage (fun z : ℂ => 1 / ‖1 - z‖ ^ 2) 0 ρ := by
    calc
      _ = Real.circleAverage (fun z : ℂ => (1 - ρ ^ 2) • (1 / ‖1 - z‖ ^ 2)) 0 ρ := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hz' : ‖z‖ = ρ := by simpa [dist_zero_right, abs_of_nonneg hρ] using hz
        have hp := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) 1
        have hp' : (h z).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
          simpa [poissonKernel_def, herglotzRieszKernel_def, h] using hp.symm
        change (h z).re = (1 - ρ ^ 2) • (1 / ‖1 - z‖ ^ 2)
        rw [hp', hz']
        simp [div_eq_mul_inv]
      _ = _ := by rw [Real.circleAverage_fun_smul]; rfl
  have hpos : 0 < 1 - ρ ^ 2 := by nlinarith
  apply (eq_div_iff hpos.ne').mpr
  rw [mul_comm, ← he, hr]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
lemma second_deriv_circle_average_bound (a : ℕ → E) {M C : ℝ} (ha : ∀ n, ‖a n‖ ≤ M)
    (hbound : ∀ z : ℂ, ‖z‖ < 1 →
      ‖deriv (deriv (fun w : ℂ => ∑' k, w ^ k • a k)) z‖ ≤ C / ‖1 - z‖ ^ 2)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Real.circleAverage (fun z : ℂ => ‖deriv (deriv (fun w : ℂ => ∑' k, w ^ k • a k)) z‖) 0 ρ ≤
      C / (1 - ρ ^ 2) := by
  have hs : Metric.sphere (0 : ℂ) ρ ⊆ Metric.ball 0 1 := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa [dist_zero_right] using hz
    simpa [dist_zero_right, hz'] using hρ1
  have hcont := ((coeffSeries_analytic a ha).deriv.deriv.continuousOn.mono hs).norm
  have hi := hcont.circleIntegrable hρ
  have hg : ContinuousOn (fun z : ℂ => C / ‖1 - z‖ ^ 2) (Metric.sphere 0 ρ) := by
    apply continuousOn_const.div ((continuous_const.sub continuous_id).norm.pow 2).continuousOn
    intro z hz
    apply pow_ne_zero 2
    apply norm_ne_zero_iff.mpr
    intro he
    change 1 - z = 0 at he
    have hz' := hs hz
    rw [← sub_eq_zero.mp he] at hz'
    simp at hz'
  have hle := Real.circleAverage_mono hi (hg.circleIntegrable hρ) (fun z hz =>
    hbound z (by simpa [abs_of_nonneg hρ, dist_zero_right] using hs (by simpa [abs_of_nonneg hρ] using hz)))
  have he : Real.circleAverage (fun z : ℂ => C / ‖1 - z‖ ^ 2) 0 ρ = C / (1 - ρ ^ 2) := by
    calc
      _ = C * Real.circleAverage (fun z : ℂ => 1 / ‖1 - z‖ ^ 2) 0 ρ := by
        have hh := Real.circleAverage_fun_smul (𝕜 := ℝ) (E := ℝ)
          (f := fun z : ℂ => 1 / ‖1 - z‖ ^ 2) (a := C) (c := 0) (R := ρ)
        simpa [smul_eq_mul, div_eq_mul_inv] using hh
      _ = _ := by rw [reciprocal_square_circle_average hρ hρ1]; ring
  exact he ▸ hle

lemma coefficient_radius_bounds (n : ℕ) (hn : 2 ≤ n) :
    let ρ : ℝ := 1 - 1 / (2 * n)
    0 < ρ ∧ ρ < 1 ∧ 1 / 2 ≤ ρ ^ (n - 2) ∧ 1 / (2 * n) ≤ 1 - ρ ^ 2 := by
  dsimp
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) := by linarith
  have ht : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have ht1 : 1 / (2 * (n : ℝ)) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hrpos : 0 < 1 - 1 / (2 * (n : ℝ)) := by linarith
  have hr1 : 1 - 1 / (2 * (n : ℝ)) < 1 := by linarith
  refine ⟨hrpos, hr1, ?_, ?_⟩
  · have hb := one_add_mul_sub_le_pow (a := 1 - 1 / (2 * (n : ℝ))) (by linarith) n
    have he : 1 + (n : ℝ) * ((1 - 1 / (2 * (n : ℝ))) - 1) = 1 / 2 := by field_simp; ring
    rw [he] at hb
    exact hb.trans (pow_le_pow_of_le_one hrpos.le hr1.le (Nat.sub_le n 2))
  · nlinarith

lemma second_deriv_coefficient_bound (a : ℕ → E) {M C : ℝ} (ha : ∀ n, ‖a n‖ ≤ M)
    (hbound : ∀ z : ℂ, ‖z‖ < 1 →
      ‖deriv (deriv (fun w : ℂ => ∑' k, w ^ k • a k)) z‖ ≤ C / ‖1 - z‖ ^ 2)
    (n : ℕ) (hn : 2 ≤ n) : ‖a n‖ ≤ 8 * C / n := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hbound 0 (by simp))
    simpa using h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  let ρ : ℝ := 1 - 1 / (2 * n)
  obtain ⟨hr0, hr1, hrpow, hrden⟩ := coefficient_radius_bounds n hn
  change 0 < ρ at hr0
  change ρ < 1 at hr1
  change 1 / 2 ≤ ρ ^ (n - 2) at hrpow
  change 1 / (2 * n) ≤ 1 - ρ ^ 2 at hrden
  have hdpos : 0 < 1 - ρ ^ 2 := by nlinarith
  have hpinv : ρ⁻¹ ^ (n - 2) ≤ 2 := by
    rw [inv_pow, inv_eq_one_div]
    apply (div_le_iff₀ (pow_pos hr0 _)).mpr
    linarith
  have hd : C / (1 - ρ ^ 2) ≤ (2 * n) * C := by
    apply (div_le_iff₀ hdpos).mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mp hrden
    nlinarith
  have hc := coeffSeries_second_circle_bound a ha (R := ⟨ρ, hr0.le⟩) hr0 hr1 (n - 2)
  have havg := second_deriv_circle_average_bound a ha hbound hr0.le hr1
  have hc' : ((n : ℝ) - 1) * n * ‖a n‖ ≤
      Real.circleAverage (fun z : ℂ => ‖deriv (deriv (fun w : ℂ => ∑' k, w ^ k • a k)) z‖) 0 ρ *
      ρ⁻¹ ^ (n - 2) := by
    have h1 : n - 2 + 1 = n - 1 := by omega
    have h2 : n - 2 + 2 = n := by omega
    simpa only [h1, h2, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
      Real.circleAverage, smul_eq_mul, NNReal.coe_mk] using! hc
  have hf : ((n : ℝ) - 1) * n * ‖a n‖ ≤ 4 * n * C := by
    calc
      _ ≤ (C / (1 - ρ ^ 2)) * ρ⁻¹ ^ (n - 2) := hc'.trans (mul_le_mul_of_nonneg_right havg (by positivity))
      _ ≤ ((2 * n) * C) * 2 := mul_le_mul hd hpinv (by positivity) (by positivity)
      _ = _ := by ring
  have hcancel : ((n : ℝ) - 1) * ‖a n‖ ≤ 4 * C := by nlinarith
  apply (le_div_iff₀ hnp).mpr
  nlinarith [norm_nonneg (a n)]

end OracleTemplate.MarkovProduct
