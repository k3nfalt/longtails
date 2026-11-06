import LongTails.Algorithms.StochasticQuasarParameters
import LongTails.Proofs.StochasticQuasarSchedule

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma outer_order_two (q : Params) : 2 ≤ outerOrder q := by unfold outerOrder; omega

lemma outer_order_pos (q : Params) : (0 : ℝ) < outerOrder q := by
  have hh := outer_order_two q
  exact_mod_cast (by omega : 0 < outerOrder q)

lemma outer_damping_pos (q : Params) : 0 < outerDamping q := by
  have hp := outer_order_pos q
  unfold outerDamping
  positivity

lemma outer_step_pos {q : Params} (hv : spec.valid q) : 0 < outerStep q := by
  have hp := outer_order_pos q
  have hL := hv.1
  unfold outerStep
  positivity

lemma outer_scale_pos {q : Params} (hv : spec.valid q) : 0 < outerScale q := by
  have hp := outer_order_pos q
  have hL := hv.1
  have hγ := hv.2.2.1
  unfold outerScale
  positivity

lemma outer_horizon_pos {q : Params} (hv : spec.valid q) : 0 < outerHorizon q := by
  rcases hv with ⟨hL, hD, hγ, _, _, hε, _, _⟩
  have hp := outer_order_pos q
  unfold outerHorizon
  positivity

lemma outer_weight_pos {q : Params} (hv : spec.valid q) (t : ℝ) : 0 < outerWeight q t := by
  have hL := hv.1
  exact acceleration_weight_pos (by positivity) (outer_scale_pos hv).le t

lemma outer_mirror_nonneg {q : Params} (hv : spec.valid q) (t : ℝ) : 0 ≤ outerMirror q t :=
  div_nonneg (acceleration_slope_nonneg (outer_scale_pos hv).le (outer_horizon_pos hv).le t) hv.2.2.1.le

lemma outer_threshold_pos {q : Params} (hv : spec.valid q) (t : ℝ) : 0 < outerThreshold q t := by
  have hL := hv.1
  have hD := hv.2.1
  have hA := outer_weight_pos hv t
  unfold outerThreshold
  positivity

lemma outer_deviation_pos {q : Params} (hv : spec.valid q) : 0 < outerDeviation q := by
  rcases hv with ⟨hL, hD, hγ, _, _, hε, _, _⟩
  unfold outerDeviation
  positivity

lemma outer_bias_pos {q : Params} (hv : spec.valid q) : 0 < outerBias q := by
  rcases hv with ⟨_, hD, hγ, _, _, hε, _, _⟩
  unfold outerBias
  positivity

lemma output_radius_pos {q : Params} (hv : spec.valid q) : 0 < outputRadius q := by
  rcases hv with ⟨hL, _, _, _, _, hε, _, _⟩
  unfold outputRadius
  positivity

lemma output_batch_pos (q : Params) : 0 < outputBatch q := by
  unfold outputBatch
  omega

lemma outer_curvature_step {q : Params} (hv : spec.valid q) :
    (2 * q.L) * outerStep q = outerDamping q := by
  have hL := ne_of_gt hv.1
  have hp := ne_of_gt (outer_order_pos q)
  unfold outerStep outerDamping
  field_simp
  ring

lemma outer_scale_tuning {q : Params} (hv : spec.valid q) :
    4 * outerScale q = q.γ ^ 2 * outerDamping q * outerStep q := by
  have hL := ne_of_gt hv.1
  have hp := ne_of_gt (outer_order_pos q)
  unfold outerScale outerDamping outerStep
  field_simp
  ring

lemma outer_mirror_tuning {q : Params} (hv : spec.valid q) (t : ℝ) :
    outerMirror q t ^ 2 ≤ outerWeight q t * outerDamping q * outerStep q := by
  have hL := hv.1
  exact acceleration_mirror_tuning (by positivity) (outer_scale_pos hv).le hv.2.2.1
    (outer_scale_tuning hv) t

lemma outer_damping_cap (q : Params) : outerDamping q ≤ 1 / 16 := by
  have hp : (2 : ℝ) ≤ outerOrder q := by exact_mod_cast outer_order_two q
  unfold outerDamping
  apply (div_le_iff₀ (by positivity : 0 < 4096 * (outerOrder q : ℝ))).mpr
  nlinarith

lemma outer_damping_small (q : Params) : 144 * (outerOrder q : ℝ) * outerDamping q ≤ 1 := by
  have hp := outer_order_pos q
  unfold outerDamping
  rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 4096 * (outerOrder q : ℝ))]
  nlinarith

lemma outer_weight_initial (q : Params) : outerWeight q 0 = 1 / (4 * q.L) :=
  acceleration_weight_initial _ _ _

lemma continuous_outer_weight (q : Params) : Continuous (outerWeight q) :=
  continuous_acceleration_weight _ _ _

lemma continuous_outer_mirror (q : Params) : Continuous (outerMirror q) :=
  (continuous_acceleration_slope _ _).div_const _

lemma continuous_outer_threshold {q : Params} (hv : spec.valid q) : Continuous (outerThreshold q) := by
  unfold outerThreshold
  apply continuous_const.mul
  exact Real.continuous_sqrt.comp (continuous_const.div (continuous_outer_weight q)
    (fun t => ne_of_gt (outer_weight_pos hv t)))

lemma outer_weight_deriv {q : Params} (hv : spec.valid q) (t : ℝ) :
    HasDerivAt (outerWeight q) (q.γ * outerMirror q t) t := by
  have hh := acceleration_weight_deriv (A0 := 1 / (4 * q.L)) (a := outerScale q)
    (ne_of_gt (outer_horizon_pos hv)) t
  convert! hh using 1
  unfold outerMirror
  field_simp [ne_of_gt hv.2.2.1]

lemma outer_mirror_after {q : Params} (hv : spec.valid q) {t : ℝ} (ht : 2 * outerHorizon q ≤ t) :
    outerMirror q t = 0 := by
  unfold outerMirror
  rw [acceleration_slope_after (outer_horizon_pos hv) ht, zero_div]

lemma outer_threshold_balance {q : Params} (hv : spec.valid q) (t : ℝ) :
    (outerOrder q : ℝ) * (outerWeight q t * outerStep q) * outerThreshold q t ^ 2 = 8 * q.D ^ 2 := by
  have hp := ne_of_gt (outer_order_pos q)
  have hL := ne_of_gt hv.1
  have hA := ne_of_gt (outer_weight_pos hv t)
  have hs := Real.sq_sqrt (div_nonneg hv.1.le (outer_weight_pos hv t).le)
  unfold outerThreshold outerStep
  rw [mul_pow, mul_pow, hs]
  field_simp
  ring

lemma outer_horizon_sq {q : Params} (hv : spec.valid q) :
    outerHorizon q ^ 2 = 4294967296 * (outerOrder q : ℝ) ^ 2 * (q.L * q.D ^ 2 / q.ε) / q.γ ^ 2 := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  unfold outerHorizon
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ q.L * q.D ^ 2 / q.ε)]
  ring

lemma outer_weight_final {q : Params} (hv : spec.valid q) {t : ℝ} (ht : 2 * outerHorizon q ≤ t) :
    outerWeight q t = 1 / (4 * q.L) + 64 * q.D ^ 2 / q.ε := by
  have hL := ne_of_gt hv.1
  have hγ := ne_of_gt hv.2.2.1
  have hε := ne_of_gt hv.2.2.2.2.2.1
  have hp := ne_of_gt (outer_order_pos q)
  unfold outerWeight
  rw [acceleration_weight_after (outer_horizon_pos hv) ht, outer_horizon_sq hv]
  unfold outerScale
  field_simp
  ring

lemma outer_weight_upper {q : Params} (hv : spec.valid q) (t : ℝ) :
    outerWeight q t ≤ 1 / (4 * q.L) + 64 * q.D ^ 2 / q.ε := by
  have hr := (GradientOnlyQuasar.smoothRamp_bounds (t / (2 * outerHorizon q))).2
  have ha := outer_scale_pos hv
  have hbound : outerWeight q t ≤ outerWeight q (2 * outerHorizon q) := by
    change accelerationWeight _ _ _ t ≤ accelerationWeight _ _ _ _
    rw [acceleration_weight_after (outer_horizon_pos hv) le_rfl]
    unfold accelerationWeight
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ 2 * outerScale q * outerHorizon q ^ 2)
    linarith
  rwa [outer_weight_final hv le_rfl] at hbound

lemma outer_weight_bound {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) (t : ℝ) :
    outerWeight q t ≤ 65 * q.D ^ 2 / q.ε := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  have hh : 1 / (4 * q.L) ≤ q.D ^ 2 / q.ε := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * q.L) hε).mpr
    nlinarith
  calc
    outerWeight q t ≤ 1 / (4 * q.L) + 64 * q.D ^ 2 / q.ε := outer_weight_upper hv t
    _ ≤ q.D ^ 2 / q.ε + 64 * q.D ^ 2 / q.ε := add_le_add hh le_rfl
    _ = 65 * q.D ^ 2 / q.ε := by ring

lemma outer_deviation_sq {q : Params} (hv : spec.valid q) :
    outerDeviation q ^ 2 = q.γ * Real.sqrt q.L * q.ε * Real.sqrt q.ε / (1048576 * q.D) := by
  rcases hv with ⟨hL, hD, hγ, _, _, hε, _, _⟩
  exact Real.sq_sqrt (by positivity)

lemma output_radius_sq {q : Params} (hv : spec.valid q) :
    outputRadius q ^ 2 = q.ε / (110592 * q.L) := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  exact Real.sq_sqrt (by positivity)

lemma output_prox_error_sq {q : Params} (hv : spec.valid q) :
    (96 * outputRadius q) ^ 2 = q.ε / (12 * q.L) := by
  rw [mul_pow, output_radius_sq hv]
  ring

lemma output_gradient_variance {q : Params} (hv : spec.valid q) :
    q.σ ^ 2 / (outputBatch q : ℝ) ≤ (q.ε / (24 * q.D)) ^ 2 / 256 := by
  have hD := hv.2.1
  have hε := hv.2.2.2.2.2.1
  have hb : (0 : ℝ) < outputBatch q := by exact_mod_cast output_batch_pos q
  have hc : 147456 * q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2 ≤ (outputBatch q : ℝ) :=
    (Nat.le_ceil _).trans (by
      apply Nat.cast_le.mpr
      exact le_max_right _ _)
  have hc' := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  apply (div_le_iff₀ hb).mpr
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hD)).mp
  have he : ((q.ε / (24 * q.D)) ^ 2 / 256 * (outputBatch q : ℝ)) * q.D ^ 2 =
      (outputBatch q : ℝ) * q.ε ^ 2 / 147456 := by
    field_simp
    ring
  rw [mul_comm (q.D ^ 2) (((q.ε / (24 * q.D)) ^ 2 / 256) * (outputBatch q : ℝ)), he]
  nlinarith

end OracleTemplate.StochasticQuasar
