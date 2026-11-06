import LongTails.Proofs.StochasticQuasarOuterTuning

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

lemma outer_horizon_normalized {q : Params} (hv : spec.valid q) :
    outerHorizon q = 65536 * (outerOrder q : ℝ) * Real.sqrt q.L * q.D /
      (q.γ * Real.sqrt q.ε) := by
  have hL := hv.1
  have hD := hv.2.1
  have hε := hv.2.2.2.2.2.1
  unfold outerHorizon
  rw [Real.sqrt_div (by positivity : 0 ≤ q.L * q.D ^ 2),
    Real.sqrt_mul hL.le, Real.sqrt_sq hD.le]
  ring

lemma outer_variance_coefficient {q : Params} (hv : spec.valid q) :
    outerStep q * outerDeviation q ^ 2 * outerHorizon q = q.ε / 131072 := by
  have hL := hv.1
  have hD := ne_of_gt hv.2.1
  have hγ := ne_of_gt hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hp := ne_of_gt (outer_order_pos q)
  have hs := ne_of_gt (Real.sqrt_pos.mpr hε)
  rw [outer_deviation_sq hv, outer_horizon_normalized hv]
  unfold outerStep
  field_simp
  nlinarith [Real.sq_sqrt hL.le]

lemma outer_bias_coefficient_sq {q : Params} (hv : spec.valid q) :
    (3 * outerBias q * outerHorizon q) ^ 2 * (outerDamping q * outerStep q * (8 * q.D ^ 2)) =
      9 * q.ε * q.D ^ 2 / 1073741824 := by
  have hL := hv.1
  have hD := ne_of_gt hv.2.1
  have hγ := ne_of_gt hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hp := ne_of_gt (outer_order_pos q)
  have hs := ne_of_gt (Real.sqrt_pos.mpr hε)
  rw [outer_horizon_normalized hv]
  unfold outerBias outerDamping outerStep
  field_simp
  nlinarith [Real.sq_sqrt hL.le, Real.sq_sqrt hε.le]

lemma outer_variance_drift_bound {q : Params} (hv : spec.valid q)
    (he : q.ε ≤ 4 * q.L * q.D ^ 2) (t : ℝ) :
    (outerWeight q t * outerStep q * outerDeviation q ^ 2) * outerHorizon q ≤
      (8 * q.D ^ 2) / 8192 := by
  have hε := hv.2.2.2.2.2.1
  have hA := (le_div_iff₀ hε).mp (outer_weight_bound hv he t)
  have hid : (outerWeight q t * outerStep q * outerDeviation q ^ 2) * outerHorizon q =
      outerWeight q t * (q.ε / 131072) := by
    rw [← outer_variance_coefficient hv]
    ring
  rw [hid]
  nlinarith [sq_nonneg q.D]

lemma outer_bias_drift_bound {q : Params} (hv : spec.valid q)
    (he : q.ε ≤ 4 * q.L * q.D ^ 2) (t : ℝ) :
    (3 * Real.sqrt (outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2)) *
      outerBias q) * outerHorizon q ≤ (8 * q.D ^ 2) / 8192 := by
  have hε := hv.2.2.2.2.2.1
  have hA := (le_div_iff₀ hε).mp (outer_weight_bound hv he t)
  have hn : 0 ≤ outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2) :=
    mul_nonneg (mul_nonneg (outer_damping_pos q).le
      (mul_nonneg (outer_weight_pos hv t).le (outer_step_pos hv).le)) (by positivity)
  have hβ := outer_bias_pos hv
  have hT := outer_horizon_pos hv
  have hs := Real.sq_sqrt hn
  have hid : ((3 * Real.sqrt (outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2)) *
      outerBias q) * outerHorizon q) ^ 2 = outerWeight q t * (9 * q.ε * q.D ^ 2 / 1073741824) := by
    rw [← outer_bias_coefficient_sq hv]
    calc
      _ = (3 * outerBias q * outerHorizon q) ^ 2 *
        (Real.sqrt (outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hs]; ring
  apply (sq_le_sq₀ (by positivity : 0 ≤ (3 * Real.sqrt
    (outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2)) * outerBias q) * outerHorizon q)
    (by positivity)).mp
  rw [hid]
  have hh := mul_le_mul_of_nonneg_right hA (sq_nonneg q.D)
  nlinarith [sq_nonneg (q.D ^ 2)]

lemma outer_noise_drift_bound {q : Params} (hv : spec.valid q)
    (he : q.ε ≤ 4 * q.L * q.D ^ 2) (t : ℝ) :
    2 * (outerOrder q : ℝ) *
      (outerWeight q t * outerStep q * outerDeviation q ^ 2 +
        3 * Real.sqrt (outerDamping q * (outerWeight q t * outerStep q) * (8 * q.D ^ 2)) * outerBias q) /
      (8 * q.D ^ 2) ≤ (outerOrder q : ℝ) / (1024 * outerHorizon q) := by
  have hp := outer_order_pos q
  have hT := outer_horizon_pos hv
  have hD := hv.2.1
  have h₁ := outer_variance_drift_bound hv he t
  have h₂ := outer_bias_drift_bound hv he t
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * q.D ^ 2) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hp.le
  nlinarith

end OracleTemplate.StochasticQuasar
