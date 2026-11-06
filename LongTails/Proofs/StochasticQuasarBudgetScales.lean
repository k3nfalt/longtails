import LongTails.Proofs.StochasticQuasarNoiseTuning
import LongTails.Proofs.StochasticQuasarEstimatorTuning

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

noncomputable def complexityScale (q : Params) : ℝ := 2 + q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε)
noncomputable def complexityLog (q : Params) : ℕ := Nat.clog 2 ⌈complexityScale q⌉₊

lemma complexity_scale_two {q : Params} (hv : spec.valid q) : 2 ≤ complexityScale q := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  unfold complexityScale
  have hh : 0 ≤ q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε) := by positivity
  linarith

lemma complexity_scale_power (q : Params) : complexityScale q ≤ (2 : ℝ) ^ complexityLog q :=
  (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈complexityScale q⌉₊)

lemma complexity_log_le_scale {q : Params} (hv : spec.valid q) :
    (complexityLog q : ℝ) ≤ complexityScale q + 1 := by
  have hh : complexityLog q ≤ ⌈complexityScale q⌉₊ := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hc := (Nat.ceil_lt_add_one (by linarith [complexity_scale_two hv] : 0 ≤ complexityScale q)).le
  exact (by exact_mod_cast hh : (complexityLog q : ℝ) ≤ ⌈complexityScale q⌉₊).trans hc

lemma acceleration_scale_sq {q : Params} (hv : spec.valid q) :
    (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) ^ 2 = q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε) := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ q.L * q.D ^ 2 / q.ε)]
  ring

lemma acceleration_scale_le_complexity {q : Params} (hv : spec.valid q) :
    Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ ≤ complexityScale q := by
  have hs := acceleration_scale_sq hv
  unfold complexityScale
  nlinarith [sq_nonneg (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ - 1)]

lemma variance_bias_ratio {q : Params} (hv : spec.valid q) :
    outerDeviation q ^ 2 / outerBias q ^ 2 = 1048576 * (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) := by
  have hL := hv.1
  have hD := hv.2.1
  have hγ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hs : Real.sqrt (q.L * q.D ^ 2 / q.ε) = Real.sqrt q.L * q.D / Real.sqrt q.ε := by
    rw [Real.sqrt_div (by positivity : 0 ≤ q.L * q.D ^ 2), Real.sqrt_mul hL.le, Real.sqrt_sq hD.le]
  rw [outer_deviation_sq hv, hs]
  unfold outerBias
  field_simp
  nlinarith [Real.sq_sqrt hε.le]

lemma deviation_bias_ratio_le_scale {q : Params} (hv : spec.valid q) :
    outerDeviation q / outerBias q ≤ 1024 * complexityScale q := by
  have hβ := outer_bias_pos hv
  have hv0 := outer_deviation_pos hv
  have hZ := complexity_scale_two hv
  have hχ := acceleration_scale_le_complexity hv
  apply (sq_le_sq₀ (by positivity : 0 ≤ outerDeviation q / outerBias q) (by positivity)).mp
  rw [div_pow, variance_bias_ratio hv]
  nlinarith

lemma ceil_log_le_of_power {x : ℝ} {k : ℕ} (hx : x ≤ (2 : ℝ) ^ k) : Nat.clog 2 ⌈x⌉₊ ≤ k := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  exact_mod_cast hx

lemma estimator_depth_le_complexity {q : Params} (hv : spec.valid q) :
    estimatorDepth (outerDeviation q) (outerBias q) + 1 ≤ 12 + complexityLog q := by
  have hh := deviation_bias_ratio_le_scale hv
  have hz := complexity_scale_two hv
  have hp := complexity_scale_power q
  have hb : 1 + outerDeviation q / outerBias q ≤ (2 : ℝ) ^ (11 + complexityLog q) := by
    rw [pow_add]
    norm_num
    linarith
  have hd := ceil_log_le_of_power hb
  change estimatorDepth (outerDeviation q) (outerBias q) ≤ 11 + complexityLog q at hd
  omega

lemma estimator_depth_le_scale {q : Params} (hv : spec.valid q) :
    (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) ≤ 16 * complexityScale q := by
  have hh : (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) ≤ 12 + complexityLog q := by
    exact_mod_cast estimator_depth_le_complexity hv
  have hb := complexity_log_le_scale hv
  have hz := complexity_scale_two hv
  linarith

lemma inner_radius_ratio_identity {q : Params} (hv : spec.valid q) :
    q.D ^ 2 / estimatorRadius q.L (outerDeviation q) (outerBias q) ^ 2 =
      41943040 * (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) * q.γ ^ 2 *
        (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) ^ 3 := by
  have hL := hv.1
  have hD := hv.2.1
  have hγ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hs : Real.sqrt (q.L * q.D ^ 2 / q.ε) = Real.sqrt q.L * q.D / Real.sqrt q.ε := by
    rw [Real.sqrt_div (by positivity : 0 ≤ q.L * q.D ^ 2), Real.sqrt_mul hL.le, Real.sqrt_sq hD.le]
  rw [estimator_radius_sq, outer_deviation_sq hv, hs]
  field_simp
  have hL4 : Real.sqrt q.L ^ 4 = q.L ^ 2 := by
    calc
      _ = (Real.sqrt q.L ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL.le]
  rw [Real.sq_sqrt hε.le, hL4]
  ring

lemma inner_radius_ratio_bound {q : Params} (hv : spec.valid q) :
    q.D ^ 2 / estimatorRadius q.L (outerDeviation q) (outerBias q) ^ 2 ≤
      1073741824 * complexityScale q ^ 4 := by
  have hγ := hv.2.2.1
  have hγ1 := hv.2.2.2.1
  have hZ := complexity_scale_two hv
  have hχ0 : 0 ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ := by positivity
  have hγsq : q.γ ^ 2 ≤ 1 := by nlinarith
  have hχ := acceleration_scale_le_complexity hv
  have hM := estimator_depth_le_scale hv
  rw [inner_radius_ratio_identity hv]
  calc
    _ ≤ 41943040 * (16 * complexityScale q) * 1 * complexityScale q ^ 3 := by gcongr
    _ ≤ 1073741824 * complexityScale q ^ 4 := by nlinarith [pow_nonneg (by linarith : 0 ≤ complexityScale q) 4]

lemma inner_stage_le_complexity {q : Params} (hv : spec.valid q) :
    innerStageCount q.D (estimatorRadius q.L (outerDeviation q) (outerBias q)) ≤ 15 + 2 * complexityLog q := by
  have hr := estimator_radius_pos hv.1 (outer_deviation_pos hv) (outerBias q)
  have hD := hv.2.1
  have hZ := complexity_scale_two hv
  have hh : q.D / estimatorRadius q.L (outerDeviation q) (outerBias q) ≤ 32768 * complexityScale q ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow]
    have hb := inner_radius_ratio_bound hv
    nlinarith
  have hp := complexity_scale_power q
  apply ceil_log_le_of_power
  calc
    _ ≤ 32768 * complexityScale q ^ 2 := hh
    _ ≤ 32768 * ((2 : ℝ) ^ complexityLog q) ^ 2 := by gcongr
    _ = (2 : ℝ) ^ (15 + 2 * complexityLog q) := by
      rw [pow_add, Nat.mul_comm 2 (complexityLog q), pow_mul]
      norm_num

lemma cleanup_stage_le_complexity {q : Params} (hv : spec.valid q) :
    innerStageCount q.D (outputRadius q) ≤ 9 + complexityLog q := by
  have hL := hv.1
  have hD := hv.2.1
  have hγ := hv.2.2.1
  have hγ1 := hv.2.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hr := output_radius_pos hv
  have hZ := complexity_scale_two hv
  have hk : q.L * q.D ^ 2 / q.ε ≤ complexityScale q := by
    have hg : q.γ ^ 2 ≤ 1 := by nlinarith
    have hh : q.L * q.D ^ 2 / q.ε ≤ q.L * q.D ^ 2 / (q.γ ^ 2 * q.ε) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    unfold complexityScale
    linarith
  have hratio : (q.D / outputRadius q) ^ 2 = 110592 * (q.L * q.D ^ 2 / q.ε) := by
    rw [div_pow, output_radius_sq hv]
    field_simp
  have hb : q.D / outputRadius q ≤ 512 * complexityScale q := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hratio]
    nlinarith
  apply ceil_log_le_of_power
  calc
    _ ≤ 512 * complexityScale q := hb
    _ ≤ 512 * (2 : ℝ) ^ complexityLog q := mul_le_mul_of_nonneg_left (complexity_scale_power q) (by norm_num)
    _ = (2 : ℝ) ^ (9 + complexityLog q) := by rw [pow_add]; norm_num

end OracleTemplate.StochasticQuasar
