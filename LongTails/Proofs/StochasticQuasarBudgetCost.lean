import LongTails.Proofs.StochasticQuasarBudgetScales
import LongTails.Proofs.StochasticQuasarTailTuning
import LongTails.Algorithms.StochasticQuasarProgram

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

noncomputable def noiseScale (q : Params) : ℝ := q.σ ^ 2 * q.D ^ 2 / (q.γ ^ 2 * q.ε ^ 2)
noncomputable def rateScale (q : Params) : ℝ := 1 + Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ + noiseScale q

lemma noise_scale_nonneg (q : Params) : 0 ≤ noiseScale q := by unfold noiseScale; positivity

lemma rate_scale_one {q : Params} (hv : spec.valid q) : 1 ≤ rateScale q := by
  have hγ := hv.2.2.1
  have hn := noise_scale_nonneg q
  have hh : 0 ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ := by positivity
  unfold rateScale
  linarith

lemma bias_noise_identity {q : Params} (hv : spec.valid q) :
    q.σ ^ 2 / outerBias q ^ 2 = 1099511627776 * noiseScale q := by
  have hD := hv.2.1
  have hγ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  unfold outerBias noiseScale
  field_simp
  ring

lemma horizon_variance_noise_identity {q : Params} (hv : spec.valid q) :
    outerHorizon q * q.σ ^ 2 / outerDeviation q ^ 2 = 68719476736 * (outerOrder q : ℝ) * noiseScale q := by
  have hL := hv.1
  have hD := hv.2.1
  have hγ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  rw [outer_horizon_normalized hv, outer_deviation_sq hv]
  unfold noiseScale
  field_simp
  rw [Real.sq_sqrt hε.le]
  ring

lemma bias_le_variance {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    outerBias q ^ 2 ≤ outerDeviation q ^ 2 := by
  have hT := outer_horizon_large hv he
  have hp := outer_order_pos q
  have ht : outerHorizon q = 65536 * (outerOrder q : ℝ) * (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) := by
    unfold outerHorizon
    ring
  rw [ht] at hT
  have hχ : (1 / 2 : ℝ) ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ := by nlinarith
  have hβ := outer_bias_pos hv
  apply (one_le_div (sq_pos_of_pos hβ)).mp
  rw [variance_bias_ratio hv]
  linarith

lemma stage_log_bounds {q : Params} (hv : spec.valid q) :
    (innerStageCount q.D (estimatorRadius q.L (outerDeviation q) (outerBias q)) : ℝ) ≤
      16 * (1 + complexityLog q) ∧
    (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) ≤ 16 * (1 + complexityLog q) := by
  have hb : (0 : ℝ) ≤ complexityLog q := by positivity
  have hk : (innerStageCount q.D (estimatorRadius q.L (outerDeviation q) (outerBias q)) : ℝ) ≤
      15 + 2 * complexityLog q := by exact_mod_cast inner_stage_le_complexity hv
  have hm : (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ) ≤ 12 + complexityLog q := by
    exact_mod_cast estimator_depth_le_complexity hv
  constructor <;> linarith

lemma mean_cost_bound {q : Params} (hv : spec.valid q) :
    outerMeanCost q ≤ 256 * (1 + complexityLog q : ℝ) ^ 2 +
      1048576 * (1 + complexityLog q : ℝ) ^ 2 * (q.σ ^ 2 / outerDeviation q ^ 2) := by
  obtain ⟨hk, hm⟩ := stage_log_bounds hv
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hm2 := pow_le_pow_left₀ (by positivity : 0 ≤ (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ)) hm 2
  have hn : 0 ≤ q.σ ^ 2 / outerDeviation q ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_right hm2 hn
  unfold outerMeanCost
  simp only [div_eq_mul_inv] at hh hn ⊢
  nlinarith [sq_nonneg ((1 + complexityLog q : ℝ) - 1),
    mul_nonneg (sq_nonneg (1 + complexityLog q : ℝ)) hn]

lemma max_cost_bound {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    outerMaxCost q ≤ 512 * (1 + complexityLog q : ℝ) +
      2305843009213693952 * (1 + complexityLog q : ℝ) * noiseScale q := by
  obtain ⟨hk, hm⟩ := stage_log_bounds hv
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hβ := outer_bias_pos hv
  have hinv := one_div_le_one_div_of_le (sq_pos_of_pos hβ) (bias_le_variance hv he)
  have hs := mul_le_mul_of_nonneg_left hinv (sq_nonneg q.σ)
  have hnoise : q.σ ^ 2 * (1 / outerDeviation q ^ 2 + 1 / outerBias q ^ 2) ≤
      2199023255552 * noiseScale q := by
    have hh := bias_noise_identity hv
    simp only [div_eq_mul_inv, one_mul] at hs hh ⊢
    nlinarith
  have hn := noise_scale_nonneg q
  have hprod := mul_le_mul_of_nonneg_left hnoise
    (by positivity : 0 ≤ (estimatorDepth (outerDeviation q) (outerBias q) + 1 : ℝ))
  have hM := mul_le_mul_of_nonneg_right hm hn
  unfold outerMaxCost
  nlinarith

lemma unscaled_noise_le {q : Params} (hv : spec.valid q) :
    q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2 ≤ noiseScale q := by
  have hγ := hv.2.2.1
  have hγ1 := hv.2.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hg : q.γ ^ 2 ≤ 1 := by nlinarith
  unfold noiseScale
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg q.ε]

lemma output_batch_cost {q : Params} (hv : spec.valid q) :
    (outputBatch q : ℝ) ≤ 1 + 147456 * noiseScale q := by
  have hn : 0 ≤ 147456 * q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2 := by positivity
  have hc := (Nat.ceil_lt_add_one hn).le
  have hh := unscaled_noise_le hv
  unfold outputBatch
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · have hn' := noise_scale_nonneg q
    linarith
  · have he : 147456 * q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2 = 147456 * (q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2) := by ring
    rw [he] at hc ⊢
    linarith

lemma high_accuracy_inner_noise {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    q.σ ^ 2 / (q.L * q.ε) ≤ 4 * noiseScale q := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  have hh : q.σ ^ 2 / (q.L * q.ε) ≤ 4 * (q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2) := by
    rw [show 4 * (q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2) = (4 * q.σ ^ 2 * q.D ^ 2) / q.ε ^ 2 by ring]
    apply (div_le_div_iff₀ (by positivity : 0 < q.L * q.ε) (sq_pos_of_pos hε)).mpr
    have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ q.σ ^ 2 * q.ε)
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left (unscaled_noise_le hv) (by norm_num))

lemma cleanup_inner_cost {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    (innerCalls q.L q.σ q.D (innerStageCount q.D (outputRadius q)) : ℝ) ≤
      64 * (1 + complexityLog q : ℝ) + 8388608 * noiseScale q := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  have hh := inner_calls_any_radius hL (output_radius_pos hv) q.σ q.D
  have hk : (innerStageCount q.D (outputRadius q) : ℝ) ≤ 9 + complexityLog q := by
    exact_mod_cast cleanup_stage_le_complexity hv
  have hb : (0 : ℝ) ≤ complexityLog q := by positivity
  have hn := noise_scale_nonneg q
  have hnoise := high_accuracy_inner_noise hv he
  have hid : (32 / 3 : ℝ) * q.σ ^ 2 / (q.L ^ 2 * outputRadius q ^ 2) =
      1179648 * (q.σ ^ 2 / (q.L * q.ε)) := by
    rw [output_radius_sq hv]
    field_simp
    ring
  rw [hid] at hh
  linarith

lemma repetitions_le_order (q : Params) : (outerOrder q + 1 : ℝ) ≤ 2 * outerOrder q := by
  have hp : (2 : ℝ) ≤ outerOrder q := by exact_mod_cast outer_order_two q
  linarith

lemma rate_scale_noise {q : Params} (hv : spec.valid q) : 1 + noiseScale q ≤ rateScale q := by
  have hγ := hv.2.2.1
  have hh : 0 ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ := by positivity
  unfold rateScale
  linarith

lemma cleanup_cost_bound {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    (cleanupCalls q : ℝ) ≤ 67108864 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hp := outer_order_pos q
  have hp2 : (2 : ℝ) ≤ outerOrder q := by exact_mod_cast outer_order_two q
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hn := noise_scale_nonneg q
  have hb := output_batch_cost hv
  have hi := cleanup_inner_cost hv he
  have hr := repetitions_le_order q
  have hbR := mul_le_mul hb hr (by positivity : (0 : ℝ) ≤ outerOrder q + 1) (by positivity)
  have hiR := mul_le_mul hi hr (by positivity : (0 : ℝ) ≤ outerOrder q + 1) (by positivity)
  have hUN := mul_le_mul_of_nonneg_right hu hn
  have hpUN := mul_le_mul_of_nonneg_left hUN hp.le
  have hpU := mul_le_mul_of_nonneg_left hu hp.le
  have hsmall : (cleanupCalls q : ℝ) ≤ 33554432 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) * (1 + noiseScale q) := by
    unfold cleanupCalls
    push_cast
    nlinarith
  have hu2 : (1 + complexityLog q : ℝ) ≤ (1 + complexityLog q : ℝ) ^ 2 := by nlinarith
  have hS := rate_scale_noise hv
  have hS0 := rate_scale_one hv
  calc
    _ ≤ 33554432 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) * (1 + noiseScale q) := hsmall
    _ ≤ 33554432 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by gcongr
    _ ≤ _ := by gcongr; norm_num

lemma initial_cleanup_cost_bound {q : Params} (hv : spec.valid q) :
    ((1 + outputBatch q * (outerOrder q + 1) : ℕ) : ℝ) ≤
      1048576 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hp := outer_order_pos q
  have hp2 : (2 : ℝ) ≤ outerOrder q := by exact_mod_cast outer_order_two q
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hn := noise_scale_nonneg q
  have hb := mul_le_mul (output_batch_cost hv) (repetitions_le_order q)
    (by positivity : (0 : ℝ) ≤ outerOrder q + 1) (by positivity)
  have hsmall : ((1 + outputBatch q * (outerOrder q + 1) : ℕ) : ℝ) ≤
      1048576 * (outerOrder q : ℝ) * (1 + noiseScale q) := by
    push_cast
    nlinarith [mul_nonneg hp.le hn]
  have hS := rate_scale_noise hv
  have hS0 := rate_scale_one hv
  have hu2 : (1 : ℝ) ≤ (1 + complexityLog q : ℝ) ^ 2 := by nlinarith
  apply hsmall.trans
  calc
    _ ≤ 1048576 * (outerOrder q : ℝ) * rateScale q := by gcongr
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hu2
        (by positivity : 0 ≤ 1048576 * (outerOrder q : ℝ) * rateScale q)
      nlinarith

lemma outer_mean_total_cost {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    2 * (outerCount q : ℝ) * outerMeanCost q ≤
      2305843009213693952 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hp := outer_order_pos q
  have hγ := hv.2.2.1
  have hT := outer_horizon_pos hv
  have hn := noise_scale_nonneg q
  have hχ : 0 ≤ Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ := by positivity
  have hc := mean_cost_bound hv
  have hk := outer_count_upper hv he
  have hb : 0 ≤ 256 * (1 + complexityLog q : ℝ) ^ 2 +
      1048576 * (1 + complexityLog q : ℝ) ^ 2 * (q.σ ^ 2 / outerDeviation q ^ 2) := by positivity
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2)) hc
    (by unfold outerMeanCost; positivity) (by positivity)
  have ht : outerHorizon q = 65536 * (outerOrder q : ℝ) *
      (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) := by unfold outerHorizon; ring
  have hnid := horizon_variance_noise_identity hv
  have heq : 2 * (9 * outerHorizon q) *
      (256 * (1 + complexityLog q : ℝ) ^ 2 + 1048576 * (1 + complexityLog q : ℝ) ^ 2 *
        (q.σ ^ 2 / outerDeviation q ^ 2)) =
      301989888 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 *
        (Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ) +
      1297036692682702848 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * noiseScale q := by
    calc
      _ = 4608 * (1 + complexityLog q : ℝ) ^ 2 * outerHorizon q +
          18874368 * (1 + complexityLog q : ℝ) ^ 2 *
          (outerHorizon q * q.σ ^ 2 / outerDeviation q ^ 2) := by ring
      _ = _ := by rw [hnid, ht]; ring
  rw [heq] at hprod
  have h1 : 0 ≤ (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 := by positivity
  have h2 := mul_nonneg h1 hχ
  have h3 := mul_nonneg h1 hn
  unfold rateScale
  nlinarith

lemma outer_max_total_cost {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    outerMaxCost q * outerOrder q ≤
      2305843009213693952 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hp := outer_order_pos q
  have hn := noise_scale_nonneg q
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hu2 : (1 + complexityLog q : ℝ) ≤ (1 + complexityLog q : ℝ) ^ 2 := by nlinarith
  have hS := rate_scale_noise hv
  calc
    _ ≤ (512 * (1 + complexityLog q : ℝ) +
        2305843009213693952 * (1 + complexityLog q : ℝ) * noiseScale q) * outerOrder q :=
      mul_le_mul_of_nonneg_right (max_cost_bound hv he) hp.le
    _ ≤ 2305843009213693952 * (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) * (1 + noiseScale q) := by
      nlinarith [mul_nonneg hp.le (by positivity : (0 : ℝ) ≤ 1 + complexityLog q)]
    _ ≤ _ := by gcongr

lemma cost_scale_one {q : Params} (hv : spec.valid q) :
    1 ≤ (outerOrder q : ℝ) * (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hp : (1 : ℝ) ≤ outerOrder q := by exact_mod_cast (outer_order_two q).trans' (by omega)
  have hu : (1 : ℝ) ≤ 1 + complexityLog q := by
    have hh : (0 : ℝ) ≤ complexityLog q := by positivity
    linarith
  have hu2 : (1 : ℝ) ≤ (1 + complexityLog q : ℝ) ^ 2 := by nlinarith
  have hS := rate_scale_one hv
  calc
    1 = 1 * 1 * (1 : ℝ) := by norm_num
    _ ≤ _ := by gcongr

lemma work_cap_cost {q : Params} (hv : spec.valid q) (he : q.ε ≤ 4 * q.L * q.D ^ 2) :
    (workCap q : ℝ) ≤ 9223372036854775808 * (outerOrder q : ℝ) *
      (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hm := outer_mean_total_cost hv he
  have hw := outer_max_total_cost hv he
  have hscale := cost_scale_one hv
  have hn : 0 ≤ 2 * (outerCount q : ℝ) * outerMeanCost q + outerMaxCost q * outerOrder q := by
    unfold outerMeanCost outerMaxCost
    positivity
  have hc := (Nat.ceil_lt_add_one hn).le
  unfold workCap
  nlinarith

lemma program_cost_bound {q : Params} (hv : spec.valid q) (seed : ProgramSeed q) :
    ((program q seed).1 : ℝ) ≤ (2 : ℝ) ^ 96 * (outerOrder q : ℝ) *
      (1 + complexityLog q : ℝ) ^ 2 * rateScale q := by
  have hscale := cost_scale_one hv
  by_cases he : 4 * q.L * q.D ^ 2 ≤ q.ε
  · have hp : (program q seed).1 = 1 + outputBatch q * (outerOrder q + 1) := by
      simp only [program, ite_eq_left he]
    rw [hp]
    have hh := initial_cleanup_cost_bound hv
    push_cast at hh
    norm_num at ⊢
    nlinarith
  · have he' := (lt_of_not_ge he).le
    have hw := work_cap_cost hv he'
    have hc := cleanup_cost_bound hv he'
    by_cases hs : outerCalls q seed ≤ workCap q
    · have hp : (program q seed).1 = cleanupCalls q + outerCalls q seed := by
        simp only [program, ite_eq_right he, ite_eq_left hs]
      have hs' : (outerCalls q seed : ℝ) ≤ workCap q := by exact_mod_cast hs
      rw [hp, Nat.cast_add]
      norm_num at ⊢
      nlinarith
    · have hp : (program q seed).1 = 0 := by simp only [program, ite_eq_right he, ite_eq_right hs]
      rw [hp, Nat.cast_zero]
      norm_num
      nlinarith

end OracleTemplate.StochasticQuasar
