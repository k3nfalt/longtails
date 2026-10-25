import LongTails.Algorithms.ValidatedHessianTransport
import LongTails.Proofs.GuardedHessianTuning

namespace LongTails.Proofs.ValidatedHessianTuning

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Algorithms.ValidatedHessianTransport

lemma repeatCount_pos (p : Params) : 0 < repeatCount p := by unfold repeatCount; omega

lemma validationCount_pos (p : Params) : 0 < validationCount p := by unfold validationCount; omega

lemma repeat_failure_small (p : Params) (hv : spec.valid p) :
    guardRadius p * (1 / 3 : ℝ) ^ repeatCount p ≤ p.ε / 8 := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (GuardedHessianTuning.radius_estimates p hL0 hL1 hΔ hε).1
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hn : Real.log (8 * guardRadius p / p.ε) / Real.log 3 ≤ (repeatCount p : ℝ) := by
    have hh := Nat.le_ceil (Real.log (8 * guardRadius p / p.ε) / Real.log 3)
    unfold repeatCount
    push_cast
    linarith
  have hh := Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 3) ((div_le_iff₀ hlog).mp hn)
  have hdiv := one_div_le_one_div_of_le (show 0 < 8 * guardRadius p / p.ε by positivity) hh
  rw [← one_div_pow] at hdiv
  have hmul := mul_le_mul_of_nonneg_left hdiv hM.le
  have he : guardRadius p * (1 / (8 * guardRadius p / p.ε)) = p.ε / 8 := by field_simp
  exact hmul.trans_eq he

lemma validationCount_size (p : Params) :
    (1048576 * (repeatCount p + 1 : ℕ) * (p.σg + p.αg * guardRadius p) / p.ε) ^
      (p.p / (p.p - 1)) ≤ (validationCount p : ℝ) := by
  have hh := Nat.le_ceil ((1048576 * (repeatCount p + 1 : ℕ) *
    (p.σg + p.αg * guardRadius p) / p.ε) ^ (p.p / (p.p - 1)))
  unfold validationCount
  push_cast at hh ⊢
  linarith

lemma validation_error_small (p : Params) (hv : spec.valid p) :
    120 * (repeatCount p + 1 : ℕ) * (p.σg + p.αg * guardRadius p) *
      (((validationCount p : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹) ≤ p.ε / 8 := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (GuardedHessianTuning.radius_estimates p hL0 hL1 hΔ hε).1
  have hh := GuardedHessianTuning.batch_root_tuning
    (show 0 ≤ 1048576 * (repeatCount p + 1 : ℕ) *
      (p.σg + p.αg * guardRadius p) / p.ε by positivity) hp
    (show (0 : ℝ) < validationCount p by exact_mod_cast validationCount_pos p)
    (validationCount_size p)
  have he := mul_le_mul_of_nonneg_right hh hε.le
  field_simp at he
  simp only [one_div] at he
  nlinarith

lemma tuned_expected_small (p : Params) (hv : spec.valid p) :
    p.ε / 4 + guardRadius p * (1 / 3 : ℝ) ^ repeatCount p +
      120 * (repeatCount p + 1 : ℕ) * (p.σg + p.αg * guardRadius p) *
        (((validationCount p : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹) ≤ p.ε := by
  have hh := repeat_failure_small p hv
  have he := validation_error_small p hv
  have hε := hv.2.2.2.2.2.2.2.2.2.2.2
  linarith

noncomputable def baseRadius (p : Params) : ℝ := Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + p.ε

noncomputable def baseCurvature (p : Params) : ℝ :=
  p.L0 + p.σh + (p.L1 + p.αh) * baseRadius p + p.ε / baseRadius p

noncomputable def tailExponent (p : Params) : ℝ := p.p / (p.p - 1)

noncomputable def noiseFactor (p : Params) : ℝ := 1 + (p.σg + p.αg * baseRadius p) / p.ε

noncomputable def guardFactor (p : Params) : ℝ := 1 + p.σg / baseRadius p + p.αg

noncomputable def workScale (p : Params) : ℝ := p.Δ * baseCurvature p / p.ε ^ 2

noncomputable def logFactor (p : Params) : ℝ :=
  1 + Real.log (2 + baseRadius p / p.ε + workScale p + noiseFactor p)

noncomputable def envelope (p : Params) : ℝ :=
  (2 : ℝ) ^ (100 * tailExponent p + 100) * (1 + tailExponent p) *
    logFactor p ^ (tailExponent p + 1) *
      (noiseFactor p ^ tailExponent p + workScale p *
        noiseFactor p ^ (tailExponent p / p.q) * guardFactor p ^ tailExponent p)

lemma baseRadius_pos (p : Params) (hv : spec.valid p) : 0 < baseRadius p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  unfold baseRadius
  positivity

lemma accuracy_le_baseRadius (p : Params) (hv : spec.valid p) : p.ε ≤ baseRadius p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  unfold baseRadius
  nlinarith [Real.sqrt_nonneg (p.L0 * p.Δ), mul_nonneg hL1 hΔ]

lemma tailExponent_ge_two (p : Params) (hv : spec.valid p) : 2 ≤ tailExponent p := by
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  apply (le_div_iff₀ (by linarith : 0 < p.p - 1)).mpr
  linarith

lemma factors_bounds (p : Params) (hv : spec.valid p) :
    1 ≤ noiseFactor p ∧ 1 ≤ guardFactor p ∧ guardFactor p ≤ noiseFactor p ∧
      0 ≤ workScale p ∧ 1 ≤ logFactor p := by
  have hR := baseRadius_pos p hv
  have hεR := accuracy_le_baseRadius p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hNoise : 0 ≤ p.σg + p.αg * baseRadius p := by positivity
  have hS : 1 ≤ noiseFactor p := by
    unfold noiseFactor
    have := div_nonneg hNoise hε.le
    linarith
  have hG : 1 ≤ guardFactor p := by
    unfold guardFactor
    have := div_nonneg hσg hR.le
    linarith
  have hGS : guardFactor p ≤ noiseFactor p := by
    have hh := div_le_div_of_nonneg_left hNoise hε hεR
    have he : guardFactor p = 1 + (p.σg + p.αg * baseRadius p) / baseRadius p := by
      unfold guardFactor
      field_simp
      ring
    rw [he]
    simpa only [noiseFactor, add_comm] using add_le_add_left hh 1
  have hA : 0 ≤ workScale p := by unfold workScale baseCurvature; positivity
  refine ⟨hS, hG, hGS, hA, ?_⟩
  unfold logFactor
  have hh : 0 ≤ Real.log (2 + baseRadius p / p.ε + workScale p + noiseFactor p) :=
    Real.log_nonneg (by have := div_nonneg hR.le hε.le; linarith)
  linarith

lemma radius_eq (p : Params) : guardRadius p = 65536 * baseRadius p := rfl

lemma gradient_noise_scale (p : Params) (hv : spec.valid p) :
    p.σg + p.αg * guardRadius p ≤ 65536 * (p.σg + p.αg * baseRadius p) := by
  have hσ := hv.2.2.1
  rw [radius_eq]
  nlinarith

lemma curvature_scale (p : Params) (hv : spec.valid p) :
    transportScale p ≤ 65536 * baseCurvature p := by
  have hR := baseRadius_pos p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM : baseRadius p ≤ guardRadius p := by rw [radius_eq]; linarith
  have hd := div_le_div_of_nonneg_left hε.le hR hM
  unfold transportScale baseCurvature
  rw [radius_eq] at hd ⊢
  have hdiv := div_nonneg hε.le hR.le
  nlinarith

lemma trial_calls_bound (p : Params) :
    trialCalls (tunedConfig p) ≤ batchCount p + stepCount p *
      (2 + guardGroupCount p * guardBatchCount p) := by
  have hB := GuardedHessianTuning.batchCount_pos p
  have hT := GuardedHessianTuning.stepCount_pos p
  have hJ := GuardedHessianTuning.guardGroupCount_pos p
  have hG := GuardedHessianTuning.guardBatchCount_pos p
  have hd := Nat.div_mul_le_self (stepCount p - 1) (batchCount p)
  simp only [trialCalls, tunedConfig]
  have hb : batchCount p - 1 + 1 = batchCount p := by omega
  have ht : stepCount p - 1 + 1 = stepCount p := by omega
  have hj : guardGroupCount p - 1 + 1 = guardGroupCount p := by omega
  have hg : guardBatchCount p - 1 + 1 = guardBatchCount p := by omega
  rw [hb, ht, hj, hg]
  nlinarith

lemma ceil_power_bound {x y b : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hb : 0 ≤ b)
    (hxy : x ≤ y) : (⌈x ^ b⌉₊ + 1 : ℕ) ≤ 4 * y ^ b := by
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hx b)
  have hp := Real.rpow_le_rpow hx hxy hb
  have hyb := Real.one_le_rpow hy hb
  push_cast
  linarith

lemma reset_count_bound (p : Params) (hv : spec.valid p) :
    (batchCount p : ℝ) ≤ 4 * ((2 : ℝ) ^ 32 * noiseFactor p) ^ tailExponent p := by
  have hR := baseRadius_pos p hv
  have hS := (factors_bounds p hv).1
  have hb := tailExponent_ge_two p hv
  have hscale := gradient_noise_scale p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM : 0 < guardRadius p := by rw [radius_eq]; positivity
  apply ceil_power_bound (by positivity) (by norm_num; linarith) (by change 0 ≤ tailExponent p; linarith)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 65536)) hε.le
  have he : 65536 * (65536 * (p.σg + p.αg * baseRadius p)) / p.ε =
      (2 : ℝ) ^ 32 * ((p.σg + p.αg * baseRadius p) / p.ε) := by norm_num; ring
  rw [he] at hh
  unfold noiseFactor
  norm_num at hh ⊢
  linarith

lemma guard_count_bound (p : Params) (hv : spec.valid p) :
    (guardBatchCount p : ℝ) ≤ 4 * ((2 : ℝ) ^ 20 * guardFactor p) ^ tailExponent p := by
  have hR := baseRadius_pos p hv
  have hG := (factors_bounds p hv).2.1
  have hb := tailExponent_ge_two p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM : 0 < guardRadius p := by rw [radius_eq]; positivity
  apply ceil_power_bound (by positivity) (by norm_num; linarith) (by change 0 ≤ tailExponent p; linarith)
  have hd := div_le_div_of_nonneg_left hσg hR (show baseRadius p ≤ guardRadius p by rw [radius_eq]; linarith)
  unfold guardFactor
  norm_num
  linarith

lemma repeat_count_bound (p : Params) (hv : spec.valid p) :
    (repeatCount p : ℝ) ≤ 32 * logFactor p := by
  have hR := baseRadius_pos p hv
  have hεR := accuracy_le_baseRadius p hv
  have hfactors := factors_bounds p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have ht : 0 < baseRadius p / p.ε := div_pos hR hε
  have ht1 : 1 ≤ baseRadius p / p.ε := (le_div_iff₀ hε).mpr (by simpa using hεR)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3lo : (2 / 3 : ℝ) ≤ Real.log 3 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    linarith
  have hlog2hi : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlogt : Real.log (baseRadius p / p.ε) ≤ logFactor p - 1 := by
    have hh := Real.log_le_log ht (show baseRadius p / p.ε ≤
      2 + baseRadius p / p.ε + workScale p + noiseFactor p by linarith [hfactors.1, hfactors.2.2.2.1])
    simpa only [logFactor, add_sub_cancel_left] using hh
  have he : 8 * guardRadius p / p.ε = (2 : ℝ) ^ 19 * (baseRadius p / p.ε) := by
    rw [radius_eq]
    norm_num
    ring
  have harg : 1 ≤ 8 * guardRadius p / p.ε := by rw [he]; norm_num; linarith
  have hlog : Real.log (8 * guardRadius p / p.ε) ≤ logFactor p + 18 := by
    rw [he, Real.log_mul (by norm_num) ht.ne', Real.log_pow]
    norm_num
    linarith
  have hc := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg harg) hlog3.le)
  have hd : Real.log (8 * guardRadius p / p.ε) / Real.log 3 ≤ 30 * logFactor p := by
    apply (div_le_iff₀ hlog3).mpr
    nlinarith [hfactors.2.2.2.2]
  unfold repeatCount
  push_cast
  linarith [hfactors.2.2.2.2]

lemma repeat_plus_one_bound (p : Params) (hv : spec.valid p) :
    (repeatCount p + 1 : ℕ) ≤ 64 * logFactor p := by
  have hh := repeat_count_bound p hv
  have hl := (factors_bounds p hv).2.2.2.2
  push_cast
  linarith

lemma gradient_ratio_bound (p : Params) (hv : spec.valid p) :
    (p.σg + p.αg * guardRadius p) / p.ε ≤ 65536 * noiseFactor p := by
  have hh := gradient_noise_scale p hv
  have hε := hv.2.2.2.2.2.2.2.2.2.2.2
  have hd := div_le_div_of_nonneg_right hh hε.le
  have he : 65536 * (p.σg + p.αg * baseRadius p) / p.ε =
      65536 * ((p.σg + p.αg * baseRadius p) / p.ε) := by ring
  rw [he] at hd
  unfold noiseFactor
  linarith

lemma validation_count_bound (p : Params) (hv : spec.valid p) :
    (validationCount p : ℝ) ≤ 4 * ((2 : ℝ) ^ 42 * logFactor p * noiseFactor p) ^ tailExponent p := by
  have hR := baseRadius_pos p hv
  have hf := factors_bounds p hv
  have hb := tailExponent_ge_two p hv
  have hratio := gradient_ratio_bound p hv
  have hK := repeat_plus_one_bound p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM : 0 < guardRadius p := by rw [radius_eq]; positivity
  have hS := hf.1
  have hl := hf.2.2.2.2
  have hLS : 1 ≤ logFactor p * noiseFactor p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hS)]
  apply ceil_power_bound (by positivity) (by norm_num; nlinarith)
    (by change 0 ≤ tailExponent p; linarith)
  have h1 := mul_le_mul_of_nonneg_left hratio
    (show (0 : ℝ) ≤ 1048576 * (repeatCount p + 1 : ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hK (show 0 ≤ 68719476736 * noiseFactor p by positivity)
  push_cast at h1 h2
  norm_num
  ring_nf at h1 h2 ⊢
  linarith

lemma reset_root_bound (p : Params) (hv : spec.valid p) :
    (batchCount p : ℝ) ^ p.q⁻¹ ≤ 4 * ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q) := by
  have hB := reset_count_bound p hv
  have hS := (factors_bounds p hv).1
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hq0 : 0 < p.q := by linarith
  have hqi : p.q⁻¹ ≤ 1 := (inv_le_one₀ hq0).mpr hq.le
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg (batchCount p)) hB (inv_nonneg.mpr hq0.le)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
    ← Real.rpow_mul (by positivity)] at hh
  have h4 : (4 : ℝ) ^ p.q⁻¹ ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hqi
  have hmul := mul_le_mul_of_nonneg_right h4
    (Real.rpow_nonneg (show 0 ≤ (2 : ℝ) ^ 32 * noiseFactor p by positivity) (tailExponent p * p.q⁻¹))
  exact hh.trans (by simpa only [div_eq_mul_inv] using hmul)

lemma step_count_bound (p : Params) (hv : spec.valid p) :
    (stepCount p : ℝ) ≤ 2 + (2 : ℝ) ^ 48 * workScale p *
      ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q) := by
  have hT := (GuardedHessianTuning.stepCount_bounds p hv).2
  have hH := curvature_scale p hv
  have hB := reset_root_bound p hv
  have hHpos := GuardedHessianTuning.transportScale_pos p hv
  have hR := baseRadius_pos p hv
  have hS := (factors_bounds p hv).1
  have hBpos : (0 : ℝ) < batchCount p := by exact_mod_cast GuardedHessianTuning.batchCount_pos p
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hc : 0 ≤ baseCurvature p := by unfold baseCurvature; positivity
  have hpow : 0 < (batchCount p : ℝ) ^ p.q⁻¹ := by positivity
  have he : 1024 * p.Δ / (stepSize p * p.ε) =
      1073741824 * p.Δ * transportScale p / p.ε ^ 2 * (batchCount p : ℝ) ^ p.q⁻¹ := by
    unfold stepSize
    field_simp
    ring
  rw [he] at hT
  have h1 := mul_le_mul_of_nonneg_right hH (show 0 ≤ 1073741824 * p.Δ / p.ε ^ 2 *
      (batchCount p : ℝ) ^ p.q⁻¹ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 70368744177664 * p.Δ * baseCurvature p / p.ε ^ 2 by positivity)
  unfold workScale
  norm_num
  ring_nf at h1 h2 hT ⊢
  linarith

lemma logarithm_factors (p : Params) (hv : spec.valid p) :
    Real.log (noiseFactor p) ≤ logFactor p ∧
      Real.log (1 + workScale p) ≤ logFactor p := by
  have hf := factors_bounds p hv
  have hR := baseRadius_pos p hv
  have hε := hv.2.2.2.2.2.2.2.2.2.2.2
  have hd : 0 ≤ baseRadius p / p.ε := by positivity
  have hs := Real.log_le_log (by linarith : 0 < noiseFactor p)
    (show noiseFactor p ≤ 2 + baseRadius p / p.ε + workScale p + noiseFactor p by linarith [hf.2.2.2.1])
  have ha := Real.log_le_log (by linarith [hf.2.2.2.1] : 0 < 1 + workScale p)
    (show 1 + workScale p ≤ 2 + baseRadius p / p.ε + workScale p + noiseFactor p by linarith [hf.1])
  unfold logFactor
  constructor <;> linarith

lemma guard_group_count_bound (p : Params) (hv : spec.valid p) :
    (guardGroupCount p : ℝ) ≤ 128 * (1 + tailExponent p) * logFactor p := by
  have hf := factors_bounds p hv
  have hb := tailExponent_ge_two p hv
  have hlogs := logarithm_factors p hv
  have hT := step_count_bound p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hq0 : 0 < p.q := by linarith
  have hbq : tailExponent p / p.q ≤ tailExponent p :=
    (div_le_self (by linarith) hq.le)
  have hbq0 : 0 ≤ tailExponent p / p.q := by positivity
  have hS : 0 < noiseFactor p := by linarith [hf.1]
  have hA := hf.2.2.2.1
  have hl := hf.2.2.2.2
  have hc : 1 ≤ (2 : ℝ) ^ 32 * noiseFactor p := by norm_num; linarith [hf.1]
  have hpw : 1 ≤ ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q) :=
    Real.one_le_rpow hc hbq0
  have hlarge : 128 * (stepCount p : ℝ) ≤ (2 : ℝ) ^ 57 * (1 + workScale p) *
      ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q) := by
    norm_num at hT ⊢
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hpw)]
  have ht : (0 : ℝ) < stepCount p := by exact_mod_cast GuardedHessianTuning.stepCount_pos p
  have hlog := Real.log_le_log (by positivity : 0 < 128 * (stepCount p : ℝ)) hlarge
  have heLog : Real.log ((2 : ℝ) ^ 57 * (1 + workScale p) *
      ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q)) =
      57 * Real.log 2 + Real.log (1 + workScale p) +
      (tailExponent p / p.q) * (32 * Real.log 2 + Real.log (noiseFactor p)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow (by positivity), Real.log_mul (by norm_num) (ne_of_gt hS), Real.log_pow]
    norm_num
  rw [heLog] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hcLog : 32 * Real.log 2 + Real.log (noiseFactor p) ≤ 32 + logFactor p := by linarith
  have hmul := mul_le_mul_of_nonneg_left hcLog hbq0
  have hmul2 := mul_le_mul_of_nonneg_right hbq (show 0 ≤ 32 + logFactor p by linarith)
  have hlogbound : Real.log (128 * (stepCount p : ℝ)) ≤ 63 * (1 + tailExponent p) * logFactor p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hl)]
  have hlogpos : 0 < Real.log 2 := by linarith
  have ht1 : (1 : ℝ) ≤ stepCount p := by exact_mod_cast GuardedHessianTuning.stepCount_pos p
  have hnonneg : 0 ≤ Real.log (128 * (stepCount p : ℝ)) := Real.log_nonneg (by linarith)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnonneg hlogpos.le)
  have hdiv : Real.log (128 * (stepCount p : ℝ)) / Real.log 2 ≤
      126 * (1 + tailExponent p) * logFactor p := by
    apply (div_le_iff₀ hlogpos).mpr
    nlinarith [mul_nonneg (show 0 ≤ (1 + tailExponent p) * logFactor p by positivity)
      (sub_nonneg.mpr hlog2lo)]
  unfold guardGroupCount
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ tailExponent p by linarith) (sub_nonneg.mpr hl)]

lemma scaled_power (n : ℕ) (x r : ℝ) (hx : 0 ≤ x) :
    ((2 : ℝ) ^ n * x) ^ r = (2 : ℝ) ^ ((n : ℝ) * r) * x ^ r := by
  rw [Real.mul_rpow (by positivity) hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

lemma rough_calls_bound (p : Params) (hv : spec.valid p) :
    (calls (tunedConfig p) (repeatCount p) (validationCount p) : ℝ) ≤
      128 * logFactor p * ((2 : ℝ) ^ 32 * noiseFactor p) ^ tailExponent p +
      32 * logFactor p * (2 + (2 : ℝ) ^ 48 * workScale p *
        ((2 : ℝ) ^ 32 * noiseFactor p) ^ (tailExponent p / p.q)) *
        (2 + 512 * (1 + tailExponent p) * logFactor p *
          ((2 : ℝ) ^ 20 * guardFactor p) ^ tailExponent p) +
      256 * logFactor p * ((2 : ℝ) ^ 42 * logFactor p * noiseFactor p) ^ tailExponent p := by
  have hf := factors_bounds p hv
  have hb := tailExponent_ge_two p hv
  have hC : (trialCalls (tunedConfig p) : ℝ) ≤ batchCount p + (stepCount p : ℝ) *
      (2 + (guardGroupCount p : ℝ) * guardBatchCount p) := by
    exact_mod_cast trial_calls_bound p
  have hB := reset_count_bound p hv
  have hT := step_count_bound p hv
  have hJ := guard_group_count_bound p hv
  have hG := guard_count_bound p hv
  have hK := repeat_count_bound p hv
  have hK1 := repeat_plus_one_bound p hv
  have hV := validation_count_bound p hv
  have hS := hf.1
  have hgf := hf.2.1
  have hA := hf.2.2.2.1
  have hl := hf.2.2.2.2
  have hJG := mul_le_mul hJ hG (Nat.cast_nonneg _) (by positivity)
  have hTC := mul_le_mul hT (add_le_add (le_refl (2 : ℝ)) hJG) (by positivity) (by positivity)
  have hKC := mul_le_mul hK (hC.trans (add_le_add hB hTC)) (by positivity) (by positivity)
  have hKV := mul_le_mul hK1 hV (by positivity) (by positivity)
  unfold calls
  push_cast at hKV ⊢
  ring_nf at hKC hKV ⊢
  linarith only [hKC, hKV]

lemma algebraic_envelope {b r S G A l : ℝ} (hb : 2 ≤ b) (_hr : 0 ≤ r)
    (hrb : r ≤ b) (hS : 1 ≤ S) (hG : 1 ≤ G) (hGS : G ≤ S)
    (hA : 0 ≤ A) (hl : 1 ≤ l) :
    128 * l * ((2 : ℝ) ^ 32 * S) ^ b +
      32 * l * (2 + (2 : ℝ) ^ 48 * A * ((2 : ℝ) ^ 32 * S) ^ r) *
        (2 + 512 * (1 + b) * l * ((2 : ℝ) ^ 20 * G) ^ b) +
      256 * l * ((2 : ℝ) ^ 42 * l * S) ^ b ≤
      (2 : ℝ) ^ (100 * b + 100) * (1 + b) * l ^ (b + 1) *
        (S ^ b + A * S ^ r * G ^ b) := by
  have hb0 : 0 ≤ b := by linarith
  have hGp : 1 ≤ ((2 : ℝ) ^ 20 * G) ^ b :=
    Real.one_le_rpow (by norm_num; linarith) hb0
  have hbl : 1 ≤ (1 + b) * l := by nlinarith
  have hguard : 2 + 512 * (1 + b) * l * ((2 : ℝ) ^ 20 * G) ^ b ≤
      1024 * (1 + b) * l * ((2 : ℝ) ^ 20 * G) ^ b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbl) (sub_nonneg.mpr hGp)]
  have hguardmul := mul_le_mul_of_nonneg_left hguard
    (show 0 ≤ 32 * l * (2 + (2 : ℝ) ^ 48 * A * ((2 : ℝ) ^ 32 * S) ^ r) by positivity)
  have hSl : 0 ≤ S := by linarith
  have hGl : 0 ≤ G := by linarith
  have hll : 0 ≤ l := by linarith
  have he : 128 * l * ((2 : ℝ) ^ 32 * S) ^ b +
      32 * l * (2 + (2 : ℝ) ^ 48 * A * ((2 : ℝ) ^ 32 * S) ^ r) *
        (1024 * (1 + b) * l * ((2 : ℝ) ^ 20 * G) ^ b) +
      256 * l * ((2 : ℝ) ^ 42 * l * S) ^ b =
      (2 : ℝ) ^ (32 * b + 7) * l * S ^ b +
      (2 : ℝ) ^ (20 * b + 16) * (1 + b) * l ^ (2 : ℕ) * G ^ b +
      (2 : ℝ) ^ (32 * r + 20 * b + 63) * (1 + b) * l ^ (2 : ℕ) * A * S ^ r * G ^ b +
      (2 : ℝ) ^ (42 * b + 8) * l ^ (b + 1) * S ^ b := by
    rw [mul_assoc ((2 : ℝ) ^ 42), scaled_power 32 S b hSl,
      scaled_power 32 S r hSl, scaled_power 20 G b hGl,
      scaled_power 42 (l * S) b (mul_nonneg hll hSl), Real.mul_rpow hll hSl]
    simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add (by linarith : 0 < l), Real.rpow_one]
    norm_num
    ring
  have hl1 : l ≤ l ^ (b + 1) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hl (show (1 : ℝ) ≤ b + 1 by linarith)
  have hl2 : l ^ (2 : ℕ) ≤ l ^ (b + 1) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hl (show (2 : ℝ) ≤ b + 1 by linarith)
  have hGSb := Real.rpow_le_rpow hGl hGS hb0
  let D := (2 : ℝ) ^ (100 * b + 98)
  have hD : 0 ≤ D := by positivity
  have hc1 : (2 : ℝ) ^ (32 * b + 7) ≤ D :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc2 : (2 : ℝ) ^ (20 * b + 16) ≤ D :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc3 : (2 : ℝ) ^ (32 * r + 20 * b + 63) ≤ D :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hc4 : (2 : ℝ) ^ (42 * b + 8) ≤ D :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have ht1 : (2 : ℝ) ^ (32 * b + 7) * l * S ^ b ≤ D * (1 + b) * l ^ (b + 1) * S ^ b := by
    have hh : (2 : ℝ) ^ (32 * b + 7) ≤ D * (1 + b) := by nlinarith
    gcongr
  have ht2 : (2 : ℝ) ^ (20 * b + 16) * (1 + b) * l ^ (2 : ℕ) * G ^ b ≤
      D * (1 + b) * l ^ (b + 1) * S ^ b := by gcongr
  have ht3 : (2 : ℝ) ^ (32 * r + 20 * b + 63) * (1 + b) * l ^ (2 : ℕ) * A * S ^ r * G ^ b ≤
      D * (1 + b) * l ^ (b + 1) * A * S ^ r * G ^ b := by gcongr
  have ht4 : (2 : ℝ) ^ (42 * b + 8) * l ^ (b + 1) * S ^ b ≤
      D * (1 + b) * l ^ (b + 1) * S ^ b := by
    have hh : (2 : ℝ) ^ (42 * b + 8) ≤ D * (1 + b) := by nlinarith
    gcongr
  have hD4 : (2 : ℝ) ^ (100 * b + 100) = 4 * D := by
    have hex : 100 * b + 100 = (100 * b + 98) + 2 := by ring
    rw [hex, Real.rpow_add (by norm_num)]
    norm_num [D]
    ring
  rw [hD4]
  have hleft := add_le_add (add_le_add
    (le_refl (128 * l * ((2 : ℝ) ^ 32 * S) ^ b)) hguardmul)
    (le_refl (256 * l * ((2 : ℝ) ^ 42 * l * S) ^ b))
  rw [he] at hleft
  have hp1 : 0 ≤ D * (1 + b) * l ^ (b + 1) * S ^ b := by positivity
  have hp2 : 0 ≤ D * (1 + b) * l ^ (b + 1) * A * S ^ r * G ^ b := by positivity
  nlinarith only [hleft, ht1, ht2, ht3, ht4, hp1, hp2]

lemma calls_le_envelope (p : Params) (hv : spec.valid p) :
    (calls (tunedConfig p) (repeatCount p) (validationCount p) : ℝ) ≤ envelope p := by
  have hf := factors_bounds p hv
  have hb := tailExponent_ge_two p hv
  have hq : 1 < p.q := hv.2.2.2.2.2.2.2.2.1
  have hq0 : 0 < p.q := by linarith
  exact (rough_calls_bound p hv).trans (algebraic_envelope hb
    (div_nonneg (by linarith) hq0.le) (div_le_self (by linarith) hq.le)
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)

lemma calls_le_budget (p : Params) (hv : spec.valid p) :
    calls (tunedConfig p) (repeatCount p) (validationCount p) ≤ ⌈envelope p⌉₊ := by
  exact_mod_cast (calls_le_envelope p hv).trans (Nat.le_ceil (envelope p))

end LongTails.Proofs.ValidatedHessianTuning
