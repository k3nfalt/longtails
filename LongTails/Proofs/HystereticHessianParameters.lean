import LongTails.Proofs.HystereticHessianTuning

namespace LongTails.Proofs.HystereticHessianParameters

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianTuning

lemma targetAccuracy_pos (p : Params) (hv : spec.valid p) : 0 < targetAccuracy p := by
  rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, _, hε⟩
  exact div_pos hε (by norm_num)

lemma noise_scales (p : Params) (hv : spec.valid p) :
    1 ≤ relativeNoise p ∧ relativeNoise p ≤ noiseLevel p ∧ targetAccuracy p ≤ localRadius p ∧
      relativeNoise p * localRadius p = targetAccuracy p * noiseLevel p ∧
      p.σg / localRadius p + p.αg ≤ 2 * relativeNoise p ∧
      p.σg + 4 * p.αg * localRadius p ≤ 5 * targetAccuracy p * noiseLevel p := by
  have he := targetAccuracy_pos p hv
  rcases hv with ⟨_, _, hσ, hα, _, _, _, _, _, _, _, _⟩
  exact noise_radius_properties he hσ hα

lemma localRadius_pos (p : Params) (hv : spec.valid p) : 0 < localRadius p :=
  (targetAccuracy_pos p hv).trans_le (noise_scales p hv).2.2.1

lemma tailPower_two_le (p : Params) (hv : spec.valid p) : 2 ≤ tailPower p := by
  rcases hv with ⟨_, _, _, _, _, _, hp, hp2, _, _, _, _⟩
  unfold tailPower
  apply (le_div_iff₀ (by linarith : 0 < p.p - 1)).mpr
  linarith

lemma epoch_base_one_le (p : Params) (hv : spec.valid p) :
    1 ≤ min ((noiseLevel p) ^ (tailPower p * (p.q - 1) / p.q))
      ((noiseLevel p / relativeNoise p) ^ tailPower p) := by
  have hs := noise_scales p hv
  have hb := tailPower_two_le p hv
  have hA : 0 < relativeNoise p := by linarith [hs.1]
  have hS : 1 ≤ noiseLevel p := hs.1.trans hs.2.1
  have hratio : 1 ≤ noiseLevel p / relativeNoise p := (one_le_div hA).mpr hs.2.1
  rcases hv with ⟨_, _, _, _, _, _, _, _, hq, _, _, _⟩
  apply le_min
  · apply Real.one_le_rpow hS
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · exact Real.one_le_rpow hratio (by linarith)

lemma epochCount_pos (p : Params) (hv : spec.valid p) : 0 < epochCount p :=
  Nat.floor_pos.mpr (epoch_base_one_le p hv)

lemma macroCount_pos (p : Params) : 0 < macroCount p := by unfold macroCount; omega

lemma pilotBatchCount_pos (p : Params) : 0 < pilotBatchCount p := by unfold pilotBatchCount; omega

lemma resetBatchCount_pos (p : Params) : 0 < resetBatchCount p := by unfold resetBatchCount; omega

lemma transportBatchCount_pos (p : Params) : 0 < transportBatchCount p := by unfold transportBatchCount; omega

lemma groupCount_pos (p : Params) : 0 < groupCount p := by unfold groupCount; omega

@[simp] lemma tuned_macros (p : Params) : (tunedConfig p).macros + 1 = macroCount p := by
  exact Nat.sub_add_cancel (macroCount_pos p)

lemma tuned_epoch (p : Params) (hv : spec.valid p) : (tunedConfig p).epoch + 1 = epochCount p := by
  exact Nat.sub_add_cancel (epochCount_pos p hv)

@[simp] lemma tuned_pilotBatch (p : Params) : (tunedConfig p).pilotBatch + 1 = pilotBatchCount p := by
  exact Nat.sub_add_cancel (pilotBatchCount_pos p)

@[simp] lemma tuned_resetBatch (p : Params) : (tunedConfig p).resetBatch + 1 = resetBatchCount p := by
  exact Nat.sub_add_cancel (resetBatchCount_pos p)

@[simp] lemma tuned_transportBatch (p : Params) : (tunedConfig p).transportBatch + 1 = transportBatchCount p := by
  exact Nat.sub_add_cancel (transportBatchCount_pos p)

@[simp] lemma tuned_groups (p : Params) : (tunedConfig p).groups + 1 = groupCount p := by
  exact Nat.sub_add_cancel (groupCount_pos p)

lemma tuned_blockCap (p : Params) (hv : spec.valid p) :
    HystereticHessianBlocks.blockCap (tunedConfig p) = logicalBlocks p := by
  simp only [HystereticHessianBlocks.blockCap, tuned_macros, tuned_epoch p hv, logicalBlocks]

lemma logicalBlocks_pos (p : Params) : 0 < logicalBlocks p := by
  exact Nat.mul_pos (macroCount_pos p) (by omega)

lemma guardRadius_bounds (p : Params) (hv : spec.valid p) :
    0 < guardRadius p ∧ localRadius p ≤ guardRadius p ∧
      16 * p.L1 * p.Δ ≤ guardRadius p ∧ 16 * p.L0 * p.Δ ≤ (guardRadius p) ^ 2 := by
  have hU := localRadius_pos p hv
  rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, hΔ, _⟩
  have hroot := Real.sqrt_nonneg (p.L0 * p.Δ)
  have hsq := Real.sq_sqrt (mul_nonneg hL0 hΔ)
  have hlin := mul_nonneg hL1 hΔ
  dsimp [guardRadius]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (Real.sqrt (p.L0 * p.Δ) + p.L1 * p.Δ + localRadius p)]

lemma momentBound_pos (p : Params) (hv : spec.valid p) : 0 < momentBound p := by
  have hM := (guardRadius_bounds p hv).1
  unfold momentBound
  positivity

lemma confidence_one_le (p : Params) (hv : spec.valid p) : 1 ≤ confidence p := by
  have hM := momentBound_pos p hv
  have he := targetAccuracy_pos p hv
  unfold confidence
  have hh : 0 ≤ ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2 := by positivity
  have hl := Real.log_nonneg (show 1 ≤ 1 + ((logicalBlocks p + macroCount p : ℕ) : ℝ) *
    momentBound p / (targetAccuracy p) ^ 2 by linarith)
  linarith

lemma pilotBatchCount_size (p : Params) :
    ((2 : ℝ) ^ 24 * relativeNoise p) ^ tailPower p ≤ (pilotBatchCount p : ℝ) := by
  have hh := Nat.le_ceil (((2 : ℝ) ^ 24 * relativeNoise p) ^ tailPower p)
  unfold pilotBatchCount
  push_cast
  linarith

lemma resetBatchCount_size (p : Params) :
    ((2 : ℝ) ^ 24 * noiseLevel p) ^ tailPower p ≤ (resetBatchCount p : ℝ) := by
  have hh := Nat.le_ceil (((2 : ℝ) ^ 24 * noiseLevel p) ^ tailPower p)
  unfold resetBatchCount
  push_cast
  linarith

lemma transportBatchCount_size (p : Params) :
    256 * confidence p * (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)) ≤ (transportBatchCount p : ℝ) := by
  have hh := Nat.le_ceil (256 * confidence p * (256 * (epochCount p : ℝ)) ^ (1 / (p.q - 1)))
  unfold transportBatchCount
  push_cast
  linarith

lemma pilot_moment (p : Params) (hv : spec.valid p) (r : ℝ) (hr : 0 ≤ r) :
    6 * (p.σg ^ p.p + p.αg ^ p.p * r ^ p.p) / (pilotBatchCount p : ℝ) ^ (p.p - 1) ≤
      (((localRadius p + r) / 256) / 1536) ^ p.p := by
  have hs := noise_scales p hv
  have hU := localRadius_pos p hv
  rcases hv with ⟨_, _, hσ, hα, _, _, hp, _, _, _, _, _⟩
  exact pilot_batch_moment hσ hα hU (by linarith [hs.1]) hr hp
    (by exact_mod_cast pilotBatchCount_pos p) hs.2.2.2.2.1 (pilotBatchCount_size p)

lemma refresh_moment (p : Params) (hv : spec.valid p) (r : ℝ) (hr : 0 ≤ r)
    (hrU : r ≤ 4 * localRadius p) :
    6 * (p.σg ^ p.p + p.αg ^ p.p * r ^ p.p) / (resetBatchCount p : ℝ) ^ (p.p - 1) ≤
      ((targetAccuracy p / 256) / 1536) ^ p.p := by
  have hs := noise_scales p hv
  have he := targetAccuracy_pos p hv
  rcases hv with ⟨_, _, hσ, hα, _, _, hp, _, _, _, _, _⟩
  exact refresh_batch_moment hσ hα he (by linarith [hs.1, hs.2.1]) hr hp
    (by exact_mod_cast resetBatchCount_pos p) hrU hs.2.2.2.2.2 (resetBatchCount_size p)

lemma momentBound_accuracy (p : Params) (hv : spec.valid p) :
    (targetAccuracy p) ^ 2 ≤ momentBound p := by
  have he := targetAccuracy_pos p hv
  have hM := guardRadius_bounds p hv
  have hMe := (noise_scales p hv).2.2.1.trans hM.2.1
  have hsq : (targetAccuracy p) ^ 2 ≤ (guardRadius p) ^ 2 := by nlinarith
  unfold momentBound
  nlinarith [mul_nonneg (Nat.cast_nonneg (logicalBlocks p) : (0 : ℝ) ≤ logicalBlocks p)
    (sq_nonneg (guardRadius p))]

lemma confidence_three_halves (p : Params) (hv : spec.valid p) : 3 / 2 ≤ confidence p := by
  have he := targetAccuracy_pos p hv
  have hM := momentBound_pos p hv
  have hMbound := momentBound_accuracy p hv
  have hK : 0 < logicalBlocks p + macroCount p := Nat.add_pos_left (logicalBlocks_pos p) _
  have hK1 : (1 : ℝ) ≤ ((logicalBlocks p + macroCount p : ℕ) : ℝ) := by exact_mod_cast hK
  have hr : 1 ≤ ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2 := by
    apply (one_le_div (sq_pos_of_pos he)).mpr
    nlinarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 1 + ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2 by linarith)
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  unfold confidence
  linarith

lemma groupCount_four_le (p : Params) (hv : spec.valid p) : 4 ≤ groupCount p := by
  have hell := confidence_three_halves p hv
  have hh := Nat.le_ceil (2 * confidence p)
  have hthree : (3 : ℝ) ≤ (⌈2 * confidence p⌉₊ : ℝ) := by linarith
  have hn : 3 ≤ ⌈2 * confidence p⌉₊ := by exact_mod_cast hthree
  unfold groupCount
  omega

lemma group_failure_bound (p : Params) :
    (1 / 2 : ℝ) ^ groupCount p ≤ Real.exp (-confidence p) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hG : 2 * confidence p ≤ (groupCount p : ℝ) := by
    have hh := Nat.le_ceil (2 * confidence p)
    unfold groupCount
    push_cast
    linarith
  have hmul := mul_le_mul hG htwo (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (Nat.cast_nonneg (groupCount p) : (0 : ℝ) ≤ groupCount p)
  have hh := GuardedHessianTuning.dyadic_log_bound (Real.exp_pos (confidence p)) (groupCount p)
    (by rw [Real.log_exp]; apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr; nlinarith)
  simpa only [Real.exp_neg, one_div] using hh

lemma group_failure_small (p : Params) (hv : spec.valid p) :
    (1 / 2 : ℝ) ^ groupCount p ≤ 1 / 16 := by
  have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (groupCount_four_le p hv)
  norm_num at hh ⊢
  exact hh

lemma confidence_failure_bound (p : Params) (hv : spec.valid p) :
    ((logicalBlocks p + macroCount p : ℕ) : ℝ) * Real.exp (-confidence p) ≤
      (targetAccuracy p) ^ 2 / momentBound p := by
  have he := targetAccuracy_pos p hv
  have hM := momentBound_pos p hv
  let r := ((logicalBlocks p + macroCount p : ℕ) : ℝ) * momentBound p / (targetAccuracy p) ^ 2
  have hx : 1 + r ≤ Real.exp (confidence p) := by
    apply Real.le_exp_of_log_le
    change Real.log (1 + r) ≤ 1 + Real.log (1 + r)
    linarith
  have hr : r ≤ Real.exp (confidence p) := by linarith
  have hh := (div_le_iff₀ (sq_pos_of_pos he)).mp hr
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos (confidence p))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hM).mpr
  nlinarith

lemma guard_pilot_moment (p : Params) (hv : spec.valid p) :
    6 * (p.σg / guardRadius p + p.αg) ^ p.p / (pilotBatchCount p : ℝ) ^ (p.p - 1) ≤
      (1 / 24576 : ℝ) ^ p.p := by
  have hU := localRadius_pos p hv
  have hM := guardRadius_bounds p hv
  have hs := noise_scales p hv
  have htail := tailPower_two_le p hv
  rcases hv with ⟨_, _, hσ, hα, _, _, hp, _, _, _, _, _⟩
  have hr : 0 ≤ p.σg / guardRadius p + p.αg := add_nonneg (div_nonneg hσ hM.1.le) hα
  have hrel : p.σg / guardRadius p + p.αg ≤ 2 * relativeNoise p := by
    have hh := div_le_div_of_nonneg_left hσ hU hM.2.1
    linarith [hs.2.2.2.2.1]
  have hbase : 1048576 * (p.σg / guardRadius p + p.αg) ≤ (2 : ℝ) ^ 24 * relativeNoise p := by
    norm_num
    nlinarith [hs.1]
  apply GuardedGradientMoments.guard_batch_size_suffices hr hp (pilotBatchCount p) (pilotBatchCount_pos p)
  exact (Real.rpow_le_rpow (by positivity) hbase (by linarith : 0 ≤ tailPower p)).trans
    (pilotBatchCount_size p)

lemma localScale_bounds (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    0 < p.L0 + p.L1 * localRadius p ∧ p.L0 + p.L1 * localRadius p ≤ localScale p ∧
      0 < localScale p ∧
      p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p) ≤ 4 * localScale p := by
  have hU := localRadius_pos p hv
  rcases hv with ⟨hL0, hL1, _, _, hσ, hα, _, _, _, _, _, _⟩
  have hD : 0 < p.L0 + p.L1 * localRadius p := by
    by_cases h0 : p.L0 = 0
    · have h1 : 0 < p.L1 := by linarith
      positivity
    · have h0' : 0 < p.L0 := lt_of_le_of_ne hL0 (Ne.symm h0)
      positivity
  have hle : p.L0 + p.L1 * localRadius p ≤ localScale p := by
    unfold localScale
    nlinarith [mul_nonneg hα hU.le]
  refine ⟨hD, hle, hD.trans_le hle, ?_⟩
  unfold localScale
  nlinarith

lemma guard_curvature_pos (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    0 < p.L0 + p.L1 * guardRadius p := by
  have hlocal := (localScale_bounds p hv hcurv).1
  have hUM := (guardRadius_bounds p hv).2.1
  rcases hv with ⟨_, hL1, _, _, _, _, _, _, _, _, _, _⟩
  nlinarith [mul_le_mul_of_nonneg_left hUM hL1]

lemma tuned_fine_conditions (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    0 < (tunedConfig p).fineStep ∧ p.L1 * (tunedConfig p).fineStep ≤ 1 / 4 ∧
      p.L0 * (tunedConfig p).fineStep ≤ targetAccuracy p / 512 ∧
      p.L0 * (tunedConfig p).fineStep ≤ localRadius p ∧
      2 * (p.L0 + 4 * p.L1 * localRadius p) * (tunedConfig p).fineStep ≤ 31 * targetAccuracy p / 64 ∧
      512 * (p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p)) *
        (tunedConfig p).fineStep ≤ targetAccuracy p / 256 := by
  have he := targetAccuracy_pos p hv
  have heU := (noise_scales p hv).2.2.1
  have hH := localScale_bounds p hv hcurv
  rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, _, _⟩
  exact fine_step_tuning hL0 hL1 he heU hH.2.2.1 hH.2.1 hH.2.2.2

lemma tuned_coarse_conditions (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    0 ≤ (tunedConfig p).coarseCap ∧ p.L1 * (tunedConfig p).coarseCap ≤ 1 / 4 ∧
      p.L0 * (tunedConfig p).coarseCap ≤ guardRadius p / 4 := by
  have hM := (guardRadius_bounds p hv).1
  have hD := guard_curvature_pos p hv hcurv
  rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, _, _⟩
  exact coarse_cap_tuning hL0 hL1 hM hD

lemma tuned_macro_budget (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : δ ≤ p.Δ) :
    δ / (31 * targetAccuracy p * (tunedConfig p).fineStep / 256) + (epochCount p : ℝ) *
      (δ / ((localRadius p) ^ 2 / (8192 * (p.L0 + p.L1 * localRadius p))) +
        2 * (24 * (p.L0 + 4 * p.L1 * localRadius p) * δ / (15 * (localRadius p) ^ 2 / 4)) + 1) <
      (macroCount p : ℝ) * (epochCount p : ℝ) := by
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hH := localScale_bounds p hv hcurv
  have hm : (0 : ℝ) < epochCount p := by exact_mod_cast epochCount_pos p hv
  have hC : p.L0 + 4 * p.L1 * localRadius p ≤ 4 * localScale p := by
    rcases hv with ⟨hL0, _, _, _, _, _, _, _, _, _, _, _⟩
    nlinarith [hH.2.1]
  exact macro_budget_tuning hδ hgap he hU hH.2.2.1 hH.1 hH.2.1 hC hm

lemma tuned_transport_bounds (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    let a := targetAccuracy p / 256
    let ell := confidence p
    let m : ℝ := epochCount p
    let b : ℝ := transportBatchCount p
    let τ := (tunedConfig p).clipThreshold
    let R := 512 * (p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p)) *
      (tunedConfig p).fineStep
    0 < τ ∧ 0 ≤ R ∧ R ≤ a ∧
      m * b * (R ^ p.q / (τ / 2) ^ (p.q - 1) / b) ≤ a ∧
      m * b * ((2 * τ) ^ (2 - p.q) * R ^ p.q / b ^ 2) ≤ a ^ 2 / (256 * ell) ∧
      2 * τ / b = a / (64 * ell) := by
  intro a ell m b τ R
  have he := targetAccuracy_pos p hv
  have hell : 0 < ell := by dsimp [ell]; linarith [confidence_one_le p hv]
  have hm : 0 < m := by dsimp [m]; exact_mod_cast epochCount_pos p hv
  have hb : 0 < b := by dsimp [b]; exact_mod_cast transportBatchCount_pos p
  have hU := localRadius_pos p hv
  have hFine := tuned_fine_conditions p hv hcurv
  have hη := hFine.1
  have ha : 0 < a := by dsimp [a]; positivity
  have hRa : R ≤ a := hFine.2.2.2.2.2
  rcases hv with ⟨hL0, hL1, _, _, hσ, hα, _, _, hq, _, _, _⟩
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsize : 256 * ell * (256 * m) ^ (1 / (p.q - 1)) ≤ b := transportBatchCount_size p
  have hc := transport_clip_tuning ha hell hm hq hsize
  change 0 < b ∧ 0 < τ ∧ m * b * (a ^ p.q / (τ / 2) ^ (p.q - 1) / b) ≤ a ∧
    m * b * ((2 * τ) ^ (2 - p.q) * a ^ p.q / b ^ 2) ≤ a ^ 2 / (256 * ell) ∧
    2 * τ / b = a / (64 * ell) at hc
  have hτ := hc.2.1
  have hp := Real.rpow_le_rpow hR hRa (by linarith : 0 ≤ p.q)
  refine ⟨hτ, hR, hRa, ?_, ?_, hc.2.2.2.2⟩
  · apply le_trans _ hc.2.2.1
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm.le hb.le)
    apply div_le_div_of_nonneg_right _ hb.le
    exact div_le_div_of_nonneg_right hp (by positivity)
  · apply le_trans _ hc.2.2.2.1
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm.le hb.le)
    apply div_le_div_of_nonneg_right _ (sq_nonneg b)
    exact mul_le_mul_of_nonneg_left hp (by positivity)

lemma tuned_transport_energy (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1) :
    let a := targetAccuracy p / 256
    let ell := confidence p
    let m : ℝ := epochCount p
    let b : ℝ := transportBatchCount p
    let τ := (tunedConfig p).clipThreshold
    let R := 512 * (p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p)) *
      (tunedConfig p).fineStep
    let C := 2 * τ / b
    let V := (2 * τ) ^ (2 - p.q) * R ^ p.q / b ^ 2
    let θ := 2 * ell / a ^ 2
    0 ≤ C ∧ 0 ≤ V ∧ 0 ≤ θ ∧ θ * (2 * a * C + C ^ 2) ≤ 1 ∧
      (m * b) * ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2 ≤ -ell := by
  intro a ell m b τ R C V θ
  have he := targetAccuracy_pos p hv
  have hell : 1 ≤ ell := confidence_one_le p hv
  have ha : 0 < a := by dsimp [a]; positivity
  have hm : 0 < m := by dsimp [m]; exact_mod_cast epochCount_pos p hv
  have hb : 0 < b := by dsimp [b]; exact_mod_cast transportBatchCount_pos p
  have ht := tuned_transport_bounds p hv hcurv
  change 0 < τ ∧ 0 ≤ R ∧ R ≤ a ∧ _ at ht
  have hτ := ht.1
  have hR := ht.2.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hNV : m * b * V ≤ a ^ 2 / (256 * ell) := ht.2.2.2.2.1
  have hh := transport_energy_tuning ha hell (mul_nonneg hm.le hb.le) hV hNV
  change _ ∧ _ at hh
  have hCe : C = a / (64 * ell) := ht.2.2.2.2.2
  refine ⟨hC, hV, hθ, ?_, ?_⟩
  · simpa only [hCe] using hh.1
  · simpa only [hCe] using hh.2

end LongTails.Proofs.HystereticHessianParameters
