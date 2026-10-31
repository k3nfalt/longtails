import LongTails.Algorithms.HeavyTailedSospTuned
import LongTails.Proofs.HeavyTailedSospConvergence
import LongTails.Proofs.HeavyTailedSpectralTuning

namespace LongTails.Proofs.HeavyTailedSospTuning

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned

lemma accuracy_pos (p : Params) (hε : 0 < p.ε) : 0 < accuracy p := by
  unfold accuracy
  positivity

lemma curvature_pos (p : Params) (hρ : 0 < p.ρ) (hε : 0 < p.ε) : 0 < curvature p :=
  Real.sqrt_pos.mpr (mul_pos hρ (accuracy_pos p hε))

lemma curvature_sq (p : Params) (hρ : 0 ≤ p.ρ) (hε : 0 ≤ p.ε) :
    curvature p ^ 2 = p.ρ * accuracy p := by
  apply Real.sq_sqrt
  unfold accuracy
  positivity

lemma stepSize_pos (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    0 < stepSize p := by
  unfold stepSize
  exact div_pos (accuracy_pos p hε) (mul_pos (by norm_num) (add_pos hL (curvature_pos p hρ hε)))

lemma ncLength_pos (p : Params) (hρ : 0 < p.ρ) (hε : 0 < p.ε) : 0 < ncLength p :=
  div_pos (curvature_pos p hρ hε) hρ

lemma curvature_length (p : Params) (hρ : 0 < p.ρ) (hε : 0 ≤ p.ε) :
    curvature p * ncLength p = accuracy p := by
  unfold ncLength
  have hh := curvature_sq p hρ.le hε
  rw [← mul_div_assoc]
  apply (div_eq_iff hρ.ne').mpr
  nlinarith

lemma rho_length (p : Params) (hρ : 0 < p.ρ) : p.ρ * ncLength p = curvature p := by
  unfold ncLength
  field_simp

lemma stepSize_le_length (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    stepSize p ≤ ncLength p := by
  have hγ := curvature_pos p hρ hε
  have hs := ncLength_pos p hρ hε
  have he := curvature_length p hρ hε.le
  unfold stepSize
  apply (div_le_iff₀ (by positivity : 0 < 100 * (p.L + curvature p))).mpr
  nlinarith [mul_pos hL hs]

lemma rho_stepSize_le_curvature (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    p.ρ * stepSize p ≤ curvature p := by
  rw [← rho_length p hρ]
  exact mul_le_mul_of_nonneg_left (stepSize_le_length p hL hρ hε) hρ.le

lemma curvature_accuracy (p : Params) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    5 * curvature p = Real.sqrt (p.ρ * p.ε) := by
  have hγ := curvature_pos p hρ hε
  have hsq := curvature_sq p hρ.le hε.le
  have hr := Real.sq_sqrt (mul_nonneg hρ.le hε.le)
  have hn := Real.sqrt_nonneg (p.ρ * p.ε)
  unfold accuracy at hsq
  nlinarith

lemma errorScale_pos (p : Params) (hε : 0 < p.ε) : 0 < errorScale p :=
  div_pos (accuracy_pos p hε) (by norm_num)

lemma smooth_step_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    p.L * stepSize p ≤ accuracy p / 100 := by
  have ha := accuracy_pos p hε
  have hγ := curvature_pos p hρ hε
  unfold stepSize
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 100 * (p.L + curvature p))).mpr
  nlinarith [mul_pos ha hγ]

lemma cycleCount_pos (p : Params) : 0 < cycleCount p := by unfold cycleCount; omega

lemma cycle_gap_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    p.Δ ≤ (cycleCount p : ℝ) * stepSize p * accuracy p / 100 := by
  have hh := stepSize_pos p hL hρ hε
  have ha := accuracy_pos p hε
  have hc : (⌈100 * p.Δ / (stepSize p * accuracy p)⌉₊ : ℝ) ≤ cycleCount p := by
    exact_mod_cast (le_max_right 1 ⌈100 * p.Δ / (stepSize p * accuracy p)⌉₊)
  have hb := (Nat.le_ceil (100 * p.Δ / (stepSize p * accuracy p))).trans hc
  have hm := (div_le_iff₀ (mul_pos hh ha)).mp hb
  nlinarith

lemma ncSegments_pos (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    0 < ncSegments p := by
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (ncLength_pos p hρ hε) (stepSize_pos p hL hρ hε)

lemma ncSegments_bounds (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    ncLength p / (max 1 (ncSegments p) : ℕ) ≤ stepSize p ∧
      (max 1 (ncSegments p) : ℕ) * stepSize p ≤ 2 * ncLength p := by
  have hh := stepSize_pos p hL hρ hε
  have hs := ncLength_pos p hρ hε
  have hM := ncSegments_pos p hL hρ hε
  rw [max_eq_right hM]
  have hMr : (0 : ℝ) < ncSegments p := by exact_mod_cast hM
  have hlo := Nat.le_ceil (ncLength p / stepSize p)
  have hhi := (Nat.ceil_lt_add_one (le_of_lt (div_pos hs hh))).le
  change ncLength p / stepSize p ≤ (ncSegments p : ℝ) at hlo
  change (ncSegments p : ℝ) ≤ ncLength p / stepSize p + 1 at hhi
  have hl := (div_le_iff₀ hh).mp hlo
  have hu := mul_le_mul_of_nonneg_right hhi hh.le
  have he : ncLength p / stepSize p * stepSize p = ncLength p := div_mul_cancel₀ _ hh.ne'
  have hhs := stepSize_le_length p hL hρ hε
  constructor
  · apply (div_le_iff₀ hMr).mpr
    nlinarith
  · nlinarith

lemma missRisk_pos (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    0 < missRisk p := by
  have hh := stepSize_pos p hL hρ hε
  have ha := accuracy_pos p hε
  have hs := ncLength_pos p hρ hε
  have hγ := curvature_pos p hρ hε
  unfold missRisk
  positivity

lemma missRisk_le (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    missRisk p ≤ 1 / 100 := by
  have hh := stepSize_pos p hL hρ hε
  have ha := accuracy_pos p hε
  have hs := ncLength_pos p hρ hε
  have hγ := curvature_pos p hρ hε
  have hhs := stepSize_le_length p hL hρ hε
  have he := curvature_length p hρ hε.le
  have hb := mul_le_mul_of_nonneg_right hhs ha.le
  unfold missRisk
  apply (div_le_iff₀ (by positivity : 0 < 100 * (p.L + curvature p) * ncLength p ^ 2)).mpr
  rw [← he] at hb
  nlinarith [mul_nonneg hL.le (sq_nonneg (ncLength p))]

lemma false_acceptance_remainder (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    ((p.L + curvature p) * ncLength p ^ 2 / 2) * (missRisk p / 2) =
      stepSize p * accuracy p / 400 := by
  have hs := ncLength_pos p hρ hε
  have hsum := add_pos hL (curvature_pos p hρ hε)
  unfold missRisk
  field_simp
  ring

lemma conjugate_holder (p : Params) (hp : 1 < p.p) : p.p.HolderConjugate (conjugate p) :=
  (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl

lemma conjugate_ge_two (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2) : 2 ≤ conjugate p := by
  unfold conjugate
  apply (le_div_iff₀ (by linarith : 0 < p.p - 1)).mpr
  linarith

lemma momentConstant_pos (p : Params) (hp : 1 < p.p) : 0 < momentConstant p := by
  unfold momentConstant conjugate
  positivity

lemma resetScale_ge_one (p : Params) (hp : 1 < p.p) (hσ : 0 ≤ p.σg) (hε : 0 < p.ε) :
    1 ≤ resetScale p := by
  have hK := momentConstant_pos p hp
  have he := errorScale_pos p hε
  unfold resetScale
  have hb : 0 ≤ momentConstant p * p.σg / errorScale p := by positivity
  linarith

lemma transportScale_nonneg (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) : 0 ≤ transportScale p := by
  have hK := momentConstant_pos p hp
  have he := errorScale_pos p hε
  have hh := stepSize_pos p hL hρ hε
  unfold transportScale transportNoise
  positivity

lemma epochCount_pos (p : Params) : 0 < epochCount p := by unfold epochCount; omega

lemma epochCount_le_cycles (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    epochCount p ≤ cycleCount p := by
  have ha : 0 < resetScale p := lt_of_lt_of_le (by norm_num) (resetScale_ge_one p hp hσg hε)
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hT := cycleCount_pos p
  have hTr : (0 : ℝ) < cycleCount p := by exact_mod_cast hT
  have hden : 0 < resetScale p + cycleCount p * transportScale p := by positivity
  have hn : 0 ≤ (cycleCount p : ℝ) * resetScale p / (resetScale p + cycleCount p * transportScale p) := by positivity
  have hr : (cycleCount p : ℝ) * resetScale p / (resetScale p + cycleCount p * transportScale p) ≤ cycleCount p := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg (cycleCount p : ℝ)) hz]
  unfold epochCount
  apply max_le hT
  exact_mod_cast (Nat.floor_le hn).trans hr

lemma epoch_inverse_bound (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    1 / (epochCount p : ℝ) ≤ 2 / (cycleCount p : ℝ) + 2 * transportScale p / resetScale p := by
  have ha : 0 < resetScale p := lt_of_lt_of_le (by norm_num) (resetScale_ge_one p hp hσg hε)
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hTr : (0 : ℝ) < cycleCount p := by exact_mod_cast cycleCount_pos p
  have hqr : (0 : ℝ) < epochCount p := by exact_mod_cast epochCount_pos p
  have hq1 : (1 : ℝ) ≤ epochCount p := by exact_mod_cast epochCount_pos p
  have hden : 0 < resetScale p + cycleCount p * transportScale p := by positivity
  have hf := Nat.lt_floor_add_one
    ((cycleCount p : ℝ) * resetScale p / (resetScale p + cycleCount p * transportScale p))
  have hfloor : (⌊(cycleCount p : ℝ) * resetScale p /
      (resetScale p + cycleCount p * transportScale p)⌋₊ : ℝ) ≤ epochCount p := by
    exact_mod_cast le_max_right 1 ⌊(cycleCount p : ℝ) * resetScale p /
      (resetScale p + cycleCount p * transportScale p)⌋₊
  have hr : (cycleCount p : ℝ) * resetScale p /
      (resetScale p + cycleCount p * transportScale p) ≤ 2 * epochCount p := by linarith
  have hb := (div_le_iff₀ hden).mp hr
  apply (div_le_iff₀ hqr).mpr
  apply (mul_le_mul_iff_left₀ (mul_pos hTr ha)).mp
  field_simp
  nlinarith

lemma probeConstant_eq (p : Params) : probeConstant p = (1 / 4 : ℝ) ^ conjugate p / 16 := by
  simp only [probeConstant, one_div]
  rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]

lemma probeConstant_pos (p : Params) : 0 < probeConstant p := by
  unfold probeConstant
  positivity

lemma validationBatch_bound (p : Params) (hp : 1 < p.p) (hρ : 0 < p.ρ)
    (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    0 < validationBatch p ∧ 6 * p.σh ^ p.p / (validationBatch p : ℝ) ^ (p.p - 1) ≤
      (curvature p / 8) ^ p.p := by
  exact HeavyTailedRayleighValidation.batch_count_tuning hp hσ
    (div_pos (curvature_pos p hρ hε) (by norm_num))

lemma repeatCount_pos (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    0 < repeatCount p := by
  have hc := probeConstant_pos p
  have hδ := missRisk_pos p hL hρ hε
  have hδu := missRisk_le p hL hρ hε
  have hl : 0 < Real.log (2 / missRisk p) := Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  apply Nat.one_le_ceil_iff.mpr
  positivity

lemma repetition_failure_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    Real.exp (-((1 / 4 : ℝ) ^ conjugate p / 64) * (max 1 (repeatCount p) : ℕ)) ≤ missRisk p / 2 := by
  have hc := probeConstant_pos p
  have hδ := missRisk_pos p hL hρ hε
  have he : Real.log (2 / missRisk p) / ((1 / 4 : ℝ) ^ conjugate p / 64) =
      (4 / probeConstant p) * Real.log (2 / missRisk p) := by
    rw [probeConstant_eq]
    field_simp
    ring
  have hh := HeavyTailedSospDetection.probe_repetition_tuning
    ((1 / 4 : ℝ) ^ conjugate p / 64) (missRisk p) (by positivity) hδ
  rw [he] at hh
  exact hh

lemma validation_failure_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (max 1 (repeatCount p) : ℕ) * Real.exp (-((max 1 (validationGroups p) : ℕ) : ℝ) / 8) ≤
      missRisk p / 2 := by
  have hR := repeatCount_pos p hL hρ hε
  have hm : 0 < validationGroups p := by unfold validationGroups; omega
  rw [max_eq_right hR, max_eq_right hm]
  have hh := HeavyTailedRayleighValidation.validation_group_tuning (repeatCount p) hR
    (missRisk p) (missRisk_pos p hL hρ hε)
  change Real.exp (-(validationGroups p : ℝ) / 8) ≤ missRisk p / (2 * (repeatCount p : ℝ)) at hh
  have hRr : (0 : ℝ) < repeatCount p := by exact_mod_cast hR
  have hb := (le_div_iff₀ (by positivity : 0 < 2 * (repeatCount p : ℝ))).mp hh
  nlinarith

lemma spectral_tuning_bounds (p : Params) (hd : 0 < p.d) (hp : 1 < p.p)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    0 < spectralStep p ∧ spectralStep p * (2 * p.L + curvature p) ≤ 1 ∧
      0 < probeSteps p ∧
      8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤
        spectralStep p * (max 1 (probeSteps p) : ℕ) * curvature p ∧
      (max 1 (probeSteps p) : ℕ) * (spectralStep p ^ p.p * p.σh ^ p.p) ≤
        (1 / 4 : ℝ) ^ conjugate p / 256 ∧
      ∀ ell, 0 ≤ ell → ell ≤ 2 * p.L + curvature p →
        ((1 + spectralStep p * ell) ^ p.p + 6 * spectralStep p ^ p.p * p.σh ^ p.p) ^ max 1 (probeSteps p) ≤
          (2 * (1 + spectralStep p * ell) ^ max 1 (probeSteps p)) ^ p.p := by
  have hγ := curvature_pos p hρ hε
  have hh := HeavyTailedSpectralTuning.probe_tuning hd
    (by positivity : 0 < 2 * p.L + curvature p) hγ hσ (conjugate_holder p hp)
    (by linarith : curvature p ≤ 2 * p.L + curvature p)
  simp only [← probeConstant_eq p] at hh
  change 0 < spectralStep p ∧ spectralStep p * (2 * p.L + curvature p) ≤ 1 ∧
    0 < probeSteps p ∧
    8 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2) ≤ spectralStep p * (probeSteps p : ℕ) * curvature p ∧
    (probeSteps p : ℕ) * (spectralStep p ^ p.p * p.σh ^ p.p) ≤ (1 / 4 : ℝ) ^ conjugate p / 256 ∧
    ∀ ell, 0 ≤ ell → ell ≤ 2 * p.L + curvature p →
      ((1 + spectralStep p * ell) ^ p.p + 6 * spectralStep p ^ p.p * p.σh ^ p.p) ^ probeSteps p ≤
        (2 * (1 + spectralStep p * ell) ^ probeSteps p) ^ p.p at hh
  have hn : 1 ≤ probeSteps p := hh.2.2.1
  simpa only [max_eq_right hn] using hh

lemma conjugate_mul (p : Params) (hp : 1 < p.p) :
    conjugate p * (p.p - 1) = p.p := by
  unfold conjugate
  exact div_mul_cancel₀ _ (by linarith)

lemma conjugate_sub_mul (p : Params) (hp : 1 < p.p) :
    (conjugate p - 1) * (p.p - 1) = 1 := by
  have hh := conjugate_mul p hp
  nlinarith

lemma resetBatch_power (p : Params) (hp : 1 < p.p) (hσg : 0 ≤ p.σg)
    (hε : 0 < p.ε) :
    resetScale p ^ p.p ≤ (resetBatch p : ℝ) ^ (p.p - 1) := by
  have ha : 0 ≤ resetScale p := le_trans (by norm_num) (resetScale_ge_one p hp hσg hε)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg ha (conjugate p))
    (Nat.le_ceil (resetScale p ^ conjugate p)) (by linarith : 0 ≤ p.p - 1)
  rw [← Real.rpow_mul ha, conjugate_mul p hp] at hh
  exact hh

lemma transportBatch_power (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (epochCount p : ℝ) * transportScale p ^ p.p ≤
      (transportBatch p : ℝ) ^ (p.p - 1) := by
  have hq : (0 : ℝ) ≤ epochCount p := Nat.cast_nonneg _
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hx : 0 ≤ (epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p :=
    mul_nonneg (Real.rpow_nonneg hq _) (Real.rpow_nonneg hz _)
  have hb : (epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p ≤
      (transportBatch p : ℝ) := by
    have hh := Nat.le_ceil ((epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p)
    unfold transportBatch
    push_cast
    linarith
  have hh := Real.rpow_le_rpow hx hb (by linarith : 0 ≤ p.p - 1)
  rw [Real.mul_rpow (Real.rpow_nonneg hq _) (Real.rpow_nonneg hz _),
    ← Real.rpow_mul hq, ← Real.rpow_mul hz, conjugate_sub_mul p hp,
    conjugate_mul p hp, Real.rpow_one] at hh
  exact hh

lemma weighted_power_bound {u v a : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 1 ≤ a) : u ^ a + 6 * v ^ a ≤ (7 * (u + v)) ^ a := by
  have hs : 0 ≤ u + v := add_nonneg hu hv
  have h1 := Real.rpow_le_rpow hu (le_add_of_nonneg_right hv) (by linarith : 0 ≤ a)
  have h2 := Real.rpow_le_rpow hv (le_add_of_nonneg_left hu) (by linarith : 0 ≤ a)
  have h7 := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 7) ha
  have h3 := mul_le_mul_of_nonneg_right h7 (Real.rpow_nonneg hs a)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) hs]
  linarith

lemma transportNoise_power (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (p.ρ * stepSize p ^ 2) ^ p.p + 6 * p.σh ^ p.p * stepSize p ^ p.p ≤
      (transportNoise p * stepSize p) ^ p.p := by
  have hh := stepSize_pos p hL hρ hε
  have hb := weighted_power_bound (mul_nonneg hρ.le (sq_nonneg (stepSize p)))
    (mul_nonneg hσh hh.le) hp.le
  rw [Real.mul_rpow hσh hh.le] at hb
  have he : 7 * (p.ρ * stepSize p ^ 2 + p.σh * stepSize p) =
      transportNoise p * stepSize p := by unfold transportNoise; ring
  rw [he] at hb
  nlinarith

lemma moment_root_bound {x t a : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (ha : 1 < a)
    (hb : x ≤ 6 * t ^ a) : x ^ (1 / a) ≤ 6 * t := by
  have h6 := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 6) ha.le
  have hc : x ≤ (6 * t) ^ a := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) ht]
    exact hb.trans (mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg ht a))
  have hh := Real.rpow_le_rpow hx hc (by positivity : 0 ≤ 1 / a)
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 6 * t),
    mul_one_div_cancel (by linarith : a ≠ 0), Real.rpow_one] at hh
  exact hh

lemma resetBatch_pos (p : Params) (hp : 1 < p.p) (hσg : 0 ≤ p.σg)
    (hε : 0 < p.ε) : 0 < resetBatch p := by
  have ha : 0 < resetScale p := lt_of_lt_of_le (by norm_num) (resetScale_ge_one p hp hσg hε)
  exact Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos ha _)

lemma reset_moment_bound (p : Params) (hp : 1 < p.p) (hσg : 0 ≤ p.σg)
    (hε : 0 < p.ε) :
    6 * p.σg ^ p.p / (resetBatch p : ℝ) ^ (p.p - 1) ≤
      6 * (errorScale p / momentConstant p) ^ p.p := by
  have he := errorScale_pos p hε
  have hK := momentConstant_pos p hp
  have hB : (0 : ℝ) < resetBatch p := by exact_mod_cast resetBatch_pos p hp hσg hε
  have ha := resetScale_ge_one p hp hσg hε
  have ht : 0 ≤ errorScale p / momentConstant p := by positivity
  have hs : p.σg ≤ (errorScale p / momentConstant p) * resetScale p := by
    unfold resetScale
    field_simp
    nlinarith
  have hpow := Real.rpow_le_rpow hσg hs (by linarith : 0 ≤ p.p)
  rw [Real.mul_rpow ht (by linarith : 0 ≤ resetScale p)] at hpow
  have hden := resetBatch_power p hp hσg hε
  have hb := mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg ht p.p)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hB _)).mpr
  nlinarith

lemma transportBatch_pos (p : Params) : 0 < transportBatch p := by
  unfold transportBatch
  omega

lemma transport_moment_bound (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    6 * (epochCount p : ℝ) *
      ((p.ρ * stepSize p ^ 2) ^ p.p + 6 * p.σh ^ p.p * stepSize p ^ p.p) /
        (transportBatch p : ℝ) ^ (p.p - 1) ≤
      6 * (errorScale p / momentConstant p) ^ p.p := by
  have he := errorScale_pos p hε
  have hK := momentConstant_pos p hp
  have hh := stepSize_pos p hL hρ hε
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hq : (0 : ℝ) ≤ epochCount p := Nat.cast_nonneg _
  have hb : (0 : ℝ) < transportBatch p := by exact_mod_cast transportBatch_pos p
  have ht : 0 ≤ errorScale p / momentConstant p := by positivity
  have hid : transportNoise p * stepSize p =
      (errorScale p / momentConstant p) * transportScale p := by
    unfold transportScale
    field_simp
  have hraw := transportNoise_power p hp hL hρ hσh hε
  rw [hid, Real.mul_rpow ht hz] at hraw
  have hden := transportBatch_power p hp hL hρ hσh hε
  have h1 := mul_le_mul_of_nonneg_left hraw hq
  have h2 := mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg ht p.p)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hb _)).mpr
  nlinarith

lemma estimator_root_bound (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh)
    (hε : 0 < p.ε) :
    (6 * p.σg ^ p.p / (resetBatch p : ℝ) ^ (p.p - 1)) ^ (1 / p.p) +
      (6 * (epochCount p : ℝ) *
        ((p.ρ * stepSize p ^ 2) ^ p.p + 6 * p.σh ^ p.p * stepSize p ^ p.p) /
          (transportBatch p : ℝ) ^ (p.p - 1)) ^ (1 / p.p) ≤ errorScale p := by
  have he := errorScale_pos p hε
  have hK := momentConstant_pos p hp
  have hh := stepSize_pos p hL hρ hε
  have ht : 0 ≤ errorScale p / momentConstant p := by positivity
  have h1 := moment_root_bound (by positivity) ht hp (reset_moment_bound p hp hσg hε)
  have h2 := moment_root_bound (by positivity) ht hp (transport_moment_bound p hp hL hρ hσh hε)
  have hr := conjugate_ge_two p hp hp2
  have h12 : 12 ≤ momentConstant p := by unfold momentConstant; linarith
  have hscale : 12 * (errorScale p / momentConstant p) ≤ errorScale p := by
    apply (mul_le_mul_iff_right₀ hK).mp
    field_simp
    nlinarith
  linarith

lemma estimator_tuning (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh)
    (hε : 0 < p.ε) :
    (6 * p.σg ^ p.p / ((max 1 (config p).resetBatch : ℕ) : ℝ) ^ (p.p - 1)) ^ (1 / p.p) +
      (6 * ((max 1 (config p).epoch * max 1 (config p).transportBatch : ℕ) : ℝ) *
        (((max 1 (config p).transportBatch : ℕ) : ℝ)⁻¹ ^ p.p *
          ((p.ρ * (config p).h ^ 2) ^ p.p + 6 * p.σh ^ p.p * (config p).h ^ p.p))) ^ (1 / p.p) ≤
      errorScale p := by
  have hB : 1 ≤ resetBatch p := resetBatch_pos p hp hσg hε
  have hb : 1 ≤ transportBatch p := transportBatch_pos p
  have hq : 1 ≤ epochCount p := epochCount_pos p
  simp only [config, max_eq_right hB, max_eq_right hb, max_eq_right hq, Nat.cast_mul]
  have hbr : (0 : ℝ) < transportBatch p := by exact_mod_cast hb
  have hid :
      6 * ((epochCount p : ℝ) * (transportBatch p : ℝ)) *
        ((transportBatch p : ℝ)⁻¹ ^ p.p *
          ((p.ρ * stepSize p ^ 2) ^ p.p + 6 * p.σh ^ p.p * stepSize p ^ p.p)) =
      6 * (epochCount p : ℝ) *
        ((p.ρ * stepSize p ^ 2) ^ p.p + 6 * p.σh ^ p.p * stepSize p ^ p.p) /
          (transportBatch p : ℝ) ^ (p.p - 1) := by
    rw [Real.inv_rpow hbr.le, Real.rpow_sub_one hbr.ne']
    field_simp
  rw [hid]
  exact estimator_root_bound p hp hp2 hL hρ hσg hσh hε

lemma configured_average_bounds (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε)
    (G A : ℝ) (hG : 0 ≤ G) (hA : 0 ≤ A)
    (hmain : stepSize p * G +
      (curvature p * ncLength p ^ 2 / 2 -
        2 * stepSize p * errorScale p * (max 1 (ncSegments p) : ℕ)) * A ≤
      p.Δ + 2 * stepSize p * errorScale p * ((cycleCount p : ℝ) + max 1 (epochCount p)) +
        p.L * stepSize p ^ 2 / 2 * cycleCount p +
          ((p.L + curvature p) * ncLength p ^ 2 / 2) * (missRisk p / 2) * cycleCount p) :
    G / (cycleCount p : ℝ) ≤ p.ε / 500 ∧
      A / (cycleCount p : ℝ) ≤ stepSize p / (5 * ncLength p) := by
  have hh := stepSize_pos p hL hρ hε
  have hs := ncLength_pos p hρ hε
  have he := errorScale_pos p hε
  have hε0 := accuracy_pos p hε
  have hT : (0 : ℝ) < cycleCount p := by exact_mod_cast cycleCount_pos p
  have hseg := ncSegments_bounds p hL hρ hε
  have hq : ((max 1 (epochCount p) : ℕ) : ℝ) ≤ cycleCount p := by
    rw [max_eq_right (show 1 ≤ epochCount p from epochCount_pos p)]
    exact_mod_cast epochCount_le_cycles p hp hL hρ hσg hσh hε
  have hc := HeavyTailedSospForecastIntegration.outer_coefficient_bound he.le hs.le
    (by nlinarith [hseg.2] : stepSize p * (max 1 (ncSegments p) : ℕ) ≤ 2 * ncLength p)
    (show errorScale p ≤ accuracy p / 10000 from le_rfl)
  have hid : curvature p * ncLength p ^ 2 = accuracy p * ncLength p := by
    nlinarith [curvature_length p hρ hε.le]
  have hc' : accuracy p * ncLength p / 4 ≤ curvature p * ncLength p ^ 2 / 2 -
      2 * stepSize p * errorScale p * (max 1 (ncSegments p) : ℕ) := by
    rw [hid]
    exact hc
  have hr := HeavyTailedSospForecastIntegration.outer_remainder_bound hh.le he.le hT.le hε0.le
    hq (show errorScale p ≤ accuracy p / 10000 from le_rfl)
    (smooth_step_bound p hL hρ hε) (cycle_gap_bound p hL hρ hε)
    (le_of_eq (false_acceptance_remainder p hL hρ hε))
  have havg := HeavyTailedSospForecastIntegration.outer_average_bounds hh hs hε0 hT hG hA hc' hr hmain
  constructor
  · have heq : accuracy p / 20 = p.ε / 500 := by unfold accuracy; ring
    simpa only [heq] using havg.1
  · exact havg.2

end LongTails.Proofs.HeavyTailedSospTuning
