import LongTails.Proofs.HeavyTailedSospDetectorCost

namespace LongTails.Proofs.HeavyTailedSospSpectralCost

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned
open HeavyTailedSospTuning HeavyTailedSospCost HeavyTailedSospDetectorCost

lemma dimension_log_ge_one (p : Params) (hd : 0 < p.d) :
    1 ≤ Real.log (2 + (p.d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ p.d := by exact_mod_cast hd
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ 2 + p.d)
  have h3 := Real.log_three_gt_d9
  linarith

lemma dimensionScale_public_upper (p : Params) (hd : 0 < p.d) :
    dimensionScale p ≤ 16 * Real.log (2 + (p.d : ℝ)) := by
  have hd0 : (0 : ℝ) < p.d := by exact_mod_cast hd
  have hD := dimension_log_ge_one p hd
  have hlogd := Real.log_le_log hd0 (by linarith : (p.d : ℝ) ≤ 2 + p.d)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  unfold dimensionScale
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.sqrt (2 * p.d) ≠ 0),
    Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * p.d),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hd0.ne']
  linarith

lemma dimensionScale_pos (p : Params) (hd : 0 < p.d) : 0 < dimensionScale p := by
  have hd1 : (1 : ℝ) ≤ p.d := by exact_mod_cast hd
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * p.d) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hl : 0 ≤ Real.log (2 * Real.sqrt (2 * p.d)) := Real.log_nonneg (by nlinarith)
  unfold dimensionScale
  linarith

lemma conjugate_sub_one (p : Params) (hp : 1 < p.p) : conjugate p - 1 = 1 / (p.p - 1) := by
  unfold conjugate
  field_simp [show p.p - 1 ≠ 0 by linarith]
  ring

lemma spectral_noise_factor {K σ γ a : ℝ} (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hγ : 0 < γ) (ha : 1 < a) :
    (K * σ ^ a / γ) ^ (1 / (a - 1)) / γ =
      K ^ (1 / (a - 1)) * (σ / γ) ^ (a / (a - 1)) := by
  let q := 1 / (a - 1)
  have hq : a / (a - 1) = a * q := by dsimp [q]; ring
  have hq1 : a * q = q + 1 := by dsimp [q]; field_simp [show a - 1 ≠ 0 by linarith]; ring
  have hpow : γ ^ q * γ = γ ^ (a * q) := by
    rw [hq1, Real.rpow_add_one hγ.ne']
  change (K * σ ^ a / γ) ^ q / γ = _
  rw [Real.div_rpow (mul_nonneg hK (Real.rpow_nonneg hσ _)) hγ.le,
    Real.mul_rpow hK (Real.rpow_nonneg hσ _), ← Real.rpow_mul hσ,
    hq, Real.div_rpow hσ hγ.le]
  rw [div_div, hpow]
  ring

lemma probeSteps_separated_upper (p : Params) (hd : 0 < p.d) (hp : 1 < p.p)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (probeSteps p : ℝ) ≤ 1 + 2 * dimensionScale p * ((2 * p.L + curvature p) / curvature p) +
      2 * dimensionScale p * (256 * dimensionScale p / probeConstant p) ^ (conjugate p - 1) *
        (p.σh / curvature p) ^ conjugate p := by
  have hD := dimensionScale_pos p hd
  have hc := probeConstant_pos p
  have hγ := curvature_pos p hρ hε
  have hη := (spectral_tuning_bounds p hd hp hL hρ hσ hε).1
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * dimensionScale p / (spectralStep p * curvature p))
  change (probeSteps p : ℝ) < 2 * dimensionScale p / (spectralStep p * curvature p) + 1 at hceil
  have hnoise := spectral_noise_factor (by positivity : 0 ≤ 256 * dimensionScale p / probeConstant p) hσ hγ hp
  have hbase : (256 * dimensionScale p / probeConstant p) * p.σh ^ p.p / curvature p =
      256 * dimensionScale p * p.σh ^ p.p / (probeConstant p * curvature p) := by ring
  rw [hbase, ← conjugate_sub_one p hp] at hnoise
  change _ = (256 * dimensionScale p / probeConstant p) ^ (conjugate p - 1) *
    (p.σh / curvature p) ^ conjugate p at hnoise
  have hid : 2 * dimensionScale p / (spectralStep p * curvature p) =
      2 * dimensionScale p * ((2 * p.L + curvature p) / curvature p) +
      2 * dimensionScale p * ((256 * dimensionScale p * p.σh ^ p.p /
        (probeConstant p * curvature p)) ^ (1 / (p.p - 1)) / curvature p) := by
    unfold spectralStep
    field_simp
  rw [hid, ← conjugate_sub_one p hp, hnoise] at hceil
  nlinarith

lemma shifted_ratio_upper (p : Params) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (2 * p.L + curvature p) / curvature p ≤
      10 * ((p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)) := by
  have hγ := curvature_pos p hρ hε
  have he := curvature_accuracy p hρ hε
  rw [← he]
  apply (div_le_iff₀ hγ).mpr
  field_simp
  nlinarith

lemma deterministic_probe_cost_upper (p : Params) (hd : 0 < p.d)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    1 + 2 * dimensionScale p * ((2 * p.L + curvature p) / curvature p) ≤
      321 * Real.log (2 + (p.d : ℝ)) *
        ((p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)) := by
  let D := Real.log (2 + (p.d : ℝ))
  let V := (p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)
  have hD : 1 ≤ D := dimension_log_ge_one p hd
  have hΓ : 0 < Real.sqrt (p.ρ * p.ε) := Real.sqrt_pos.mpr (mul_pos hρ hε)
  have hV : 1 ≤ V := by dsimp [V]; apply (le_div_iff₀ hΓ).mpr; linarith
  have hγ := curvature_pos p hρ hε
  have h1 := dimensionScale_public_upper p hd
  have h2 := shifted_ratio_upper p hρ hε
  have hm := mul_le_mul h1 h2 (by positivity : 0 ≤ (2 * p.L + curvature p) / curvature p)
    (by positivity : 0 ≤ 16 * D)
  have hprod : 1 ≤ D * V := by nlinarith
  change 1 + 2 * dimensionScale p * ((2 * p.L + curvature p) / curvature p) ≤ 321 * D * V
  change dimensionScale p * ((2 * p.L + curvature p) / curvature p) ≤ 16 * D * (10 * V) at hm
  nlinarith

lemma spectral_noise_base_upper (p : Params) (hd : 0 < p.d) :
    256 * dimensionScale p / probeConstant p ≤
      (2 : ℝ) ^ (2 * conjugate p + 16) * Real.log (2 + (p.d : ℝ)) := by
  have hc := probeConstant_pos p
  have hD := dimension_log_ge_one p hd
  have hb := mul_le_mul_of_nonneg_left (dimensionScale_public_upper p hd)
    (by positivity : 0 ≤ 64 * (4 / probeConstant p))
  rw [probe_reciprocal_power] at hb
  have hid : 64 * (2 : ℝ) ^ (2 * conjugate p + 6) * 16 = (2 : ℝ) ^ (2 * conjugate p + 16) := by
    rw [show 2 * conjugate p + 16 = (2 * conjugate p + 6) + 10 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) (2 * conjugate p + 6) 10]
    norm_num
    ring
  have hleft : 64 * (2 : ℝ) ^ (2 * conjugate p + 6) * dimensionScale p =
      256 * dimensionScale p / probeConstant p := by
    rw [← probe_reciprocal_power]
    ring
  rw [hleft] at hb
  calc
    _ ≤ 64 * (2 : ℝ) ^ (2 * conjugate p + 6) * (16 * Real.log (2 + (p.d : ℝ))) := hb
    _ = _ := by rw [← mul_assoc, hid]

lemma spectral_noise_constant {r : ℝ} (hr : 2 ≤ r) :
    32 * ((2 : ℝ) ^ (2 * r + 16)) ^ (r - 1) * (8 : ℝ) ^ r ≤ (2 : ℝ) ^ (13 * r ^ 2) := by
  have h8 : (8 : ℝ) ^ r = (2 : ℝ) ^ (3 * r) := by
    have hh := Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 3 r
    norm_num at hh
    exact hh.symm
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), h8]
  have h32 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
  rw [h32, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [sq_nonneg (r - 2)]

lemma spectral_noise_scale_bound {r D0 B y D X : ℝ} (hr : 2 ≤ r)
    (hB : 0 ≤ B) (hy : 0 ≤ y) (hD : 0 < D) (hX : 0 ≤ X)
    (hDim : D0 ≤ 16 * D) (hBase : B ≤ (2 : ℝ) ^ (2 * r + 16) * D) (hNoise : y ≤ 8 * X) :
    2 * D0 * B ^ (r - 1) * y ^ r ≤ (2 : ℝ) ^ (13 * r ^ 2) * D ^ r * X ^ r := by
  have h1 := Real.rpow_le_rpow hB hBase (by linarith : 0 ≤ r - 1)
  have h2 := Real.rpow_le_rpow hy hNoise (by linarith : 0 ≤ r)
  have h3 := mul_le_mul (mul_le_mul_of_nonneg_left hDim (by norm_num : (0 : ℝ) ≤ 2)) h1
    (Real.rpow_nonneg hB _) (by positivity : 0 ≤ 2 * (16 * D))
  have h4 := mul_le_mul h3 h2 (Real.rpow_nonneg hy _)
    (by positivity : 0 ≤ 2 * (16 * D) * ((2 : ℝ) ^ (2 * r + 16) * D) ^ (r - 1))
  have hDp : D ^ (r - 1) * D = D ^ r := by
    rw [← Real.rpow_add_one hD.ne']
    congr 1
    ring
  have hid : 2 * (16 * D) * ((2 : ℝ) ^ (2 * r + 16) * D) ^ (r - 1) * (8 * X) ^ r =
      (32 * ((2 : ℝ) ^ (2 * r + 16)) ^ (r - 1) * (8 : ℝ) ^ r) * D ^ r * X ^ r := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r + 16)) hD.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hX]
    calc
      _ = (32 * ((2 : ℝ) ^ (2 * r + 16)) ^ (r - 1) * (8 : ℝ) ^ r) *
          (D ^ (r - 1) * D) * X ^ r := by ring
      _ = _ := by rw [hDp]
  rw [hid] at h4
  exact h4.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (spectral_noise_constant hr) (Real.rpow_nonneg hD.le _))
    (Real.rpow_nonneg hX _))

lemma probeSteps_public_upper (p : Params) (hd : 0 < p.d) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (probeSteps p : ℝ) ≤ (2 : ℝ) ^ (13 * conjugate p ^ 2) *
      (Real.log (2 + (p.d : ℝ)) * ((p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)) +
        Real.log (2 + (p.d : ℝ)) ^ conjugate p * (p.σh / Real.sqrt (p.ρ * p.ε)) ^ conjugate p) := by
  let D := Real.log (2 + (p.d : ℝ))
  let V := (p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)
  let X := p.σh / Real.sqrt (p.ρ * p.ε)
  have hr := conjugate_ge_two p hp hp2
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (dimension_log_ge_one p hd)
  have hγ := curvature_pos p hρ hε
  have hc := probeConstant_pos p
  have hD0 := dimensionScale_pos p hd
  have hΓ : 0 < Real.sqrt (p.ρ * p.ε) := Real.sqrt_pos.mpr (mul_pos hρ hε)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hy : p.σh / curvature p ≤ 8 * X := by
    dsimp [X]
    rw [← curvature_accuracy p hρ hε]
    have heq : 8 * (p.σh / (5 * curvature p)) = (8 / 5) * (p.σh / curvature p) := by ring
    rw [heq]
    have hn : 0 ≤ p.σh / curvature p := by positivity
    linarith
  have hnoise := spectral_noise_scale_bound hr
    (by positivity : 0 ≤ 256 * dimensionScale p / probeConstant p)
    (by positivity : 0 ≤ p.σh / curvature p) hD hX
    (dimensionScale_public_upper p hd) (spectral_noise_base_upper p hd) hy
  have hdet := deterministic_probe_cost_upper p hd hL hρ hε
  have hcst : (321 : ℝ) ≤ (2 : ℝ) ^ (13 * conjugate p ^ 2) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith [sq_nonneg (conjugate p - 2)] : 9 ≤ 13 * conjugate p ^ 2)
    norm_num at hh
    linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcoef := mul_le_mul_of_nonneg_right hcst (mul_nonneg hD.le hV)
  have hsteps := probeSteps_separated_upper p hd hp hL hρ hσ hε
  change (probeSteps p : ℝ) ≤ (2 : ℝ) ^ (13 * conjugate p ^ 2) * (D * V + D ^ conjugate p * X ^ conjugate p)
  change 1 + 2 * dimensionScale p * ((2 * p.L + curvature p) / curvature p) ≤ 321 * D * V at hdet
  nlinarith

end LongTails.Proofs.HeavyTailedSospSpectralCost
