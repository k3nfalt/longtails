import LongTails.Proofs.HeavyTailedSospCost
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.HeavyTailedSospDetectorCost

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned
open HeavyTailedSospTuning HeavyTailedSospCost

lemma missRisk_explicit (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    missRisk p = p.ρ * p.ε / (250000 * (p.L + curvature p) ^ 2) := by
  have hγ := curvature_pos p hρ hε
  have hs : 0 < p.L + curvature p := by positivity
  have hγ2 := curvature_sq p hρ.le hε.le
  unfold missRisk stepSize ncLength accuracy
  unfold accuracy at hγ2
  field_simp
  nlinarith [hγ2]

lemma public_curvature_ratio (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    1 ≤ (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε) := by
  have hsq := Real.sq_sqrt (mul_nonneg hρ.le hε.le)
  have hn := Real.sqrt_nonneg (p.ρ * p.ε)
  apply (le_div_iff₀ (mul_pos hρ hε)).mpr
  nlinarith

lemma missRisk_inverse_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    1 / missRisk p ≤ 250000 * ((p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  have hγ := curvature_pos p hρ hε
  have hid := curvature_accuracy p hρ hε
  rw [missRisk_explicit p hL hρ hε]
  have heq : 1 / (p.ρ * p.ε / (250000 * (p.L + curvature p) ^ 2)) =
      250000 * (p.L + curvature p) ^ 2 / (p.ρ * p.ε) := by field_simp
  rw [heq, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hρ.le hε.le)
  nlinarith

lemma log_large_multiple_bound {x : ℝ} (hx : 1 ≤ x) :
    Real.log (500000 * x) ≤ 16 * Real.log (2 + x) := by
  have hx0 : 0 < x := by linarith
  have hp : (3 : ℝ) ^ 15 ≤ (2 + x) ^ 15 := pow_le_pow_left₀ (by norm_num) (by linarith) 15
  have hfactor : (500000 : ℝ) ≤ (2 + x) ^ 15 := by norm_num at hp; linarith
  have hm := mul_le_mul hfactor (by linarith : x ≤ 2 + x) hx0.le (by positivity : 0 ≤ (2 + x) ^ 15)
  have hprod : 500000 * x ≤ (2 + x) ^ 16 := by nlinarith [hm]
  have hl := Real.log_le_log (by positivity : 0 < 500000 * x) hprod
  rw [Real.log_pow] at hl
  norm_num at hl
  exact hl

lemma missRisk_log_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    Real.log (2 / missRisk p) ≤
      16 * Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  have hδ := missRisk_pos p hL hρ hε
  have hi := missRisk_inverse_bound p hL hρ hε
  have hb : 2 / missRisk p ≤ 500000 * ((p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
    have hh := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)
    simp only [mul_one_div] at hh
    nlinarith
  exact (Real.log_le_log (by positivity : 0 < 2 / missRisk p) hb).trans
    (log_large_multiple_bound (public_curvature_ratio p hL hρ hε))

lemma public_log_ge_one (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    1 ≤ Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  have hx := public_curvature_ratio p hL hρ hε
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith :
    3 ≤ 2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
  have h3 := Real.log_three_gt_d9
  linarith

lemma probe_reciprocal_power (p : Params) :
    4 / probeConstant p = (2 : ℝ) ^ (2 * conjugate p + 6) := by
  have he : (4 : ℝ) ^ conjugate p = (2 : ℝ) ^ (2 * conjugate p) := by
    have hh := Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 2 (conjugate p)
    norm_num at hh
    exact hh.symm
  unfold probeConstant
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [← he]
  field_simp
  norm_num

lemma repeatCount_public_upper (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (repeatCount p : ℝ) ≤ (2 : ℝ) ^ (2 * conjugate p + 11) *
      Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
  have hJ : 1 ≤ J := public_log_ge_one p hL hρ hε
  have hr := conjugate_ge_two p hp hp2
  have hδ := missRisk_pos p hL hρ hε
  have hδu := missRisk_le p hL hρ hε
  have hl : 0 ≤ Real.log (2 / missRisk p) :=
    Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  have hc := Nat.ceil_lt_add_one (mul_nonneg
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (probeConstant_pos p).le) hl)
  change (repeatCount p : ℝ) < 4 / probeConstant p * Real.log (2 / missRisk p) + 1 at hc
  rw [probe_reciprocal_power] at hc
  have hb := mul_le_mul_of_nonneg_left (missRisk_log_bound p hL hρ hε)
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * conjugate p + 6))
  have hpow : 1 ≤ (2 : ℝ) ^ (2 * conjugate p + 6) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hmul : 1 ≤ (2 : ℝ) ^ (2 * conjugate p + 6) * J := by nlinarith
  have hid : (2 : ℝ) ^ (2 * conjugate p + 11) = 32 * (2 : ℝ) ^ (2 * conjugate p + 6) := by
    rw [show 2 * conjugate p + 11 = (2 * conjugate p + 6) + 5 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  rw [hid]
  change (repeatCount p : ℝ) ≤ 32 * (2 : ℝ) ^ (2 * conjugate p + 6) * J
  change (2 : ℝ) ^ (2 * conjugate p + 6) * Real.log (2 / missRisk p) ≤
    (2 : ℝ) ^ (2 * conjugate p + 6) * (16 * J) at hb
  nlinarith

lemma validation_log_bound (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    Real.log (2 * repeatCount p / missRisk p) ≤ (2 * conjugate p + 28) *
      Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
  have hJ : 1 ≤ J := public_log_ge_one p hL hρ hε
  have hJ0 : 0 < J := by linarith
  have hr := conjugate_ge_two p hp hp2
  have hR : (0 : ℝ) < repeatCount p := by exact_mod_cast repeatCount_pos p hL hρ hε
  have hδ := missRisk_pos p hL hρ hε
  have hlog := Real.log_le_log hR (repeatCount_public_upper p hp hp2 hL hρ hε)
  change Real.log (repeatCount p : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 * conjugate p + 11) * J) at hlog
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ (2 * conjugate p + 11) ≠ 0) hJ0.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogJ := Real.log_le_self hJ0.le
  have hfactor := mul_le_mul_of_nonneg_right hlog2 (by linarith : 0 ≤ 2 * conjugate p + 11)
  have hscale := mul_le_mul_of_nonneg_left hJ (by linarith : 0 ≤ 2 * conjugate p + 11)
  have hRlog : Real.log (repeatCount p : ℝ) ≤ (2 * conjugate p + 12) * J := by nlinarith
  have hδlog := missRisk_log_bound p hL hρ hε
  change Real.log (2 / missRisk p) ≤ 16 * J at hδlog
  have hid : Real.log (2 * repeatCount p / missRisk p) =
      Real.log (repeatCount p : ℝ) + Real.log (2 / missRisk p) := by
    rw [← Real.log_mul hR.ne' (by positivity : 2 / missRisk p ≠ 0)]
    congr 1
    ring
  rw [hid]
  change _ ≤ (2 * conjugate p + 28) * J
  linarith

lemma validationGroups_public_upper (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (validationGroups p : ℝ) ≤ 256 * conjugate p *
      Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
  have hJ : 1 ≤ J := public_log_ge_one p hL hρ hε
  have hr := conjugate_ge_two p hp hp2
  have hR : (1 : ℝ) ≤ repeatCount p := by exact_mod_cast repeatCount_pos p hL hρ hε
  have hδ := missRisk_pos p hL hρ hε
  have hδu := missRisk_le p hL hρ hε
  have hlog : 0 ≤ Real.log (2 * repeatCount p / missRisk p) :=
    Real.log_nonneg ((one_le_div hδ).mpr (by linarith))
  have hc := Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlog)
  have hb := validation_log_bound p hp hp2 hL hρ hε
  change Real.log (2 * repeatCount p / missRisk p) ≤ (2 * conjugate p + 28) * J at hb
  have hm : (validationGroups p : ℝ) ≤ (16 * conjugate p + 227) * J := by
    unfold validationGroups
    push_cast
    nlinarith
  change (validationGroups p : ℝ) ≤ 256 * conjugate p * J
  have hh := mul_nonneg (by linarith : 0 ≤ 240 * conjugate p - 227) (by linarith : 0 ≤ J)
  nlinarith

lemma validation_root_bound (p : Params) (hp : 1 < p.p) (hρ : 0 < p.ρ)
    (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (6 * p.σh ^ p.p / (curvature p / 8) ^ p.p) ^ (1 / (p.p - 1)) ≤
      (256 * (p.σh / Real.sqrt (p.ρ * p.ε))) ^ conjugate p := by
  have hγ := curvature_pos p hρ hε
  have hΓ : 0 < Real.sqrt (p.ρ * p.ε) := Real.sqrt_pos.mpr (mul_pos hρ hε)
  have hscale := curvature_accuracy p hρ hε
  have hq : 0 ≤ p.σh / (curvature p / 8) := by positivity
  have h6 := Real.self_le_rpow_of_one_le (by norm_num : (1 : ℝ) ≤ 6) hp.le
  have hb : 6 * p.σh ^ p.p / (curvature p / 8) ^ p.p ≤
      (6 * (p.σh / (curvature p / 8))) ^ p.p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hq,
      Real.div_rpow hσ (by positivity : 0 ≤ curvature p / 8)]
    have hh := mul_le_mul_of_nonneg_right h6 (by positivity : 0 ≤ p.σh ^ p.p / (curvature p / 8) ^ p.p)
    simpa only [mul_div_assoc] using hh
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 6 * p.σh ^ p.p / (curvature p / 8) ^ p.p)
    hb (by positivity : 0 ≤ 1 / (p.p - 1))
  rw [← Real.rpow_mul (by positivity : 0 ≤ 6 * (p.σh / (curvature p / 8))), mul_one_div] at hh
  change _ ≤ (6 * (p.σh / (curvature p / 8))) ^ conjugate p at hh
  have heq : 6 * (p.σh / (curvature p / 8)) = 240 * (p.σh / Real.sqrt (p.ρ * p.ε)) := by
    rw [← hscale]
    field_simp
    ring
  rw [heq] at hh
  refine hh.trans (Real.rpow_le_rpow (by positivity) ?_ (conjugate_holder p hp).symm.nonneg)
  have hn : 0 ≤ p.σh / Real.sqrt (p.ρ * p.ε) := by positivity
  linarith

lemma validationBatch_public_upper (p : Params) (hp : 1 < p.p) (hρ : 0 < p.ρ)
    (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (validationBatch p : ℝ) ≤ (2 : ℝ) ^ (8 * conjugate p) *
      (1 + (p.σh / Real.sqrt (p.ρ * p.ε)) ^ conjugate p) := by
  have hγ := curvature_pos p hρ hε
  have hr := (conjugate_holder p hp).symm.nonneg
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg
    (by positivity : 0 ≤ 6 * p.σh ^ p.p / (curvature p / 8) ^ p.p) (1 / (p.p - 1)))
  have hb : (validationBatch p : ℝ) ≤
      1 + (6 * p.σh ^ p.p / (curvature p / 8) ^ p.p) ^ (1 / (p.p - 1)) := by
    unfold validationBatch
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  have hh := validation_root_bound p hp hρ hσ hε
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 256) (by positivity)] at hh
  have heq : (256 : ℝ) ^ conjugate p = (2 : ℝ) ^ (8 * conjugate p) := by
    have he := Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 8 (conjugate p)
    norm_num at he
    exact he.symm
  rw [heq] at hh
  have hpow : 1 ≤ (2 : ℝ) ^ (8 * conjugate p) := Real.one_le_rpow (by norm_num) (by positivity)
  nlinarith

lemma group_constant_envelope {r : ℝ} (hr : 2 ≤ r) :
    256 * r ≤ (2 : ℝ) ^ (3 * r ^ 2) := by
  have hr0 : 0 < r := by linarith
  have hh := Real.exp_le_exp.mpr (log_le_self_mul_log_two hr)
  rw [Real.exp_log hr0, mul_comm r, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 256)
  have hid : (256 : ℝ) * (2 : ℝ) ^ r = (2 : ℝ) ^ (8 + r) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hid] at hm
  exact hm.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (r - 2)]))

lemma validationGroups_envelope (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (validationGroups p : ℝ) ≤ (2 : ℝ) ^ (3 * conjugate p ^ 2) *
      Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  have hJ := public_log_ge_one p hL hρ hε
  exact (validationGroups_public_upper p hp hp2 hL hρ hε).trans
    (mul_le_mul_of_nonneg_right (group_constant_envelope (conjugate_ge_two p hp hp2)) (by linarith))

lemma repeatCount_envelope (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    (repeatCount p : ℝ) ≤ (2 : ℝ) ^ (4 * conjugate p ^ 2) *
      Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) := by
  have hr := conjugate_ge_two p hp hp2
  have hJ := public_log_ge_one p hL hρ hε
  refine (repeatCount_public_upper p hp hp2 hL hρ hε).trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (conjugate p - 2)])

lemma validation_calls_envelope (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σh) (hε : 0 < p.ε) :
    ((max 1 (repeatCount p) * max 1 (validationBatch p) * max 1 (validationGroups p) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (11 * conjugate p ^ 2) *
        Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) ^ 2 *
          (1 + (p.σh / Real.sqrt (p.ρ * p.ε)) ^ conjugate p) := by
  let J := Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))
  let X := 1 + (p.σh / Real.sqrt (p.ρ * p.ε)) ^ conjugate p
  have hJ : 0 ≤ J := le_trans (by norm_num) (public_log_ge_one p hL hρ hε)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hr := conjugate_ge_two p hp hp2
  have hR := repeatCount_envelope p hp hp2 hL hρ hε
  have hm := validationGroups_envelope p hp hp2 hL hρ hε
  have hn := validationBatch_public_upper p hp hρ hσ hε
  have hex : (2 : ℝ) ^ (8 * conjugate p) ≤ (2 : ℝ) ^ (4 * conjugate p ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [sq_nonneg (conjugate p - 2)])
  have hn' : (validationBatch p : ℝ) ≤ (2 : ℝ) ^ (4 * conjugate p ^ 2) * X :=
    hn.trans (mul_le_mul_of_nonneg_right hex hX)
  have h1 := mul_le_mul hR hn' (Nat.cast_nonneg (validationBatch p))
    (by positivity : 0 ≤ (2 : ℝ) ^ (4 * conjugate p ^ 2) * J)
  have h2 := mul_le_mul h1 hm (Nat.cast_nonneg (validationGroups p))
    (by positivity : 0 ≤ ((2 : ℝ) ^ (4 * conjugate p ^ 2) * J) * ((2 : ℝ) ^ (4 * conjugate p ^ 2) * X))
  have hid : ((2 : ℝ) ^ (4 * conjugate p ^ 2) * J * ((2 : ℝ) ^ (4 * conjugate p ^ 2) * X)) *
      ((2 : ℝ) ^ (3 * conjugate p ^ 2) * J) = (2 : ℝ) ^ (11 * conjugate p ^ 2) * J ^ 2 * X := by
    calc
      _ = ((2 : ℝ) ^ (4 * conjugate p ^ 2) * (2 : ℝ) ^ (4 * conjugate p ^ 2) *
          (2 : ℝ) ^ (3 * conjugate p ^ 2)) * J ^ 2 * X := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 3
        ring
  change (repeatCount p : ℝ) * validationBatch p * validationGroups p ≤
    ((2 : ℝ) ^ (4 * conjugate p ^ 2) * J * ((2 : ℝ) ^ (4 * conjugate p ^ 2) * X)) *
      ((2 : ℝ) ^ (3 * conjugate p ^ 2) * J) at h2
  change _ ≤ (2 : ℝ) ^ (11 * conjugate p ^ 2) * J ^ 2 * X
  have hRp : 1 ≤ repeatCount p := repeatCount_pos p hL hρ hε
  have hnp : 1 ≤ validationBatch p := (validationBatch_bound p hp hρ hσ hε).1
  have hmp : 1 ≤ validationGroups p := by unfold validationGroups; omega
  rw [max_eq_right hRp, max_eq_right hnp, max_eq_right hmp, Nat.cast_mul, Nat.cast_mul]
  simpa only [hid] using h2

end LongTails.Proofs.HeavyTailedSospDetectorCost
