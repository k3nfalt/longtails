import LongTails.Algorithms.PowerDualAveraging
import LongTails.Proofs.PowerMirrorEnergy
import LongTails.Proofs.PowerMirrorGeometry
import Mathlib.Tactic

namespace LongTails.Proofs.PowerMirrorTuning

open LongTails.Algorithms.PowerDualAveraging
open LongTails.Setups.PowerGeometryRelativeErrorConvex

lemma totalWeight_succ (n : ℕ) :
    totalWeight (n + 1) = totalWeight n + weight (n + 1) := by
  simp only [totalWeight, weight, Nat.cast_add, Nat.cast_one]
  ring

lemma totalWeight_nonneg (n : ℕ) : 0 ≤ totalWeight n := by
  unfold totalWeight
  positivity

lemma totalWeight_lower (n : ℕ) : (n : ℝ) ^ 3 / 3 ≤ totalWeight n := by
  unfold totalWeight
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

lemma totalWeight_pos {n : ℕ} (hn : 0 < n) : 0 < totalWeight n := by
  exact lt_of_lt_of_le (by positivity) (totalWeight_lower n)

lemma coupling_weight {n : ℕ} {L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    weight n ^ 2 * L ≤ (64 * L * n) * totalWeight n / 16 := by
  have hh := mul_le_mul_of_nonneg_left (totalWeight_lower n)
    (show 0 ≤ 4 * L * (n : ℝ) by positivity)
  unfold weight
  nlinarith [mul_nonneg hL.le (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4)]

lemma geometryConstant_lower (d : Public) : 128 ≤ geometryConstant d := by
  unfold geometryConstant
  nlinarith [le_max_left (1 : ℝ) (32 ^ ((d.p - 2) / 2) / d.c)]

lemma geometryConstant_curvature (d : Public) (hc : 0 < d.c) :
    128 * 32 ^ ((d.p - 2) / 2) ≤ geometryConstant d * d.c := by
  have hh := (div_le_iff₀ hc).mp (le_max_right (1 : ℝ) (32 ^ ((d.p - 2) / 2) / d.c))
  unfold geometryConstant
  nlinarith

lemma regularization_pos (d : Public) (hd : d.Valid) (n : ℕ) :
    0 < regularization d n := by
  have hL := hd.1
  have hB : 0 < geometryConstant d := lt_of_lt_of_le (by norm_num) (geometryConstant_lower d)
  unfold regularization
  positivity

lemma regularization_drift (d : Public) (hd : d.Valid) (n : ℕ) :
    geometryConstant d * d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p) +
      512 * d.L * d.α ^ 2 * ((n : ℝ) + 1) ≤
        regularization d (n + 1) - regularization d n := by
  have hL := hd.1
  have hp : 0 < d.p := by linarith [hd.2.1]
  have he : 1 ≤ 2 - 2 / d.p := by
    have hh := (div_le_iff₀ hp).mpr (show (2 : ℝ) ≤ 1 * d.p by linarith [hd.2.1])
    linarith
  have hh := PowerMirrorEnergy.power_increment_lower
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity) he
  have hexp : 2 - 2 / d.p - 1 = 1 - 2 / d.p := by ring
  rw [hexp] at hh
  have hB := geometryConstant_lower d
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ geometryConstant d * d.L by positivity)
  unfold regularization
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_nonneg hL.le (sq_nonneg d.α)]

lemma regularization_base_lower (d : Public) (hd : d.Valid) (n : ℕ) :
    d.L * geometryConstant d * ((n : ℝ) + 1) ^ (2 - 2 / d.p) ≤ regularization d n := by
  unfold regularization
  have hL := hd.1
  nlinarith [mul_nonneg hL.le
    (show 0 ≤ 256 * d.α ^ 2 * ((n : ℝ) + 1) ^ 2 by positivity)]

lemma radius_scale_identity {p t : ℝ} (hp : 2 < p) (ht : 0 < t) :
    (32 : ℝ) ^ ((p - 2) / 2) * t ^ (2 - 2 / p) *
      ((32 : ℝ) ^ (-(1 : ℝ) / 2) * t ^ (-1 / p)) ^ (p - 2) = t := by
  have hp0 : p ≠ 0 := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg ht.le _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32), ← Real.rpow_mul ht.le]
  calc
    _ = ((32 : ℝ) ^ ((p - 2) / 2) * (32 : ℝ) ^ ((-1 / 2) * (p - 2))) *
        (t ^ (2 - 2 / p) * t ^ ((-1 / p) * (p - 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 32), ← Real.rpow_add ht]
      have h₁ : (p - 2) / 2 + (-1 / 2) * (p - 2) = 0 := by ring
      have h₂ : 2 - 2 / p + (-1 / p) * (p - 2) = 1 := by field_simp; ring
      rw [h₁, h₂, Real.rpow_zero, Real.rpow_one, one_mul]

lemma radius_defect_identity {p t : ℝ} (ht : 0 < t) :
    t * ((32 : ℝ) ^ (-(1 : ℝ) / 2) * t ^ (-1 / p)) ^ 2 =
      t ^ (1 - 2 / p) / 32 := by
  have hc : ((32 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
    norm_num [Real.rpow_neg_one]
  have hn : t * (t ^ (-1 / p)) ^ 2 = t ^ (1 - 2 / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    conv_lhs => lhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  rw [mul_pow, hc]
  calc
    _ = (t * (t ^ (-1 / p)) ^ 2) / 32 := by ring
    _ = _ := by rw [hn]

lemma radius_scale_bound (d : Public) (hd : d.Valid) (n : ℕ) :
    128 * d.L * ((n : ℝ) + 1) ≤ regularization d n * d.c *
      ((32 : ℝ) ^ (-(1 : ℝ) / 2) * ((n : ℝ) + 1) ^ (-1 / d.p)) ^ (d.p - 2) := by
  have hL := hd.1
  have hp := hd.2.1
  have hc := hd.2.2.1
  have hb := geometryConstant_curvature d hc
  have he := radius_scale_identity hp (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ d.L * ((n : ℝ) + 1) ^ (2 - 2 / d.p) *
      ((32 : ℝ) ^ (-(1 : ℝ) / 2) * ((n : ℝ) + 1) ^ (-1 / d.p)) ^ (d.p - 2) by positivity)
  have hr := mul_le_mul_of_nonneg_right (regularization_base_lower d hd n)
    (show 0 ≤ d.c *
      ((32 : ℝ) ^ (-(1 : ℝ) / 2) * ((n : ℝ) + 1) ^ (-1 / d.p)) ^ (d.p - 2) by positivity)
  have he' := congrArg (fun x : ℝ => 128 * d.L * x) he
  nlinarith only [hh, hr, he']

lemma quadratic_surrogate (d : Public) (hd : d.Valid) (n : ℕ) (z w : d.E) :
    (64 * d.L * ((n : ℝ) + 1)) * ‖w - z‖ ^ 2 / 2 +
      (16 * d.L * ((n : ℝ) + 1)) * ‖w - z‖ ^ 2 -
      3 * (16 * d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p)) * d.ψ w ≤
        regularization d n * (d.ψ w - d.ψ z - fderiv ℝ d.ψ z (w - z)) := by
  have hL := hd.1
  have hp := hd.2.1
  have hc := hd.2.2.1
  have huc := hd.2.2.2.2.2.2 z w
  let t := (32 : ℝ) ^ (-(1 : ℝ) / 2) * ((n : ℝ) + 1) ^ (-1 / d.p)
  have ht : 0 < t := by dsimp [t]; positivity
  have hh := PowerMirrorGeometry.norm_square_curvature_surrogate hp.le hc.le
    (regularization_pos d hd n).le (show 0 ≤ 128 * d.L * ((n : ℝ) + 1) by positivity)
    ht (radius_scale_bound d hd n) huc
  have he := radius_defect_identity (p := d.p)
    (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  have hdef : 4 * (128 * d.L * ((n : ℝ) + 1)) * t ^ 2 =
      16 * d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p) := by
    dsimp [t]
    nlinarith only [congrArg (fun x : ℝ => 512 * d.L * x) he]
  rw [hdef] at hh
  have htri := PowerMirrorGeometry.squared_norm_triangle (x0 := d.x0) (w := w) (z := z)
  have hδ : 0 ≤ 16 * d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p) := by positivity
  have hm := mul_le_mul_of_nonneg_left htri hδ
  have hp0 : 0 < d.p := by linarith
  have he' : 1 - 2 / d.p ≤ 1 := by
    have hh : 0 ≤ 2 / d.p := by positivity
    linarith
  have hb := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (n : ℝ) + 1 by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) he'
  rw [Real.rpow_one] at hb
  have hb' := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 16 * d.L * ‖w - z‖ ^ 2 by positivity)
  simp only [Public.ψ] at hh ⊢
  nlinarith only [hh, hm, hb']

lemma shifted_power_bound {t s : ℝ} (ht : 1 ≤ t) (hs : 0 ≤ s) (hs' : s ≤ 2) :
    (t + 1) ^ s ≤ 4 * t ^ s := by
  have ht0 : 0 ≤ t := by linarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ t + 1)
    (show t + 1 ≤ 2 * t by linarith) hs
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0] at hh
  have htwo : (2 : ℝ) ^ s ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs'
    norm_num [Real.rpow_two] at h ⊢
    exact h
  exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg ht0 s))

lemma regularization_upper (d : Public) (hd : d.Valid) {T : ℕ} (hT : 0 < T) {R : ℝ} :
    regularization d T * (R ^ 2 / 2) ≤
      2 * geometryConstant d * d.L * R ^ 2 * (T : ℝ) ^ (2 - 2 / d.p) +
      512 * d.L * d.α ^ 2 * R ^ 2 * (T : ℝ) ^ 2 := by
  have hL := hd.1
  have hp : 0 < d.p := by linarith [hd.2.1]
  have hB := geometryConstant_lower d
  have he : 0 ≤ 2 - 2 / d.p := by
    have hh := (div_le_iff₀ hp).mpr (show (2 : ℝ) ≤ 2 * d.p by linarith [hd.2.1])
    linarith
  have he' : 2 - 2 / d.p ≤ 2 := by
    have hh : 0 ≤ 2 / d.p := by positivity
    linarith
  have hh := shifted_power_bound (show (1 : ℝ) ≤ T by exact_mod_cast hT) he he'
  have hs : ((T : ℝ) + 1) ^ 2 ≤ 4 * (T : ℝ) ^ 2 := by
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ d.L * geometryConstant d * R ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ d.L * d.α ^ 2 * R ^ 2 by positivity)
  unfold regularization
  nlinarith only [h₁, h₂]

lemma drift_absorbs (d : Public) (hd : d.Valid) (n : ℕ) :
    3 * (16 * d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p)) +
      3 * (128 * d.L * ((n : ℝ) + 1)) * d.α ^ 2 ≤
        regularization d (n + 1) - regularization d n := by
  have hL := hd.1
  have hB := geometryConstant_lower d
  have hh := regularization_drift d hd n
  have hm := mul_le_mul_of_nonneg_right hB
    (show 0 ≤ d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p) by positivity)
  have hn : 0 ≤ d.L * d.α ^ 2 * ((n : ℝ) + 1) := by positivity
  have hz : 0 ≤ d.L * ((n : ℝ) + 1) ^ (1 - 2 / d.p) := by positivity
  nlinarith

lemma accuracy_from_numerator {p C B ε gap : ℝ} {T : ℕ}
    (hp : 2 < p) (hC : 0 ≤ C) (hB : 0 ≤ B) (hε : 0 < ε)
    (hT : 0 < T) (hgap : 0 ≤ gap)
    (hbudget : (12 * C / ε) ^ (p / (p + 2)) + 4224 * B / ε ≤ T)
    (hnum : totalWeight T * gap ≤
      2 * C * (T : ℝ) ^ (2 - 2 / p) + 704 * B * (T : ℝ) ^ 2) :
    gap ≤ ε := by
  have hp0 : 0 < p := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hb0 : 0 ≤ 12 * C / ε := by positivity
  have hnoise : 4224 * B / ε ≤ T :=
    le_trans (le_add_of_nonneg_left (Real.rpow_nonneg hb0 _)) hbudget
  have hexact : (12 * C / ε) ^ (p / (p + 2)) ≤ T :=
    le_trans (le_add_of_nonneg_right (by positivity)) hbudget
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hb0 _) hexact
    (show 0 ≤ 1 + 2 / p by positivity)
  rw [← Real.rpow_mul hb0] at hpow
  have hexp : p / (p + 2) * (1 + 2 / p) = 1 := by field_simp
  rw [hexp, Real.rpow_one] at hpow
  have hprod : (T : ℝ) ^ (1 + 2 / p) * (T : ℝ) ^ (2 - 2 / p) = (T : ℝ) ^ 3 := by
    rw [← Real.rpow_add hT0]
    have hh : 1 + 2 / p + (2 - 2 / p) = 3 := by ring
    rw [hh]
    exact Real.rpow_natCast _ 3
  have hlarge := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hpow)
    (Real.rpow_nonneg hT0.le (2 - 2 / p))
  have hlarge' : 12 * C * (T : ℝ) ^ (2 - 2 / p) ≤ ε * (T : ℝ) ^ 3 := by
    calc
      _ ≤ ((T : ℝ) ^ (1 + 2 / p) * ε) * (T : ℝ) ^ (2 - 2 / p) := hlarge
      _ = ε * ((T : ℝ) ^ (1 + 2 / p) * (T : ℝ) ^ (2 - 2 / p)) := by ring
      _ = _ := by rw [hprod]
  have hnoise' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hnoise)
    (sq_nonneg (T : ℝ))
  have hlow := mul_le_mul_of_nonneg_right (totalWeight_lower T) hgap
  have hfin : (T : ℝ) ^ 3 * gap ≤ (T : ℝ) ^ 3 * ε := by
    nlinarith only [hlarge', hnoise', hlow, hnum]
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (T : ℝ) ^ 3)).mp
    (by simpa only [mul_comm] using hfin)

end LongTails.Proofs.PowerMirrorTuning
