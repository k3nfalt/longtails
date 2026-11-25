import LongTails.Algorithms.RhoSmoothThreePhase
import LongTails.Proofs.RhoSmoothLocal

namespace LongTails.Proofs.RhoSmoothParams

open LongTails.Setups.RhoSmoothRadiusConvex LongTails.Algorithms.RhoSmoothThreePhase
open LongTails.Proofs.RhoSmoothLocal

variable (p : Params) (hp : spec.valid p)
include hp

lemma L0_pos : 0 < p.L0 := hp.1
lemma L1_pos : 0 < p.L1 := hp.2.1
lemma ρ_pos : 0 < p.ρ := by linarith [hp.2.2.1]
lemma ρ_le : p.ρ ≤ 2 := hp.2.2.2.1
lemma R_pos : 0 < p.R := hp.2.2.2.2.1
lemma ε_pos : 0 < p.ε := hp.2.2.2.2.2

lemma threshold_pos : 0 < threshold p := by
  unfold threshold
  have := L0_pos p hp
  have := L1_pos p hp
  positivity

lemma threshold_rpow : threshold p ^ p.ρ = p.L0 / p.L1 := by
  unfold threshold
  have h0 : 0 ≤ p.L0 / p.L1 := by have := L0_pos p hp; have := L1_pos p hp; positivity
  rw [← Real.rpow_mul h0, one_div, inv_mul_cancel₀ (ρ_pos p hp).ne', Real.rpow_one]

omit hp in
lemma curvature_eq (s : ℝ) : curvature p s = curv p.L0 p.L1 p.ρ s := rfl

lemma curvature_scaled {c : ℝ} (hc : 0 ≤ c) :
    curvature p (c * threshold p) = p.L0 * (1 + c ^ p.ρ) := by
  unfold curvature
  rw [Real.mul_rpow hc (threshold_pos p hp).le, threshold_rpow p hp]
  have := L1_pos p hp
  field_simp

lemma curvature_threshold : curvature p (threshold p) = 2 * p.L0 := by
  have h := curvature_scaled p hp (c := 1) zero_le_one
  rw [one_mul, Real.one_rpow] at h
  rw [h]; ring

lemma curvature_le_of_le {s : ℝ} (hs : 0 ≤ s) (hsG : s ≤ threshold p) :
    curvature p s ≤ 2 * p.L0 := by
  rw [← curvature_threshold p hp]
  exact curv_mono (L1_pos p hp).le (ρ_pos p hp).le hs hsG

lemma curvature_double : curvature p (2 * threshold p) ≤ 5 * p.L0 := by
  rw [curvature_scaled p hp (by norm_num : (0 : ℝ) ≤ 2)]
  have h1 : (2 : ℝ) ^ p.ρ ≤ 2 ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (ρ_le p hp)
  have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  have := L0_pos p hp
  nlinarith

lemma curvature_pos {s : ℝ} (hs : 0 ≤ s) : 0 < curvature p s :=
  curv_pos (L0_pos p hp) (L1_pos p hp).le hs

lemma depth_pos : 0 < depth p := by
  unfold depth
  have := threshold_pos p hp
  have := curvature_pos p hp (show (0 : ℝ) ≤ 2 * threshold p by linarith)
  positivity

lemma depth_ge : threshold p / (20 * p.L0) ≤ depth p := by
  unfold depth
  have hG := threshold_pos p hp
  have hc := curvature_pos p hp (show (0 : ℝ) ≤ 2 * threshold p by linarith)
  have hd := curvature_double p hp
  have hL := L0_pos p hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma sq_curv_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    s ^ 2 * curvature p (2 * t) ≤ t ^ 2 * curvature p (2 * s) := by
  unfold curvature
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hρ := ρ_pos p hp
  have hρ2 := ρ_le p hp
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have h1 : s ^ 2 * p.L0 ≤ t ^ 2 * p.L0 := by
    have : s ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  have h2 : s ^ 2 * (2 * t) ^ p.ρ ≤ t ^ 2 * (2 * s) ^ p.ρ := by
    rw [Real.mul_rpow (by norm_num) ht.le, Real.mul_rpow (by norm_num) hs.le]
    have h2ρ : 0 < (2 : ℝ) ^ p.ρ := by positivity
    have hsq : s ^ 2 = s ^ p.ρ * s ^ (2 - p.ρ) := by
      rw [← Real.rpow_add hs, add_sub_cancel, Real.rpow_two]
    have htq : t ^ 2 = t ^ p.ρ * t ^ (2 - p.ρ) := by
      rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_two]
    have hmono : s ^ (2 - p.ρ) ≤ t ^ (2 - p.ρ) :=
      Real.rpow_le_rpow hs.le hst (by linarith)
    have hsρ : 0 ≤ s ^ p.ρ := Real.rpow_nonneg hs.le _
    have htρ : 0 ≤ t ^ p.ρ := Real.rpow_nonneg ht.le _
    rw [hsq, htq]
    have : s ^ p.ρ * s ^ (2 - p.ρ) * t ^ p.ρ ≤ t ^ p.ρ * t ^ (2 - p.ρ) * s ^ p.ρ := by
      have := mul_le_mul_of_nonneg_left hmono (mul_nonneg hsρ htρ)
      nlinarith
    nlinarith
  nlinarith

lemma ratio_nonneg : 0 ≤ ratio p := by
  unfold ratio
  have := L0_pos p hp
  have := R_pos p hp
  have := threshold_pos p hp
  positivity

lemma ratio_sq : ratio p ^ 2 = p.L0 ^ 2 * p.R ^ 2 / threshold p ^ 2 := by
  unfold ratio
  have := threshold_pos p hp
  field_simp

lemma stepSize_pos : 0 < stepSize p := by
  unfold stepSize
  have := L0_pos p hp
  positivity

lemma initialWeight_pos : 0 < initialWeight p := by
  unfold initialWeight
  have := L0_pos p hp
  have := R_pos p hp
  have := threshold_pos p hp
  apply lt_min <;> positivity

lemma initialWeight_le_gap : initialWeight p * p.R ^ 2 ≤ threshold p ^ 2 / (8192 * p.L0) := by
  have hR := R_pos p hp
  have h := min_le_left (threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2) (8 * p.L0)
  have := mul_le_mul_of_nonneg_right h (sq_nonneg p.R)
  unfold initialWeight
  have e : threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2 * p.R ^ 2 =
      threshold p ^ 2 / (8192 * p.L0) := by field_simp
  linarith

omit hp in
lemma initialWeight_le : initialWeight p ≤ 8 * p.L0 := min_le_right _ _

lemma momentum_le_one {Γ : ℝ} (hΓ0 : Γ ≤ initialWeight p) : momentum p Γ ≤ 1 := by
  unfold momentum
  rw [Real.sqrt_le_one]
  have h := initialWeight_le p
  unfold stepSize
  have hL := L0_pos p hp
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  linarith

end LongTails.Proofs.RhoSmoothParams
