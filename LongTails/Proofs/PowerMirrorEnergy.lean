import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.PowerMirrorEnergy

lemma relative_error_reply_bound {e g G α : ℝ} (hα : α ≤ 1 / 4)
    (he0 : 0 ≤ e) (he : e ≤ α * G) (hG : G ≤ g + e) (hα0 : 0 ≤ α) :
    e ≤ (4 / 3) * α * g := by
  have h := mul_le_mul_of_nonneg_left hG hα0
  nlinarith

lemma quadratic_cross_bound {a b s : ℝ} (hs : 0 < s) :
    a * b ≤ s * a ^ 2 + b ^ 2 / (4 * s) := by
  have heq : (2 * s * a - b) ^ 2 / (4 * s) =
      s * a ^ 2 + b ^ 2 / (4 * s) - a * b := by field_simp; ring
  have hn : 0 ≤ (2 * s * a - b) ^ 2 / (4 * s) := by positivity
  rw [heq] at hn
  linarith

lemma coupling_error_bound {P Q δ A a L μ α g r : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hA : 0 < A)
    (hweight : a ^ 2 * L ≤ μ * A / 16)
    (hstep : Q ≤ P + δ - A * g ^ 2 / (8 * L) +
      a ^ 2 * g ^ 2 / (2 * μ) + (4 / 3) * a * α * g * r) :
    Q ≤ P + δ + μ * α ^ 2 * r ^ 2 := by
  have hquad : a ^ 2 * g ^ 2 / (2 * μ) ≤ A * g ^ 2 / (32 * L) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * μ)
      (by positivity : 0 < 32 * L)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hweight (sq_nonneg g)]
  have hcross := quadratic_cross_bound (a := g) (b := (4 / 3) * a * α * r)
    (s := A / (32 * L)) (by positivity)
  have hrest : ((4 / 3) * a * α * r) ^ 2 / (4 * (A / (32 * L))) ≤
      μ * α ^ 2 * r ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (A / (32 * L)))).mpr
    have hw := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (sq_nonneg α) (sq_nonneg r))
    have hn := mul_nonneg (mul_nonneg (le_of_lt hμ) (le_of_lt hA))
      (mul_nonneg (sq_nonneg α) (sq_nonneg r))
    field_simp
    nlinarith
  have hn : 0 ≤ A * g ^ 2 / (32 * L) := by positivity
  have heq : A * g ^ 2 / (8 * L) = 4 * (A * g ^ 2 / (32 * L)) := by ring
  rw [heq] at hstep
  have hcross' : (4 / 3) * a * α * g * r ≤
      A * g ^ 2 / (32 * L) + μ * α ^ 2 * r ^ 2 := by
    calc
      _ = g * ((4 / 3) * a * α * r) := by ring
      _ ≤ A / (32 * L) * g ^ 2 + μ * α ^ 2 * r ^ 2 := by linarith
      _ = _ := by ring
  nlinarith

lemma power_quadratic_bound {r p : ℝ} (hr : 0 ≤ r) (hp : 2 ≤ p) :
    r ^ (2 : ℝ) ≤ r ^ p + 1 := by
  by_cases h : r ≤ 1
  · have hsmall := Real.rpow_le_one hr h (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.rpow_nonneg hr p
    linarith
  · have hlarge := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp
    linarith

lemma scaled_power_quadratic_bound {r t p c μ : ℝ}
    (hr : 0 ≤ r) (ht : 0 < t) (hp : 2 ≤ p) (hc : 0 ≤ c) (hμ : 0 ≤ μ)
    (hscale : μ ≤ c * t ^ (p - 2)) :
    μ * r ^ 2 / 2 ≤ c * r ^ p + μ * t ^ 2 := by
  by_cases hrt : r ≤ t
  · have hsq : r ^ 2 ≤ t ^ 2 := sq_le_sq₀ hr ht.le |>.mpr hrt
    have hmul := mul_le_mul_of_nonneg_left hsq hμ
    have hn := mul_nonneg hc (Real.rpow_nonneg hr p)
    nlinarith [mul_nonneg hμ (sq_nonneg r)]
  · have hrt' : t ≤ r := le_of_not_ge hrt
    have hrpos : 0 < r := lt_of_lt_of_le ht hrt'
    have hpow := Real.rpow_le_rpow ht.le hrt' (sub_nonneg.mpr hp)
    have hcoeff : μ ≤ c * r ^ (p - 2) :=
      hscale.trans (mul_le_mul_of_nonneg_left hpow hc)
    have heq : r ^ p = r ^ (p - 2) * r ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hrpos]
      congr 1
      ring
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg r)
    nlinarith [mul_nonneg hμ (sq_nonneg r), mul_nonneg hμ (sq_nonneg t)]

lemma radius_drift_absorption {μ δ D W d r R α : ℝ}
    (hμ : 0 ≤ μ) (hW : 0 ≤ W) (hα : α ^ 2 ≤ 1 / 16)
    (hD : 3 * δ + 3 * μ * α ^ 2 ≤ D)
    (hr : r ^ 2 ≤ 3 * d ^ 2 + 6 * W + 3 * R ^ 2) :
    3 * δ * W - D * W - μ * d ^ 2 / 8 +
      (μ / 2) * α ^ 2 * r ^ 2 ≤ (3 / 2) * μ * α ^ 2 * R ^ 2 := by
  have hnoise := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (μ / 2) * α ^ 2 by positivity)
  have hdrift := mul_le_mul_of_nonneg_right hD hW
  have hsmall := mul_le_mul_of_nonneg_left hα
    (mul_nonneg hμ (sq_nonneg d))
  have hn := mul_nonneg hμ (sq_nonneg d)
  nlinarith

lemma power_increment_lower {n s : ℝ} (hn : 0 < n) (hs : 1 ≤ s) :
    n ^ (s - 1) ≤ (n + 1) ^ s - n ^ s := by
  have hp := Real.rpow_le_rpow hn.le (show n ≤ n + 1 by linarith)
    (sub_nonneg.mpr hs)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ n + 1 by positivity)
  have he (x : ℝ) (hx : 0 < x) : x * x ^ (s - 1) = x ^ s := by
    conv_lhs => lhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [he (n + 1) (by positivity)] at hm
  have hen := he n hn
  nlinarith

lemma scale_relative_quadratic {r S t p c β μ b : ℝ}
    (hr : 0 ≤ r) (hS : 0 < S) (ht : 0 < t) (hp : 2 ≤ p)
    (hc : 0 ≤ c) (hβ : 0 ≤ β) (hμ : 0 ≤ μ)
    (hscale : μ ≤ β * c * t ^ (p - 2))
    (hcurv : c * r ^ p / S ^ (p - 2) ≤ b) :
    μ * r ^ 2 / 2 ≤ β * b + μ * t ^ 2 * S ^ 2 := by
  have hSp : 0 < S ^ (p - 2) := Real.rpow_pos_of_pos hS _
  have heq : (β * c / S ^ (p - 2)) * (t * S) ^ (p - 2) =
      β * c * t ^ (p - 2) := by
    rw [Real.mul_rpow ht.le hS.le]
    field_simp
  have hh := scaled_power_quadratic_bound hr (mul_pos ht hS) hp
    (show 0 ≤ β * c / S ^ (p - 2) by positivity) hμ
    (show μ ≤ (β * c / S ^ (p - 2)) * (t * S) ^ (p - 2) by rw [heq]; exact hscale)
  have hbc := mul_le_mul_of_nonneg_left hcurv hβ
  have heq' : (β * c / S ^ (p - 2)) * r ^ p =
      β * (c * r ^ p / S ^ (p - 2)) := by ring
  rw [heq'] at hh
  nlinarith only [hh, hbc]

end LongTails.Proofs.PowerMirrorEnergy
