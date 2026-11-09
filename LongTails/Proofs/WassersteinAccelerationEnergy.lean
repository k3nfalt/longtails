import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.WassersteinAccelerationEnergy

lemma extrapolated_norm_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y z : E) (t : ℝ) :
    ‖t • x - (t - 1) • y - z‖ ^ 2 =
      t * ‖x - z‖ ^ 2 - (t - 1) * ‖y - z‖ ^ 2 +
        t * (t - 1) * ‖x - y‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
  ring

lemma extrapolation_coefficients (s t β : ℝ) (hβ : t * β = s - 1) :
    t * (1 + β) - (t - 1) = s ∧
      t * β * (1 + β) + t * (t - 1) * β ^ 2 = s * (s - 1) := by
  constructor
  · nlinarith
  · calc
      t * β * (1 + β) + t * (t - 1) * β ^ 2 =
          (t * β) + (t * β) ^ 2 := by ring
      _ = s * (s - 1) := by rw [hβ]; ring

lemma weighted_descent (s t β h gnext gold yz yx nz nx xz pz xp r : ℝ)
    (ht : 1 ≤ t) (hh : 0 ≤ h) (hgold : 0 ≤ gold)
    (hrec : t * (t - 1) ≤ s ^ 2) (hβ : t * β = s - 1)
    (hz : 2 * h * gnext ≤ yz - nz - r)
    (hx : 2 * h * (gnext - gold) ≤ yx - nx - r)
    (hyz : yz ≤ (1 + β) * xz - β * pz + β * (1 + β) * xp)
    (hyx : yx ≤ β ^ 2 * xp) :
    2 * h * t ^ 2 * gnext + t * nz - (t - 1) * xz + t * (t - 1) * nx ≤
      2 * h * s ^ 2 * gold + s * xz - (s - 1) * pz + s * (s - 1) * xp -
        t ^ 2 * r := by
  have ht0 : 0 ≤ t := by linarith
  have htm : 0 ≤ t * (t - 1) := mul_nonneg ht0 (by linarith)
  have hw := add_le_add (mul_le_mul_of_nonneg_left hz ht0)
    (mul_le_mul_of_nonneg_left hx htm)
  have he := add_le_add (mul_le_mul_of_nonneg_left hyz ht0)
    (mul_le_mul_of_nonneg_left hyx htm)
  have hc := extrapolation_coefficients s t β hβ
  have halg : t * ((1 + β) * xz - β * pz + β * (1 + β) * xp) +
      t * (t - 1) * (β ^ 2 * xp) - (t - 1) * xz =
      s * xz - (s - 1) * pz + s * (s - 1) * xp := by
    calc
      _ = (t * (1 + β) - (t - 1)) * xz - (t * β) * pz +
          (t * β * (1 + β) + t * (t - 1) * β ^ 2) * xp := by ring
      _ = _ := by rw [hc.1, hc.2, hβ]
  have hgap : t * (2 * h * gnext) + t * (t - 1) * (2 * h * (gnext - gold)) =
      2 * h * t ^ 2 * gnext - 2 * h * (t * (t - 1)) * gold := by ring
  rw [hgap] at hw
  have hr := mul_le_mul_of_nonneg_right hrec (mul_nonneg (by positivity : 0 ≤ 2 * h) hgold)
  nlinarith

lemma remove_interpolation_error (a b C : ℝ) (hC : 0 ≤ C)
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → a ≤ b + θ * C) : a ≤ b := by
  by_contra hab
  have hg : 0 < a - b := by linarith
  have hd : 0 < 2 * (C + 1) := by positivity
  let θ := min 1 ((a - b) / (2 * (C + 1)))
  have hp : 0 < θ := lt_min (by norm_num) (div_pos hg hd)
  have hu : θ ≤ 1 := min_le_left _ _
  have hv : θ * (2 * (C + 1)) ≤ a - b :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have hh := h θ hp hu
  nlinarith

lemma interpolated_norm_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y z : E) (θ : ℝ) :
    ‖x - ((1 - θ) • y + θ • z)‖ ^ 2 =
      (1 - θ) * ‖x - y‖ ^ 2 + θ * ‖x - z‖ ^ 2 -
        θ * (1 - θ) * ‖y - z‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
  ring

end LongTails.Proofs.WassersteinAccelerationEnergy
