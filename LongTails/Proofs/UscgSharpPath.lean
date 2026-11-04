import LongTails.Proofs.UscgSharpGeometry
import LongTails.Proofs.UscgSharpTracking
import LongTails.Proofs.UscgSharpDescent

namespace LongTails.Proofs.UscgSharpPath

open LongTails.Setups.UscgConstant
open OracleTemplate.NormBallLMO
open UscgSharpTracking UscgSharpGeometry
open scoped RealInnerProductSpace

lemma pathwise_bound {d : ℕ} {N : Seminorm ℝ (Space d)} {R L Δ α η ζ G S fmin : ℝ}
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hζ : 0 < ζ) (hG : 0 ≤ G)
    (hζnorm : ∀ u, dualNorm N u ≤ ζ * ‖u‖)
    {f : Space d → ℝ} (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (hlower : ∀ x, fmin ≤ f x)
    (hself : ∀ x, dualNorm N (gradient f x) ^ 2 ≤ 2 * L * (f x - fmin))
    (x v samples : ℕ → Space d) (T : ℕ)
    (hgap : f (x 0) - fmin ≤ Δ) (hGsq : 4 * L * Δ ≤ G ^ 2)
    (hfeas : ∀ t, N (v t) ≤ 1) (hpath : ∀ t, x (t + 1) = x t + η • v t)
    (hmin : ∀ t w, N w ≤ 1 →
      ⟪mean α samples (t + 1), v t⟫ ≤ ⟪mean α samples (t + 1), w⟫)
    (hcap : ∑ t ∈ Finset.range T, min (G / ζ)
      ‖mean α (fun k => samples k - gradient f (x k)) (t + 1)‖ ≤ S)
    (hmargin : η * (2 * ζ * S + 2 * (G + T * (L * η)) / α) + T * (L * η ^ 2 / 2) ≤ Δ) :
    (∀ n ≤ T, f (x n) ≤ f (x 0) + Δ) ∧
      η * ∑ t ∈ Finset.range T, dualNorm N (gradient f (x t)) ≤ 2 * Δ := by
  let u := fun t => gradient f (x t)
  let z := fun t => mean α (fun k => samples k - u k) (t + 1)
  let b := fun t => dualNorm N (bias α u t)
  let a := fun t => dualNorm N (u t) + ⟪u t, v t⟫
  let w := fun t => 2 * ζ * min (G / ζ) ‖z t‖ + 2 * b t
  let B := 2 * ζ * S + 2 * (G + T * (L * η)) / α
  have hmove : ∀ t, dualNorm N (u t - u (t + 1)) ≤ L * η := by
    intro t
    have hh := hlip (x t) (x (t + 1))
    have he : x t - x (t + 1) = -(η • v t) := by rw [hpath]; abel
    rw [he, map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hη] at hh
    have hv := mul_le_mul_of_nonneg_left (hfeas t) (mul_nonneg hL hη)
    dsimp [u]
    nlinarith
  have hgin : dualNorm N (u 0) ≤ G := by
    have hh := hself (x 0)
    have hg := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * L by positivity)
    dsimp [u]
    nlinarith
  have hb := bias_sum hR hα hα1 (mul_nonneg hL hη) u hmove T
  have hbs : ∑ t ∈ Finset.range T, b t ≤ (G + T * (L * η)) / α :=
    hb.trans ((div_le_div_iff_of_pos_right hα).mpr (by linarith))
  have hws : ∑ t ∈ Finset.range T, w t ≤ B := by
    dsimp [w, B]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2 * ζ by positivity)
    dsimp [z, u] at *
    have hb2 := mul_le_mul_of_nonneg_left hbs (by norm_num : (0 : ℝ) ≤ 2)
    convert add_le_add hh hb2 using 1
    ring
  have hstep : ∀ t < T, f (x (t + 1)) ≤ f (x t) - η * dualNorm N (u t) +
      η * a t + L * η ^ 2 / 2 := by
    intro t _
    have hh := descent hR hdef hgrad hlip (x t) (x (t + 1))
    rw [hpath t, add_sub_cancel_left, inner_smul_right, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg hη] at hh
    have hv : (η * N (v t)) ^ 2 ≤ η ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg hη (apply_nonneg N _))
      nlinarith [hfeas t]
    have hq := mul_le_mul_of_nonneg_left hv (show 0 ≤ L / 2 by positivity)
    rw [← hpath t] at hh
    dsimp [a, u]
    nlinarith
  have hac : ∀ t < T, f (x t) ≤ f (x 0) + Δ → a t ≤ w t := by
    intro t _ ht
    have hgt : dualNorm N (u t) ≤ G := by
      have hh := hself (x t)
      have hf : f (x t) - fmin ≤ 2 * Δ := by linarith
      have hz := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2 * L by positivity)
      dsimp [u]
      nlinarith
    have hgc : dualNorm N (u t) ≤ ζ * (G / ζ) := by
      simpa only [mul_div_cancel₀ G hζ.ne'] using hgt
    exact alignment_capped hR (hζnorm (z t)) hgc (hfeas t) (hmin t)
      (tracking_decomposition α samples u t)
  have hboot := UscgSharpDescent.sublevel_and_sum hη
    (show 0 ≤ L * η ^ 2 / 2 by positivity) (fun i _ => dualNorm_nonneg hR (u i))
    (fun i => by
      dsimp [w, b]
      have hb0 := dualNorm_nonneg hR (bias α u i)
      have hmn : 0 ≤ min (G / ζ) ‖z i‖ := le_min (div_nonneg hG hζ.le) (norm_nonneg _)
      positivity)
    hstep hac hws hmargin (hlower (x T)) hgap
  refine ⟨hboot.1, ?_⟩
  have hh := hboot.2
  change η * ∑ t ∈ Finset.range T, dualNorm N (u t) ≤ 2 * Δ
  dsimp [B] at hh
  linarith

end LongTails.Proofs.UscgSharpPath
