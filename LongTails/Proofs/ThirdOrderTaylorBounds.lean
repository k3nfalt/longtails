import LongTails.Proofs.HiddenConvexGeometry
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace LongTails.Proofs.ThirdOrderTaylorBounds

open Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma power_derivative_bound {f g : ℝ → F} {M : ℝ} (hM : 0 ≤ M) (k : ℕ)
    (hd : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, ‖g t‖ ≤ M * |t| ^ k) (t : ℝ) :
    ‖f t - f 0‖ ≤ M * |t| ^ (k + 1) := by
  have hb : ∀ s ∈ segment ℝ 0 t, ‖g s‖ ≤ M * |t| ^ k := by
    intro s hs
    have hs' : |s| ≤ |t| := by
      simpa only [sub_zero, Real.norm_eq_abs] using
        OracleTemplate.LocalHiddenConvex.norm_sub_le_of_mem_segment' hs
    exact (hg s).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hs' _) hM)
  have hm := (convex_segment (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb (left_mem_segment ℝ 0 t) (right_mem_segment ℝ 0 t)
  simpa only [sub_zero, Real.norm_eq_abs, pow_succ, mul_assoc] using hm

lemma cubic_taylor_bound {f f₁ f₂ f₃ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h₀ : ∀ t, HasDerivAt f (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t, HasDerivAt f₂ (f₃ t) t)
    (h₃ : ∀ t, |f₃ t - f₃ 0| ≤ M * |t|) (t : ℝ) :
    |f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2 - f₃ 0 * t ^ 3 / 6| ≤ M * |t| ^ 4 := by
  let r₂ := fun s : ℝ => f₂ s - f₂ 0 - s * f₃ 0
  have hd₂ : ∀ s, HasDerivAt r₂ (f₃ s - f₃ 0) s := by
    intro s
    convert ((h₂ s).sub_const (f₂ 0)).sub ((hasDerivAt_id s).mul_const (f₃ 0)) using 1 <;>
      (try funext u) <;> simp [r₂]
  have hb₂ : ∀ s, |r₂ s| ≤ M * |s| ^ 2 := by
    intro s
    have hm := power_derivative_bound hM 1 hd₂ (by simpa only [Real.norm_eq_abs, pow_one] using h₃) s
    simpa [r₂, Real.norm_eq_abs] using hm
  let r₁ := fun s : ℝ => f₁ s - f₁ 0 - s * f₂ 0 - s ^ 2 / 2 * f₃ 0
  have hd₁ : ∀ s, HasDerivAt r₁ (r₂ s) s := by
    intro s
    convert (((h₁ s).sub_const (f₁ 0)).sub ((hasDerivAt_id s).mul_const (f₂ 0))).sub
      ((((hasDerivAt_id s).pow 2).div_const 2).mul_const (f₃ 0)) using 1
    all_goals
      try funext u
      dsimp [r₁, r₂]
    all_goals ring
  have hb₁ : ∀ s, |r₁ s| ≤ M * |s| ^ 3 := by
    intro s
    have hm := power_derivative_bound hM 2 hd₁ (by simpa only [Real.norm_eq_abs] using hb₂) s
    simpa [r₁, Real.norm_eq_abs] using hm
  let r₀ := fun s : ℝ => f s - f 0 - s * f₁ 0 - s ^ 2 / 2 * f₂ 0 - s ^ 3 / 6 * f₃ 0
  have hd₀ : ∀ s, HasDerivAt r₀ (r₁ s) s := by
    intro s
    convert ((((h₀ s).sub_const (f 0)).sub ((hasDerivAt_id s).mul_const (f₁ 0))).sub
      ((((hasDerivAt_id s).pow 2).div_const 2).mul_const (f₂ 0))).sub
      ((((hasDerivAt_id s).pow 3).div_const 6).mul_const (f₃ 0)) using 1
    all_goals
      try funext u
      dsimp [r₀, r₁]
    all_goals ring
  have hm := power_derivative_bound hM 3 hd₀ (by simpa only [Real.norm_eq_abs] using hb₁) t
  have he : r₀ t - r₀ 0 = f t - f 0 - f₁ 0 * t - f₂ 0 * t ^ 2 / 2 - f₃ 0 * t ^ 3 / 6 := by
    dsimp [r₀]
    ring
  simpa only [he, Real.norm_eq_abs] using hm

end LongTails.Proofs.ThirdOrderTaylorBounds
