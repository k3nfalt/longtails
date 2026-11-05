import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.QuarticBregmanKernel

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quartic_support (x s : E) :
    ‖s‖ ^ 4 / 12 ≤ ‖x + s‖ ^ 4 / 4 - ‖x‖ ^ 4 / 4 -
      ‖x‖ ^ 2 * ⟪x, s⟫ := by
  have hcs : ⟪x, s⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖s‖ ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg ⟪x, s⟫)
      (mul_nonneg (norm_nonneg x) (norm_nonneg s))).mpr (abs_real_inner_le_norm x s)
    simpa only [sq_abs, mul_pow] using hh
  have hsum : ‖x + s‖ ^ 4 = (‖x‖ ^ 2 + 2 * ⟪x, s⟫ + ‖s‖ ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, norm_add_sq_real]
  rw [hsum]
  nlinarith [sq_nonneg (3 * ⟪x, s⟫ + ‖s‖ ^ 2)]

lemma quartic_gap_lower {f : E → ℝ} {u v c g : E} {γ : ℝ}
    (hγ : 0 ≤ γ) (hsupport : f u + ⟪g, v - u⟫ ≤ f v)
    (hstationary : g + (γ * ‖u - c‖ ^ 2) • (u - c) = 0) :
    γ / 12 * ‖v - u‖ ^ 4 ≤
      (f v + γ / 4 * ‖v - c‖ ^ 4) - (f u + γ / 4 * ‖u - c‖ ^ 4) := by
  have hq := mul_le_mul_of_nonneg_left (quartic_support (u - c) (v - u)) hγ
  rw [show u - c + (v - u) = v - c by abel] at hq
  have hi := congrArg (fun a => ⟪a, v - u⟫) hstationary
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hi
  nlinarith

lemma quartic_reverse (x s : E) :
    ‖x‖ ^ 4 / 4 - ‖x + s‖ ^ 4 / 4 + ‖x + s‖ ^ 2 * ⟪x + s, s⟫ ≤
      4 * (‖x + s‖ ^ 4 / 4 - ‖x‖ ^ 4 / 4 - ‖x‖ ^ 2 * ⟪x, s⟫) := by
  have hcs : ⟪x, s⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖s‖ ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg ⟪x, s⟫)
      (mul_nonneg (norm_nonneg x) (norm_nonneg s))).mpr (abs_real_inner_le_norm x s)
    simpa only [sq_abs, mul_pow] using hh
  have hsum : ‖x + s‖ ^ 4 = (‖x‖ ^ 2 + 2 * ⟪x, s⟫ + ‖s‖ ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, norm_add_sq_real]
  rw [hsum, norm_add_sq_real, inner_add_left, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg (2 * ⟪x, s⟫ + ‖s‖ ^ 2 / 2), sq_nonneg ⟪x, s⟫]

end LongTails.Proofs.QuarticBregmanKernel
