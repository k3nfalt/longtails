import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothShield

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_add_controls_sum (u v : E)
    (h : -(‖u‖ * ‖v‖) ≤ 2 * ⟪u, v⟫) :
    ‖u‖ + ‖v‖ ≤ 2 * ‖u + v‖ := by
  have he := norm_add_sq_real u v
  have hs := sq_nonneg (‖u‖ - ‖v‖)
  have hn := norm_nonneg (u + v)
  nlinarith [norm_nonneg u, norm_nonneg v]

lemma weighted_norm_control (u v : E) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (h : -(‖u‖ * ‖v‖) ≤ 2 * ⟪u, v⟫) :
    t * ‖u‖ + (1 - t) * ‖v‖ ≤ 2 * ‖t • u + (1 - t) • v‖ := by
  have hprod : 0 ≤ t * (1 - t) := mul_nonneg ht (sub_nonneg.mpr ht')
  have hh := mul_le_mul_of_nonneg_left h hprod
  have hangle : -(‖t • u‖ * ‖(1 - t) • v‖) ≤
      2 * ⟪t • u, (1 - t) • v⟫ := by
    simp only [norm_smul, Real.norm_of_nonneg ht,
      Real.norm_of_nonneg (sub_nonneg.mpr ht'), real_inner_smul_left,
      real_inner_smul_right]
    nlinarith only [hh]
  simpa only [norm_smul, Real.norm_of_nonneg ht,
    Real.norm_of_nonneg (sub_nonneg.mpr ht')] using
    norm_add_controls_sum (t • u) ((1 - t) • v) hangle

lemma radial_angle_of_minimizer (f : E → ℝ) (g x z : E) (r : ℝ)
    (hmodel : f x + ⟪g, z - x⟫ ≤ f z) (hmin : f z ≤ f x)
    (hz : ‖z‖ ≤ r) (hx : 2 * r ≤ ‖x‖) :
    -(‖g‖ * ‖x‖) ≤ 2 * ⟪g, x⟫ := by
  rw [inner_sub_right] at hmodel
  have hb := (abs_le.mp (abs_real_inner_le_norm g z)).1
  have hr := mul_le_mul_of_nonneg_left hz (norm_nonneg g)
  have hx' := mul_le_mul_of_nonneg_left hx (norm_nonneg g)
  nlinarith

end LongTails.Proofs.GeneralizedSmoothShield
