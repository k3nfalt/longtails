import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.GeneralizedMirrorPotential

lemma quadratic_radius {t R : ℝ} (hR : 0 < R)
    (h : t ^ 2 / 2 ≤ R ^ 2 / 2 + R * t / 4) : t ≤ 3 * R / 2 := by
  by_contra hn
  push Not at hn
  have hp : 0 < (t - 3 * R / 2) * (t + R) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg R]

lemma prox_radius {E : Type*} [SeminormedAddCommGroup E]
    (D : E → E → ℝ) (u z z' : E) {a e R : ℝ} (hR : 0 < R)
    (hstrong : ‖u - z'‖ ^ 2 / 2 ≤ D u z')
    (hinit : D u z ≤ R ^ 2 / 2)
    (hprox : D u z' ≤ D u z + a * e * ‖u - z'‖)
    (hstep : a * e ≤ R / 4) : ‖u - z'‖ ≤ 3 * R / 2 := by
  apply quadratic_radius hR
  have he := mul_le_mul_of_nonneg_right hstep (norm_nonneg (u - z'))
  nlinarith

lemma prox_displacement {E : Type*} [SeminormedAddCommGroup E]
    {u z z' : E} {R : ℝ} (hz : ‖u - z‖ ≤ R)
    (hz' : ‖u - z'‖ ≤ 3 * R / 2) : ‖z' - z‖ ≤ 5 * R / 2 := by
  have htri := norm_sub_le_norm_sub_add_norm_sub z' u z
  rw [norm_sub_rev z' u] at htri
  linarith

lemma error_displacement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E →L[ℝ] ℝ) (z z' : E) {a : ℝ} (ha : 0 ≤ a) :
    a * e (z - z') ≤ a ^ 2 * ‖e‖ ^ 2 + ‖z' - z‖ ^ 2 / 4 := by
  have he : e (z - z') ≤ ‖e‖ * ‖z' - z‖ := by
    have h := (le_abs_self (e (z - z'))).trans (e.le_opNorm (z - z'))
    simpa only [Real.norm_eq_abs, norm_sub_rev z z'] using h
  have hm := mul_le_mul_of_nonneg_left he ha
  nlinarith [sq_nonneg (a * ‖e‖ - ‖z' - z‖ / 2)]

lemma potential_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F ψ : E → ℝ) (D : E → E → ℝ) (g e : E →L[ℝ] ℝ)
    (u x x' z z' : E) {A a : ℝ} (ha : 0 ≤ a)
    (hmodel : (A + a) * F x' - A * F x - a * F u ≤
      a * (g (z' - u) - e (z' - u) + ψ z' - ψ u) + ‖z' - z‖ ^ 2 / 4)
    (hprox : a * (g (z' - u) + ψ z' - ψ u) ≤
      D u z - D u z' - ‖z' - z‖ ^ 2 / 2) :
    (A + a) * (F x' - F u) + D u z' ≤
      A * (F x - F u) + D u z + a * e (u - z) + a ^ 2 * ‖e‖ ^ 2 := by
  have he : -e (z' - u) = e (u - z) + e (z - z') := by
    simp only [map_sub]
    ring
  have herr := error_displacement e z z' ha
  nlinarith

end LongTails.Proofs.GeneralizedMirrorPotential
