import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_contraction {f : E → ℝ} {x z u g : E} {L μ : ℝ}
    (hL : 0 < L)
    (hupper : f z ≤ f x + ⟪g, z - x⟫ + L / 2 * ‖z - x‖ ^ 2)
    (hlower : f x + ⟪g, u - x⟫ + μ / 2 * ‖u - x‖ ^ 2 ≤ f u)
    (hmin : f u ≤ f z)
    (hproj : 0 ≤ ⟪g + L • (z - x), u - z⟫) :
    ‖z - u‖ ^ 2 ≤ (1 - μ / L) * ‖x - u‖ ^ 2 := by
  have hid : ‖x - u‖ ^ 2 = ‖z - x‖ ^ 2 + ‖z - u‖ ^ 2 -
      2 * ⟪z - x, z - u⟫ := by
    have hh : x - u = (z - u) - (z - x) := by abel
    rw [hh, norm_sub_sq_real, real_inner_comm (z - u) (z - x)]
    ring
  have he : u - x = (u - z) + (z - x) := by abel
  have hg : ⟪g, u - x⟫ = ⟪g, u - z⟫ + ⟪g, z - x⟫ := by rw [he, inner_add_right]
  rw [hg, norm_sub_rev u x] at hlower
  simp only [inner_add_left, real_inner_smul_left] at hproj
  have hz : ⟪z - x, u - z⟫ = -⟪z - x, z - u⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hz] at hproj
  have hh : L * ‖z - u‖ ^ 2 ≤ (L - μ) * ‖x - u‖ ^ 2 := by
    nlinarith
  suffices hh' : L * ‖z - u‖ ^ 2 ≤ L * ((1 - μ / L) * ‖x - u‖ ^ 2) from
    le_of_mul_le_mul_left hh' hL
  calc
    L * ‖z - u‖ ^ 2 ≤ (L - μ) * ‖x - u‖ ^ 2 := hh
    _ = L * ((1 - μ / L) * ‖x - u‖ ^ 2) := by field_simp

lemma outer_descent {a b : ℝ} {g h s : E} {L e : ℝ}
    (hL : 0 < L) (herr : ‖g - h‖ ≤ e)
    (hupper : b ≤ a + ⟪g, s⟫ + L / 2 * ‖s‖ ^ 2)
    (hproj : ⟪h, s⟫ ≤ -(2 * L) * ‖s‖ ^ 2) :
    b ≤ a - L * ‖s‖ ^ 2 + e ^ 2 / (2 * L) := by
  have hi := real_inner_le_norm (g - h) s
  have hm := mul_le_mul_of_nonneg_right herr (norm_nonneg s)
  simp only [inner_sub_left] at hi
  have hy : e * ‖s‖ ≤ L / 2 * ‖s‖ ^ 2 + e ^ 2 / (2 * L) := by
    have hs := sq_nonneg (L * ‖s‖ - e)
    have hdiv : (L * ‖s‖ - e) ^ 2 / (2 * L) ≥ 0 := by positivity
    field_simp at hdiv ⊢
    nlinarith
  linarith

lemma envelope_upper {a b L μ d : ℝ} {g h s : E} (hμ : 0 < μ)
    (herr : ‖h - g‖ ≤ L * d)
    (hupper : b ≤ a + ⟪h, s⟫ + L / 2 * ‖s‖ ^ 2 - μ / 2 * d ^ 2) :
    b ≤ a + ⟪g, s⟫ + (L + L ^ 2 / μ) / 2 * ‖s‖ ^ 2 := by
  have hi := real_inner_le_norm (h - g) s
  have hm := mul_le_mul_of_nonneg_right herr (norm_nonneg s)
  simp only [inner_sub_left] at hi
  have hy : L * d * ‖s‖ ≤ μ / 2 * d ^ 2 + L ^ 2 / (2 * μ) * ‖s‖ ^ 2 := by
    have hdiv : (μ * d - L * ‖s‖) ^ 2 / (2 * μ) ≥ 0 := by positivity
    field_simp at hdiv ⊢
    nlinarith
  have he : (L + L ^ 2 / μ) / 2 = L / 2 + L ^ 2 / (2 * μ) := by ring
  rw [he]
  nlinarith

end LongTails.Proofs.CoupledMinimaxDescent
