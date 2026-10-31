import LongTails.Proofs.GdConvex
import LongTails.Proofs.RelativeGeneralizedGeometry

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma energy_step {f : E → ℝ} {g : E → E} {c u x y z x' z' e : E}
    {A a η R α : ℝ} (hf : ConvexOn ℝ univ f)
    (hg : ∀ w, HasGradientAt f (g w) w)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hu : ‖u - c‖ ≤ R) (hz : ‖z - c‖ ≤ 2 * R)
    (he : ‖e‖ ≤ α * ‖g y‖)
    (hweight : 1024 * a ^ 2 ≤ η * (A + a))
    (hcouple : A • (y - x) + a • (y - z) = 0)
    (hdesc : f x' ≤ f y - η / 64 * ‖g y‖ ^ 2)
    (hmirror : ‖z' - u‖ ^ 2 ≤ ‖z - a • (g y + e) - u‖ ^ 2) :
    (A + a) * (f x' - f u) + 1 / 2 * ‖z' - u‖ ^ 2 ≤
      A * (f x - f u) + 1 / 2 * ‖z - u‖ ^ 2 + α ^ 2 * R ^ 2 := by
  have hcx := Gradient.convex_support hf hg y x
  have hcu := Gradient.convex_support hf hg y u
  have hid := congrArg (fun w => ⟪g y, w⟫) hcouple
  simp only [inner_add_right, inner_smul_right, inner_sub_right, inner_zero_right] at hid
  simp only [inner_sub_right] at hcx hcu
  have hdist : ‖z - u‖ ≤ 3 * R := by
    calc
      _ ≤ ‖z - c‖ + ‖c - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 * R := by rw [norm_sub_rev c u]; linarith
  have herr : -⟪e, z - u⟫ ≤ 3 * α * R * ‖g y‖ := by
    have h1 := real_inner_le_norm (-e) (z - u)
    rw [inner_neg_left, norm_neg] at h1
    have h2 := mul_le_mul he hdist (norm_nonneg _) (by positivity : 0 ≤ α * ‖g y‖)
    nlinarith
  have hgn : ‖g y + e‖ ≤ 2 * ‖g y‖ := by
    have h1 := norm_add_le (g y) e
    have h2 := mul_le_mul_of_nonneg_right hα1 (norm_nonneg (g y))
    linarith
  have hgsq : ‖g y + e‖ ^ 2 ≤ 4 * ‖g y‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgn)
      (show 0 ≤ 2 * ‖g y‖ + ‖g y + e‖ by positivity)]
  have hnorm : ‖z - a • (g y + e) - u‖ ^ 2 =
      ‖z - u‖ ^ 2 - 2 * a * (⟪g y, z - u⟫ + ⟪e, z - u⟫) +
        a ^ 2 * ‖g y + e‖ ^ 2 := by
    have heq : z - a • (g y + e) - u = (z - u) - a • (g y + e) := by module
    rw [heq, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, real_inner_comm, inner_add_left]
    ring
  rw [hnorm] at hmirror
  have h1 := mul_le_mul_of_nonneg_left hdesc (add_nonneg hA ha)
  have h2 := mul_le_mul_of_nonneg_left hcx hA
  have h3 := mul_le_mul_of_nonneg_left hcu ha
  have h4 := mul_le_mul_of_nonneg_left herr ha
  have h5 := mul_le_mul_of_nonneg_left hgsq (sq_nonneg a)
  have h6 := mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖g y‖)
  have hyoung := sq_nonneg (3 * a * ‖g y‖ - α * R)
  rw [inner_sub_right] at hmirror
  nlinarith [sq_nonneg (a * ‖g y‖)]

end OracleTemplate.RelativeGeneralized
