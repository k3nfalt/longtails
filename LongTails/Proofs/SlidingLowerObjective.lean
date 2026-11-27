import LongTails.Proofs.SlidingLowerGeometry
import LongTails.Proofs.SoftRadialProjection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.SlidingLowerObjective

open SlidingLowerChain SlidingLowerGeometry SoftRadialProjection

variable {d T : ℕ}

lemma project_taylor {R : ℝ} (hR : 0 < R) (x y : Point d) :
    ‖project R y - project R x - derivative R x (y - x)‖ ≤ (6 / R) * ‖y - x‖ ^ 2 := by
  let φ : Point d → Point d := fun z => project R z - derivative R x z
  have hφ : ∀ z ∈ Metric.closedBall x ‖y - x‖,
      HasFDerivWithinAt φ (derivative R z - derivative R x) (Metric.closedBall x ‖y - x‖) z := by
    intro z _
    exact ((project_hasFDerivAt hR z).sub (derivative R x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall x ‖y - x‖,
      ‖derivative R z - derivative R x‖ ≤ (6 / R) * ‖y - x‖ := by
    intro z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have h := derivative_difference hR z x w
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by simpa [dist_eq_norm] using hz
    calc _ ≤ (6 / R) * ‖z - x‖ * ‖w‖ := h
      _ ≤ (6 / R) * ‖y - x‖ * ‖w‖ := by gcongr
  have hy : y ∈ Metric.closedBall x ‖y - x‖ := by simp [dist_eq_norm]
  have hx : x ∈ Metric.closedBall x ‖y - x‖ := by simp
  have h := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hφ hb hx hy
  have he : φ y - φ x = project R y - project R x - derivative R x (y - x) := by
    simp only [φ, map_sub]; abel
  rw [he] at h
  calc _ ≤ (6 / R) * ‖y - x‖ * ‖y - x‖ := h
    _ = _ := by ring

lemma compressed_support {R G : ℝ} (hR : 0 < R) (hG : 0 ≤ G) {H : Point d → ℝ}
    {gH : Point d → Point d} (hconv : ∀ a b, H a + ⟪gH a, b - a⟫ ≤ H b)
    (hbound : ∀ a, ‖gH a‖ ≤ G) (x y : Point d) :
    H (project R x) + 6 * G / R * ‖x‖ ^ 2 +
        ⟪derivative R x (gH (project R x)) + (12 * G / R) • x, y - x⟫ ≤
      H (project R y) + 6 * G / R * ‖y‖ ^ 2 := by
  have h1 := hconv (project R x) (project R y)
  have ht := project_taylor hR x y
  have hrem : |⟪gH (project R x), project R y - project R x - derivative R x (y - x)⟫| ≤
      G * ((6 / R) * ‖y - x‖ ^ 2) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hbound _) ht (norm_nonneg _) hG)
  have hsplit : ⟪gH (project R x), project R y - project R x⟫ =
      ⟪derivative R x (gH (project R x)), y - x⟫ +
        ⟪gH (project R x), project R y - project R x - derivative R x (y - x)⟫ := by
    rw [derivative_self_adjoint, ← inner_add_right]
    congr 1
    abel
  have hq : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 := by
    have e : y = x + (y - x) := by abel
    conv_lhs => rw [e]
    rw [norm_add_sq_real]
  rw [inner_add_left, inner_smul_left]
  simp only [conj_trivial]
  have hq' : 6 * G / R * ‖y‖ ^ 2 =
      6 * G / R * ‖x‖ ^ 2 + 12 * G / R * ⟪x, y - x⟫ + 6 * G / R * ‖y - x‖ ^ 2 := by
    rw [hq]; ring
  have e6 : G * ((6 / R) * ‖y - x‖ ^ 2) = 6 * G / R * ‖y - x‖ ^ 2 := by ring
  linarith [neg_abs_le ⟪gH (project R x), project R y - project R x - derivative R x (y - x)⟫]

end LongTails.Proofs.SlidingLowerObjective
