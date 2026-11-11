import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Proofs.TensorFreeModel
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.LogFreeLineSearch
import LongTails.Proofs.LogFreeLinearAlgebra

namespace LongTails.Proofs.LogFreeGeometry

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def regF (f : E → ℝ) (γ : ℝ) (c z : E) : ℝ := f z + γ / 2 * ‖z - c‖ ^ 2

omit [FiniteDimensional ℝ E] in
lemma sq_norm_shift (a e : E) (t : ℝ) :
    ‖a + t • e‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * ⟪a, e⟫ + t ^ 2 * ‖e‖ ^ 2 := by
  rw [@norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

section Taylor

variable {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ} (hL : 0 ≤ L)
  (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
    fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
include hf hL hT

lemma line_expansion (γ : ℝ) (c y e : E) (t : ℝ) :
    |regF f γ c (y + t • e) - (regF f γ c y + t * ⟪gradient f y + γ • (y - c), e⟫ +
      t ^ 2 / 2 * (⟪fderiv ℝ (gradient f) y e, e⟫ + γ * ‖e‖ ^ 2) +
      t ^ 3 / 6 * ⟪fderiv ℝ (fderiv ℝ (gradient f)) y e e, e⟫)| ≤ L * ‖e‖ ^ 4 * |t| ^ 4 := by
  have h := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT y e t
  have hn : ‖y + t • e - c‖ ^ 2 = ‖y - c‖ ^ 2 + 2 * t * ⟪y - c, e⟫ + t ^ 2 * ‖e‖ ^ 2 := by
    have : y + t • e - c = (y - c) + t • e := by abel
    rw [this, sq_norm_shift]
  have hi : ⟪gradient f y + γ • (y - c), e⟫ = ⟪gradient f y, e⟫ + γ * ⟪y - c, e⟫ := by
    rw [inner_add_left, real_inner_smul_left]
  unfold regF
  rw [hn, hi]
  have he : f (y + t • e) + γ / 2 * (‖y - c‖ ^ 2 + 2 * t * ⟪y - c, e⟫ + t ^ 2 * ‖e‖ ^ 2) -
      (f y + γ / 2 * ‖y - c‖ ^ 2 + t * (⟪gradient f y, e⟫ + γ * ⟪y - c, e⟫) +
        t ^ 2 / 2 * (⟪fderiv ℝ (gradient f) y e, e⟫ + γ * ‖e‖ ^ 2) +
        t ^ 3 / 6 * ⟪fderiv ℝ (fderiv ℝ (gradient f)) y e e, e⟫) =
      f (y + t • e) - f y - ⟪gradient f y, e⟫ * t - ⟪fderiv ℝ (gradient f) y e, e⟫ * t ^ 2 / 2 -
        ⟪fderiv ℝ (fderiv ℝ (gradient f)) y e e, e⟫ * t ^ 3 / 6 := by ring
  rw [he]
  exact h

lemma plain_escape (γ r : ℝ) (y v : E) (hv : ‖v‖ = 1)
    (hneg : ⟪fderiv ℝ (gradient f) y v, v⟫ ≤ -(γ / 4)) :
    min (f (y + r • v)) (f (y - r • v)) ≤ f y - γ * r ^ 2 / 8 + L * r ^ 4 := by
  have hp := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT y v r
  have hm := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT y v (-r)
  have hneg' : y + (-r) • v = y - r • v := by rw [neg_smul, ← sub_eq_add_neg]
  rw [hneg'] at hm
  rw [hv] at hp hm
  have ha : |(-r)| ^ 4 = r ^ 4 := by rw [abs_neg, pow_abs]; exact abs_of_nonneg (by positivity)
  have hb : |r| ^ 4 = r ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [ha] at hm
  rw [hb] at hp
  have hp' := (abs_le.mp hp).2
  have hm' := (abs_le.mp hm).2
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hH := mul_le_mul_of_nonneg_right hneg hr2
  have hmin1 := min_le_left (f (y + r • v)) (f (y - r • v))
  have hmin2 := min_le_right (f (y + r • v)) (f (y - r • v))
  nlinarith

end Taylor

end LongTails.Proofs.LogFreeGeometry
