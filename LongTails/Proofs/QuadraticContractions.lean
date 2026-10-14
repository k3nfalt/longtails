import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.MarkovQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma quadratic_cocoercivity (H : E →L[ℝ] E) {L : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (x : E) :
    ‖H x‖ ^ 2 ≤ L * ⟪x, H x⟫ := by
  have hsym : ⟪x, H (H x)⟫ = ‖H x‖ ^ 2 := by
    calc
      ⟪x, H (H x)⟫ = ⟪H x, H x⟫ := by
        simpa only [hs] using H.adjoint_inner_right x (H x)
      _ = ‖H x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hn := hp (L • x - H x)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial,
    hsym, real_inner_self_eq_norm_sq] at hn
  have hm : L * ‖H x‖ ^ 2 ≤ L * (L * ⟪x, H x⟫) := by
    nlinarith [hb (H x)]
  exact le_of_mul_le_mul_left hm hL

lemma quadratic_step_energy (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (x : E) :
    η * (2 - η * L) * ⟪x, H x⟫ ≤ ‖x‖ ^ 2 - ‖x - η • H x‖ ^ 2 := by
  have hc := mul_le_mul_of_nonneg_left (quadratic_cocoercivity H hL hs hp hb x)
    (sq_nonneg η)
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  nlinarith

lemma quadratic_step_increment (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2)
    (hηL : η * L < 2) (x : E) :
    ‖η • H x‖ ^ 2 ≤ η * L / (2 - η * L) *
      (‖x‖ ^ 2 - ‖x - η • H x‖ ^ 2) := by
  have hc := quadratic_cocoercivity H hL hs hp hb x
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hηL)).mpr
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg η)
  nlinarith

lemma quadratic_step_contract (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hηL : η * L ≤ 2) (x : E) : ‖x - η • H x‖ ≤ ‖x‖ := by
  have he := quadratic_step_energy H hL hs hp hb (η := η) x
  have hn : 0 ≤ η * (2 - η * L) * ⟪x, H x⟫ :=
    mul_nonneg (mul_nonneg hη (sub_nonneg.mpr hηL)) (hp x)
  nlinarith [norm_nonneg (x - η • H x), norm_nonneg x]

lemma quadratic_comparison (H : E →L[ℝ] E) {L : ℝ}
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (x y : E) :
    ⟪x, H x⟫ ≤ 2 * ⟪y, H y⟫ + 2 * L * ‖x - y‖ ^ 2 := by
  have hxy : ⟪x, H y⟫ = ⟪y, H x⟫ := by
    calc
      ⟪x, H y⟫ = ⟪H x, y⟫ := by simpa only [hs] using H.adjoint_inner_right x y
      _ = ⟪y, H x⟫ := real_inner_comm _ _
  have hn := hp (x - (2 : ℝ) • y)
  have hu := hb (x - y)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, hxy] at hn hu
  nlinarith

lemma quadratic_step_objective (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hηL : η * L ≤ 1) (x : E) :
    η * ⟪x, H x⟫ ≤ ‖x‖ ^ 2 - ‖x - η • H x‖ ^ 2 := by
  have he := quadratic_step_energy H hL hs hp hb (η := η) x
  have hm := mul_nonneg (sub_nonneg.mpr hηL) (mul_nonneg hη (hp x))
  nlinarith

lemma quadratic_step_small_increment (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hηL : η * L ≤ 1) (x : E) :
    ‖η • H x‖ ^ 2 ≤ η * L * (‖x‖ ^ 2 - ‖x - η • H x‖ ^ 2) := by
  have hc := mul_le_mul_of_nonneg_left (quadratic_cocoercivity H hL hs hp hb x)
    (sq_nonneg η)
  have he := mul_le_mul_of_nonneg_left
    (quadratic_step_objective H hL hs hp hb hη hηL x) (mul_nonneg hη hL.le)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

end OracleTemplate.MarkovQuadratic
