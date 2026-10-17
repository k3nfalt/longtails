import LongTails.Proofs.GuardedMetricSupport
import LongTails.Algorithms.GuardedMetricAcceleration

namespace LongTails.Proofs.GuardedMetricDescent

open scoped RealInnerProductSpace
open LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma regularization_difference (α fu fv : ℝ) (c u v gv : E) :
    regularizedValue α c u fu - regularizedValue α c v fv -
      ⟪regularizedGradient α c v gv, u - v⟫ = fu - fv - ⟪gv, u - v⟫ + α * ‖u - v‖ ^ 2 := by
  unfold regularizedValue regularizedGradient
  rw [show u - c = (u - v) + (v - c) by abel, norm_add_sq_real]
  simp only [inner_add_left, real_inner_smul_left]
  rw [real_inner_comm (u - v) (v - c)]
  ring

lemma transformed_pairing (S : E ≃L[ℝ] E) (g h : E) :
    ⟪g, S.symm h⟫ = ⟪transformedGradient S g, h⟫ :=
  (S.symm.toContinuousLinearMap.adjoint_inner_left h g).symm

lemma metric_pairing (S : E ≃L[ℝ] E) (g d : E) :
    ⟪g, d⟫ = ⟪transformedGradient S g, S d⟫ := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using transformed_pairing S g (S d)

lemma metric_gradient_descent {F : E → ℝ} (S : E ≃L[ℝ] E) (y g : E) {L t : ℝ}
    (ht : 0 ≤ t) (htL : L * t ≤ 1)
    (hmodel : F (y - S.symm (t • transformedGradient S g)) ≤ F y +
      ⟪g, -S.symm (t • transformedGradient S g)⟫ +
      L / 2 * ‖S (-S.symm (t • transformedGradient S g))‖ ^ 2) :
    F (y - S.symm (t • transformedGradient S g)) ≤ F y - t / 2 * ‖transformedGradient S g‖ ^ 2 := by
  have hi : ⟪g, -S.symm (t • transformedGradient S g)⟫ = -t * ‖transformedGradient S g‖ ^ 2 := by
    rw [inner_neg_right, transformed_pairing, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hn : ‖S (-S.symm (t • transformedGradient S g))‖ ^ 2 = t ^ 2 * ‖transformedGradient S g‖ ^ 2 := by
    rw [map_neg, ContinuousLinearEquiv.apply_symm_apply, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  rw [hi, hn] at hmodel
  have hh := mul_le_mul_of_nonneg_right htL (mul_nonneg ht (sq_nonneg ‖transformedGradient S g‖))
  nlinarith

lemma support_center_upper (S : E ≃L[ℝ] E) (c y g : E) {Fc Fy μ : ℝ}
    (hμ : 0 ≤ μ)
    (hsupport : Fy + ⟪g, c - y⟫ + μ / 2 * ‖S (c - y)‖ ^ 2 ≤ Fc) :
    Fy ≤ Fc + ‖transformedGradient S g‖ * ‖S (y - c)‖ := by
  have hi := real_inner_le_norm (transformedGradient S g) (S (y - c))
  rw [← metric_pairing] at hi
  have he : ⟪g, c - y⟫ = -⟪g, y - c⟫ := by rw [← neg_sub y c, inner_neg_right]
  rw [he] at hsupport
  have hp : 0 ≤ μ / 2 * ‖S (c - y)‖ ^ 2 := by positivity
  linarith

lemma gradient_norm_bound (S : E ≃L[ℝ] E) {M : ℝ}
    (hM : ∀ v, ‖S v‖ ^ 2 ≤ M * ‖v‖ ^ 2) (g : E) :
    ‖g‖ ^ 2 ≤ M * ‖transformedGradient S g‖ ^ 2 := by
  have hi := real_inner_le_norm (transformedGradient S g) (S g)
  rw [← metric_pairing, real_inner_self_eq_norm_sq] at hi
  have hs := pow_le_pow_left₀ (sq_nonneg ‖g‖) hi 2
  have hm := mul_le_mul_of_nonneg_left (hM g) (sq_nonneg ‖transformedGradient S g‖)
  by_cases hg : g = 0
  · subst g
    simp [transformedGradient]
  have hn : 0 < ‖g‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hp : ‖g‖ ^ 2 * ‖g‖ ^ 2 ≤ (M * ‖transformedGradient S g‖ ^ 2) * ‖g‖ ^ 2 := by
    nlinarith only [hs, hm]
  exact (mul_le_mul_iff_left₀ hn).mp hp

lemma proximal_progress {Fc Fx α ε n G Gf : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hvalue : Fx + α * n ^ 2 ≤ Fc) (hlarge : ε < G) (hsmall : Gf ≤ ε / 2)
    (htriangle : G ≤ Gf + 2 * α * n) :
    ε ^ 2 / (16 * α) ≤ Fc - Fx := by
  have hd : ε / 2 ≤ 2 * α * n := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ε / 2) hd 2
  apply (div_le_iff₀ (by positivity : 0 < 16 * α)).mpr
  have hv := mul_le_mul_of_nonneg_left hvalue hα.le
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma regularized_upper (S : E ≃L[ℝ] E) (c u v gv : E) {fu fv α β : ℝ}
    (hα : α ≤ β) (hnorm : β * ‖u - v‖ ^ 2 ≤ ‖S (u - v)‖ ^ 2)
    (hmodel : fu - fv - ⟪gv, u - v⟫ ≤ 9 / 16 * ‖S (u - v)‖ ^ 2) :
    regularizedValue α c u fu ≤ regularizedValue α c v fv +
      ⟪regularizedGradient α c v gv, u - v⟫ + 2 * ‖S (u - v)‖ ^ 2 := by
  have hid := regularization_difference α fu fv c u v gv
  have hh := mul_le_mul_of_nonneg_right hα (sq_nonneg ‖u - v‖)
  nlinarith [sq_nonneg ‖S (u - v)‖]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma regularized_distance {α Fc Fx q : ℝ} (c x : E)
    (hvalue : regularizedValue α c x Fx ≤ Fc) (hgap : Fc - q ≤ Fx) :
    α * ‖x - c‖ ^ 2 ≤ q := by
  unfold regularizedValue at hvalue
  linarith

omit [FiniteDimensional ℝ E] in
lemma small_regularized_progress {α ε Fc Fx : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (c x gx : E) (hvalue : regularizedValue α c x Fx ≤ Fc)
    (hlarge : ε < ‖gx‖) (hsmall : ‖regularizedGradient α c x gx‖ ≤ ε / 2) :
    ε ^ 2 / (16 * α) ≤ Fc - Fx := by
  apply proximal_progress hα hε hvalue hlarge hsmall
  have he : gx = regularizedGradient α c x gx - (2 * α) • (x - c) := by
    simp [regularizedGradient]
  calc
    ‖gx‖ = ‖regularizedGradient α c x gx - (2 * α) • (x - c)‖ := congrArg norm he
    _ ≤ ‖regularizedGradient α c x gx‖ + ‖(2 * α) • (x - c)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma truncated_progress_half {L r G A Fy Fc Fnext : ℝ} (hr : 0 < r) (hG : 0 ≤ G)
    (hlarge : L * r / 2 < G) (hA : A ≤ r / 8)
    (hsupport : Fy ≤ Fc + G * A) (hdescent : Fnext ≤ Fy - G * r / 4) :
    Fnext ≤ Fc - L * r ^ 2 / 16 := by
  have ha := mul_le_mul_of_nonneg_left hA hG
  have hg := mul_lt_mul_of_pos_right hlarge hr
  nlinarith

lemma no_progress_full_coefficient {L r G A Fy Fc Fnext q : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hG : 0 ≤ G) (hA : A ≤ r / 8)
    (hq : q ≤ L * r ^ 2 / 16)
    (hsupport : Fy ≤ Fc + G * A)
    (hdescent : Fnext ≤ Fy - min L⁻¹ (r / (2 * G)) / 2 * G ^ 2)
    (hnoprogress : Fc - q < Fnext) : G = 0 ∨ min L⁻¹ (r / (2 * G)) = L⁻¹ := by
  by_cases hz : G = 0
  · exact Or.inl hz
  have hp : 0 < G := lt_of_le_of_ne hG (Ne.symm hz)
  by_cases hfull : L⁻¹ ≤ r / (2 * G)
  · exact Or.inr (min_eq_left hfull)
  have ht : r / (2 * G) < L⁻¹ := lt_of_not_ge hfull
  have hg : L * r / 2 < G := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * G)).mp ht
    have hh' := mul_lt_mul_of_pos_left hh hL
    field_simp at hh'
    nlinarith
  rw [min_eq_right ht.le] at hdescent
  have he : r / (2 * G) / 2 * G ^ 2 = G * r / 4 := by field_simp; ring
  rw [he] at hdescent
  have hh := truncated_progress_half hr hG hg hA hsupport hdescent
  exfalso
  linarith

end LongTails.Proofs.GuardedMetricDescent
