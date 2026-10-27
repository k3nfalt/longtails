import LongTails.Proofs.PLHessianGeometry

open Set InnerProductSpace Filter Topology Asymptotics
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma pl_error_bound [FiniteDimensional ℝ E] {f : E → ℝ} {L μ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : IsMinOn f univ u)
    (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2) (x : E) :
    ∃ p, IsMinOn f univ p ∧ μ ^ 2 * ‖x - p‖ ^ 2 ≤ 8 * ‖gradient f x‖ ^ 2 := by
  obtain ⟨p, hp, hd⟩ := PLHessian.quad_growth hL hμ hμL hg hlip hu hpl x
  refine ⟨p, hp, ?_⟩
  have hd' := mul_le_mul_of_nonneg_left hd hμ.le
  nlinarith [hpl x]

lemma weighted_primal_gap {L μ a b d value saddle primal dual : ℝ}
    (hL : 0 < L) (hμ : 0 < μ)
    (hdual : dual ≤ saddle)
    (hmax : primal - value ≤ b ^ 2 / (2 * μ))
    (hmin : value - dual ≤ a ^ 2 / (2 * L))
    (hgrowth : L / 2 * d ^ 2 ≤ primal - saddle) :
    d ^ 2 ≤ a ^ 2 / L ^ 2 + b ^ 2 / (L * μ) := by
  have hgap : L / 2 * d ^ 2 ≤ b ^ 2 / (2 * μ) + a ^ 2 / (2 * L) := by linarith
  field_simp at hgap ⊢
  nlinarith

lemma saddle_perturbation_gap {L r oldValue newEnvelope newDual : ℝ}
    (hupper : newEnvelope ≤ oldValue)
    (hlower : oldValue - 2 * L * r ^ 2 ≤ newDual) :
    newEnvelope - newDual ≤ 2 * L * r ^ 2 := by linarith

omit [CompleteSpace E] in
lemma lift_energy {F : Type*} [NormedAddCommGroup F]
    {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (h u : E) (v : F)
    (henergy : L * ‖u‖ ^ 2 + μ * ‖v‖ ^ 2 ≤ 2 * L * ⟪h, u⟫) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ (4 + L / μ) * ‖h‖ ^ 2 := by
  have hcomplete : L * ‖u - h‖ ^ 2 + μ * ‖v‖ ^ 2 ≤ L * ‖h‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm h u]
    nlinarith
  have hv : μ * ‖v‖ ^ 2 ≤ L * ‖h‖ ^ 2 := by
    nlinarith [mul_nonneg hL.le (sq_nonneg ‖u - h‖)]
  have hu : ‖u‖ ≤ 2 * ‖h‖ := by
    have hi := real_inner_le_norm h u
    have hh : L * ‖u‖ ^ 2 ≤ 2 * L * (‖h‖ * ‖u‖) := by
      nlinarith [mul_nonneg hμ.le (sq_nonneg ‖v‖)]
    have hh' : ‖u‖ ^ 2 ≤ 2 * (‖h‖ * ‖u‖) := by nlinarith
    nlinarith [norm_nonneg u, norm_nonneg h]
  have hv' : ‖v‖ ^ 2 ≤ L / μ * ‖h‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith
  nlinarith [sq_nonneg (2 * ‖h‖ - ‖u‖), norm_nonneg u, norm_nonneg h]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasFDerivAt_of_quadratic_remainder {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℝ E] {G : E → F} {A : E →L[ℝ] F} {x : E} {C : ℝ}
    (hbound : ∀ h, ‖G (x + h) - G x - A h‖ ≤ C * ‖h‖ ^ 2) : HasFDerivAt G A x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : E => G (x + h) - G x - A h) =O[nhds 0]
      (fun h : E => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2)]
    exact hbound h
  have hlit : (fun h : E => ‖h‖ ^ 2) =o[nhds 0] (fun h : E => h) := by
    have h0 := (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)).comp_tendsto
      (tendsto_norm_zero (E := E))
    exact Asymptotics.isLittleO_norm_right.mp h0
  exact hbig.trans_isLittleO hlit

end OracleTemplate.PLMinimax
