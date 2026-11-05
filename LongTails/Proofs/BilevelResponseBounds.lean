import LongTails.Proofs.BilevelGeometry

set_option maxSynthPendingDepth 5

namespace LongTails.Proofs.BilevelResponseBounds

open LongTails.Setups.HigherSmoothBilevel BilevelGeometry BilevelCurvature BilevelImplicitEstimates
open scoped RealInnerProductSpace

lemma second_response_bounds {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hLip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hLip2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hLip3 : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    {q : ℝ} (hq : 1 ≤ q) (heq : p.μ * q ^ 2 = p.L)
    (x a b : p.X) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    let z := fderiv ℝ (fderiv ℝ (lowerSolution I)) x b a
    Real.sqrt ⟪(p.L⁻¹ • lowerHessian I (x, lowerSolution I x)) z, z⟫ ≤ 16 * q ^ 4 ∧
      ‖z‖ ≤ 16 * q ^ 5 := by
  let s := (x, lowerSolution I x)
  let H := lowerHessian I s
  let T := p.L⁻¹ • fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) s
  let Y := fderiv ℝ (lowerSolution I) x
  let Z := fderiv ℝ (fderiv ℝ (lowerSolution I)) x b a
  have hsym : ∀ u v, ⟪(p.L⁻¹ • H) u, v⟫ = ⟪(p.L⁻¹ • H) v, u⟫ := by
    intro u v
    simp only [smul_apply, inner_smul_left, conj_trivial]
    rw [lowerHessian_symmetric hg]
  have hpos : ∀ v, 0 ≤ ⟪(p.L⁻¹ • H) v, v⟫ := by
    intro v
    simp only [smul_apply, inner_smul_left, conj_trivial]
    exact mul_nonneg (inv_nonneg.mpr hL.le) (lowerHessian_positive hg hμ.le hsc s v)
  let P := energySeminorm (p.L⁻¹ • H) hsym hpos
  have hP : ∀ v, p.L * (P v) ^ 2 = ⟪H v, v⟫ := by
    intro v
    rw [show P v = Real.sqrt ⟪(p.L⁻¹ • H) v, v⟫ from rfl, Real.sq_sqrt (hpos v)]
    simp only [smul_apply, inner_smul_left, conj_trivial]
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  have hc : ∀ v, p.μ * ‖v‖ ^ 2 ≤ ⟪H v, v⟫ := by
    intro v
    dsimp [H, s]
    rw [lowerHessian_eq hg]
    exact lowerHessian_coercive hg hsc x (lowerSolution I x) v
  have hy : ∀ u : p.X, ‖u‖ ≤ 1 → ‖Y u‖ ≤ q ^ 2 ∧ P (Y u) ≤ q := by
    intro u hu
    have hh := lowerSolution_derivative_bounds hg hμ hL.le hsc hLip x u
    apply scaled_response_bounds H P hL hμ (by linarith) heq hP
    · exact hh.1.trans (by nlinarith)
    · exact hh.2.trans (by simpa using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu 2) (sq_nonneg p.L))
  have hTnorm : ‖T‖ ≤ 1 := by
    have ht : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) s‖ ≤ p.L :=
      norm_fderiv_le_of_lip' ℝ hL.le (Filter.Eventually.of_forall (fun z => hLip2 z s))
    dsimp [T]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
    calc
      _ ≤ p.L⁻¹ * p.L := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  have hTb : ∀ w u v, |T w u v| ≤ ‖w‖ * ‖u‖ * ‖v‖ := by
    intro w u v
    calc
      _ = ‖T w u v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖T w u‖ * ‖v‖ := (T w u).le_opNorm v
      _ ≤ (‖T w‖ * ‖u‖) * ‖v‖ := by gcongr; exact (T w).le_opNorm u
      _ ≤ (‖T‖ * ‖w‖ * ‖u‖) * ‖v‖ := by gcongr; exact T.le_opNorm w
      _ ≤ (1 * ‖w‖ * ‖u‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hTs : ∀ w u v, T w u v = T u w v := by
    intro w u v
    simp only [T, smul_apply, smul_eq_mul, third_swap_first hg s w u v]
  have hTs2 : ∀ w u v, T w u v = T w v u := by
    intro w u v
    simp only [T, smul_apply, smul_eq_mul, third_swap_last hg s w u v]
  have hTm : ∀ w u v, |T w (0, u) (0, v)| ≤
      2 * ‖w‖ * (‖u‖ * P v + ‖v‖ * P u) := by
    intro w u v
    have hh := normalized_positive_field_mixed hL (lowerHessian_hasFDerivAt hg)
      (lowerHessian_derivative_lipschitz hLip3) (lowerHessian_positive hg hμ.le hsc)
      (lowerHessian_symmetric hg) s w u v
    simpa only [ContinuousLinearMap.comp_apply, lowerHessianMap_apply,
      lowerRestriction_inner, T, P, energySeminorm_apply, H, smul_apply, smul_eq_mul] using hh
  have henergy : (P Z) ^ 2 = -T (0, Z) (b, Y b) (a, Y a) := by
    rw [show P Z = Real.sqrt ⟪(p.L⁻¹ • H) Z, Z⟫ from rfl, Real.sq_sqrt (hpos Z)]
    simp only [smul_apply, inner_smul_left, conj_trivial]
    have hh := lowerSolution_second_energy_identity hg hμ hsc x a b
    change ⟪H Z, Z⟫ = _ at hh
    rw [hh]
    simp only [T, smul_apply, smul_eq_mul, mul_neg]
    rfl
  exact implicit_second_energy T P hq hTb hTs hTs2 hTm hb ha
    (hy b hb).1 (hy a ha).1 (hy b hb).2 (hy a ha).2
    (scaled_coercivity H P hμ (by linarith) heq hP hc Z) henergy

end LongTails.Proofs.BilevelResponseBounds
