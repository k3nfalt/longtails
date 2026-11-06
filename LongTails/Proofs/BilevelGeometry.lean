import LongTails.Setups.HigherSmoothBilevel
import LongTails.Proofs.BilevelMinimizers
import LongTails.Proofs.BilevelCurvature
import LongTails.Proofs.BilevelImplicit
import LongTails.Proofs.BilevelImplicitEstimates
import LongTails.Proofs.HessianLipschitzModel

set_option maxSynthPendingDepth 5

namespace LongTails.Proofs.BilevelGeometry

open LongTails.Setups.HigherSmoothBilevel
open scoped RealInnerProductSpace

noncomputable def lowerRestriction (p : Params) : ((p.X × p.Y) →L[ℝ] ℝ) →L[ℝ] p.Y :=
  (InnerProductSpace.toDual ℝ p.Y).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ p.Y (p.X × p.Y) ℝ).flip (.inr ℝ p.X p.Y))

lemma lowerRestriction_apply (p : Params) (A : (p.X × p.Y) →L[ℝ] ℝ) :
    lowerRestriction p A = (InnerProductSpace.toDual ℝ p.Y).symm
      (A.comp (.inr ℝ p.X p.Y)) := rfl

lemma lowerRestriction_norm (p : Params) : ‖lowerRestriction p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [lowerRestriction_apply, (InnerProductSpace.toDual ℝ p.Y).symm.norm_map, one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ p.X p.Y) (norm_nonneg A))


noncomputable def lowerJacobianMap (p : Params) :
    ((p.X × p.Y) →L[ℝ] (p.X × p.Y) →L[ℝ] ℝ) →L[ℝ] ((p.X × p.Y) →L[ℝ] p.Y) :=
  (ContinuousLinearMap.compL ℝ (p.X × p.Y) ((p.X × p.Y) →L[ℝ] ℝ) p.Y) (lowerRestriction p)

lemma lowerJacobianMap_apply (p : Params)
    (A : (p.X × p.Y) →L[ℝ] (p.X × p.Y) →L[ℝ] ℝ) (v : p.X × p.Y) :
    lowerJacobianMap p A v = lowerRestriction p (A v) := rfl


lemma lowerJacobianMap_norm (p : Params) : ‖lowerJacobianMap p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  change ‖(lowerRestriction p).comp A‖ ≤ ‖A‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (lowerRestriction_norm p) (norm_nonneg A))

noncomputable def lowerHessianMap (p : Params) :
    ((p.X × p.Y) →L[ℝ] (p.X × p.Y) →L[ℝ] ℝ) →L[ℝ] (p.Y →L[ℝ] p.Y) :=
  ((ContinuousLinearMap.compL ℝ p.Y (p.X × p.Y) p.Y).flip (.inr ℝ p.X p.Y)).comp
    ((ContinuousLinearMap.compL ℝ (p.X × p.Y) ((p.X × p.Y) →L[ℝ] ℝ) p.Y)
      (lowerRestriction p))

lemma lowerHessianMap_apply (p : Params)
    (A : (p.X × p.Y) →L[ℝ] (p.X × p.Y) →L[ℝ] ℝ) (v : p.Y) :
    lowerHessianMap p A v = lowerRestriction p (A (0, v)) := rfl

lemma lowerHessianMap_norm (p : Params) : ‖lowerHessianMap p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  rw [lowerHessianMap_apply]
  calc
    _ ≤ ‖lowerRestriction p‖ * ‖A (0, v)‖ := (lowerRestriction p).le_opNorm _
    _ ≤ 1 * (‖A‖ * ‖(0, v)‖) :=
      mul_le_mul (lowerRestriction_norm p) (A.le_opNorm _) (norm_nonneg _) zero_le_one
    _ = ‖A‖ * ‖v‖ := by simp

noncomputable def lowerHessian {p : Params} (I : Instance p) (z : p.X × p.Y) : p.Y →L[ℝ] p.Y :=
  lowerHessianMap p (fderiv ℝ (fderiv ℝ I.g) z)

lemma lowerHessian_hasFDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (z : p.X × p.Y) :
    HasFDerivAt (lowerHessian I)
      ((lowerHessianMap p).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z)) z := by
  have hd : ContDiff ℝ 2 (fderiv ℝ I.g) := (contDiff_succ_iff_fderiv.mp hg).2.2
  have hdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ I.g)) := (contDiff_succ_iff_fderiv.mp hd).2.2
  exact (lowerHessianMap p).hasFDerivAt.comp z (hdd.differentiable (by norm_num) z).hasFDerivAt

noncomputable def lowerGradient {p : Params} (I : Instance p) (z : p.X × p.Y) : p.Y :=
  (InnerProductSpace.toDual ℝ p.Y).symm
    ((fderiv ℝ I.g z).comp (.inr ℝ p.X p.Y))

lemma lowerGradient_contDiff {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g) :
    ContDiff ℝ 2 (lowerGradient I) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ I.g) := (contDiff_succ_iff_fderiv.mp hg).2.2
  exact (InnerProductSpace.toDual ℝ p.Y).symm.toContinuousLinearMap.contDiff.comp
    (hd.clm_comp contDiff_const)


lemma lowerGradient_hasFDerivAt {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (z : p.X × p.Y) :
    HasFDerivAt (lowerGradient I)
      ((lowerRestriction p).comp (fderiv ℝ (fderiv ℝ I.g) z)) z := by
  have hd : ContDiff ℝ 2 (fderiv ℝ I.g) := (contDiff_succ_iff_fderiv.mp hg).2.2
  exact (lowerRestriction p).hasFDerivAt.comp z
    (hd.differentiable (by norm_num) z).hasFDerivAt


lemma lowerGradient_second_derivative {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (z : p.X × p.Y) :
    fderiv ℝ (fderiv ℝ (lowerGradient I)) z =
      (lowerJacobianMap p).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ I.g) := (contDiff_succ_iff_fderiv.mp hg).2.2
  have hdd : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ I.g)) := (contDiff_succ_iff_fderiv.mp hd).2.2
  have he : fderiv ℝ (lowerGradient I) =
      fun z => lowerJacobianMap p (fderiv ℝ (fderiv ℝ I.g) z) := by
    funext w
    exact (lowerGradient_hasFDerivAt hg w).fderiv
  rw [he]
  exact ((lowerJacobianMap p).hasFDerivAt.comp z
    (hdd.differentiable (by norm_num) z).hasFDerivAt).fderiv


lemma lowerGradient_second_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g)
    (hlip : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    (z w : p.X × p.Y) :
    ‖fderiv ℝ (fderiv ℝ (lowerGradient I)) z -
      fderiv ℝ (fderiv ℝ (lowerGradient I)) w‖ ≤ p.L * ‖z - w‖ := by
  rw [lowerGradient_second_derivative hg, lowerGradient_second_derivative hg,
    ← ContinuousLinearMap.comp_sub]
  calc
    _ ≤ ‖lowerJacobianMap p‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
        fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (p.L * ‖z - w‖) := mul_le_mul (lowerJacobianMap_norm p) (hlip z w)
      (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma lowerGradient_lipschitz {p : Params} {I : Instance p}
    (hlip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (z w : p.X × p.Y) : ‖lowerGradient I z - lowerGradient I w‖ ≤ p.L * ‖z - w‖ := by
  change ‖lowerRestriction p (fderiv ℝ I.g z) - lowerRestriction p (fderiv ℝ I.g w)‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖lowerRestriction p‖ * ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ :=
      (lowerRestriction p).le_opNorm _
    _ ≤ 1 * (p.L * ‖z - w‖) := by
      exact mul_le_mul (lowerRestriction_norm p) (hlip z w) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma lowerGradient_hasGradientAt {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (x : p.X) (y : p.Y) :
    HasGradientAt (fun y => I.g (x, y)) (lowerGradient I (x, y)) y := by
  have hd := (hg (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  simpa [lowerGradient, Function.comp_def] using hd.hasGradientAt

lemma lowerGradient_inner {p : Params} (I : Instance p) (z : p.X × p.Y) (v : p.Y) :
    ⟪lowerGradient I z, v⟫ = fderiv ℝ I.g z (0, v) := by
  have h := (InnerProductSpace.toDual ℝ p.Y).apply_symm_apply
    ((fderiv ℝ I.g z).comp (.inr ℝ p.X p.Y))
  exact DFunLike.congr_fun h v


lemma lowerGradient_root {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) :
    lowerGradient I (x, lowerSolution I x) = 0 := by
  rw [lowerGradient, BilevelMinimizers.lowerSolution_stationary hg hμ hsc x, map_zero]

lemma lowerGradient_root_unique {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y : p.Y)
    (hy : lowerGradient I (x, y) = 0) : y = lowerSolution I x := by
  apply BilevelMinimizers.stationary_eq_lowerSolution hg hμ hsc x y
  apply (InnerProductSpace.toDual ℝ p.Y).symm.injective
  simpa [lowerGradient] using hy

lemma lowerHessian_coercive {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y v : p.Y) :
    p.μ * ‖v‖ ^ 2 ≤ ⟪(fderiv ℝ (lowerGradient I) (x, y)) (0, v), v⟫ := by
  have hd := (lowerGradient_contDiff hg).differentiable (by norm_num)
  have hsec : Differentiable ℝ (fun y => lowerGradient I (x, y)) :=
    hd.comp ((differentiable_const x).prodMk differentiable_id)
  have hs : ∀ a b, I.g (x, a) + ⟪lowerGradient I (x, a), b - a⟫ +
      p.μ / 2 * ‖b - a‖ ^ 2 ≤ I.g (x, b) := by
    intro a b
    simpa only [lowerGradient_inner] using hsc x a b
  have hh := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound hsec hs y v
  have he := ((hd (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).fderiv
  simp only [Function.comp_def] at he
  rw [he] at hh
  exact hh

lemma lowerSolution_contDiff {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) : ContDiff ℝ 2 (lowerSolution I) := by
  have hd := hg.differentiable (by norm_num)
  apply BilevelImplicit.contDiff_root (lowerGradient_contDiff hg) (by norm_num)
    (lowerGradient_root hd hμ hsc) (lowerGradient_root_unique hd hμ hsc)
  intro x
  exact BilevelCurvature.coercive_isInvertible _ hμ
    (lowerHessian_coercive hg hsc x (lowerSolution I x))

lemma hyperObjective_contDiff {p : Params} {I : Instance p}
    (hf : ContDiff ℝ 2 I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) : ContDiff ℝ 2 (hyperObjective I) := by
  exact hf.comp (contDiff_id.prodMk (lowerSolution_contDiff hg hμ hsc))


lemma lowerHessian_eq {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (z : p.X × p.Y) : lowerHessian I z =
      (fderiv ℝ (lowerGradient I) z).comp (.inr ℝ p.X p.Y) := by
  rw [(lowerGradient_hasFDerivAt hg z).fderiv]
  rfl

lemma lowerRestriction_inner {p : Params} (A : (p.X × p.Y) →L[ℝ] ℝ) (v : p.Y) :
    ⟪lowerRestriction p A, v⟫ = A (0, v) := by
  exact DFunLike.congr_fun ((InnerProductSpace.toDual ℝ p.Y).apply_symm_apply
    (A.comp (.inr ℝ p.X p.Y))) v

lemma lowerHessian_inner {p : Params} (I : Instance p) (z : p.X × p.Y) (u v : p.Y) :
    ⟪lowerHessian I z u, v⟫ = fderiv ℝ (fderiv ℝ I.g) z (0, u) (0, v) :=
  lowerRestriction_inner _ v


lemma lowerGradient_second_inner {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (z a b : p.X × p.Y) (v : p.Y) :
    ⟪fderiv ℝ (fderiv ℝ (lowerGradient I)) z a b, v⟫ =
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z (0, v) a b := by
  rw [lowerGradient_second_derivative hg]
  simp only [ContinuousLinearMap.comp_apply, lowerJacobianMap_apply, lowerRestriction_inner]
  rw [BilevelImplicitEstimates.third_swap_last hg z,
    BilevelImplicitEstimates.third_swap_first hg z]

lemma lowerHessian_derivative_apply {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (z w : p.X × p.Y) (v : p.Y) :
    fderiv ℝ (lowerHessian I) z w v = fderiv ℝ (fderiv ℝ (lowerGradient I)) z w (0, v) := by
  rw [(lowerHessian_hasFDerivAt hg z).fderiv, lowerGradient_second_derivative hg]
  rfl

lemma lowerHessian_symmetric {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (z : p.X × p.Y) (u v : p.Y) : ⟪lowerHessian I z u, v⟫ = ⟪lowerHessian I z v, u⟫ := by
  simp only [lowerHessian_inner]
  exact hg.contDiffAt.isSymmSndFDerivAt (by norm_num) |>.eq (0, u) (0, v)

lemma lowerHessian_positive {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (hμ : 0 ≤ p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (z : p.X × p.Y) (v : p.Y) :
    0 ≤ ⟪lowerHessian I z v, v⟫ := by
  rw [lowerHessian_eq hg]
  exact (mul_nonneg hμ (sq_nonneg ‖v‖)).trans (lowerHessian_coercive hg hsc z.1 z.2 v)

lemma lowerHessian_derivative_lipschitz {p : Params} {I : Instance p}
    (hlip : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    (z w : p.X × p.Y) :
    ‖(lowerHessianMap p).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z) -
      (lowerHessianMap p).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w)‖ ≤ p.L * ‖z - w‖ := by
  rw [← ContinuousLinearMap.comp_sub]
  calc
    _ ≤ ‖lowerHessianMap p‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
        fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (p.L * ‖z - w‖) := mul_le_mul (lowerHessianMap_norm p) (hlip z w)
      (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma lower_third_mixed {p : Params} {I : Instance p} (hg : ContDiff ℝ 3 I.g)
    (hL : 0 < p.L) (hμ : 0 ≤ p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hlip : ∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖)
    (z w : p.X × p.Y) (a b : p.Y) :
    |fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z w (0, a) (0, b)| ≤
      Real.sqrt (2 * p.L) * ‖w‖ *
        (‖a‖ * Real.sqrt ⟪lowerHessian I z b, b⟫ +
          ‖b‖ * Real.sqrt ⟪lowerHessian I z a, a⟫) := by
  have h := BilevelCurvature.positive_field_derivative_mixed hL
    (lowerHessian_hasFDerivAt hg) (lowerHessian_derivative_lipschitz hlip)
    (lowerHessian_positive hg hμ hsc) (lowerHessian_symmetric hg) z w a b
  simpa only [ContinuousLinearMap.comp_apply, lowerHessianMap_apply, lowerRestriction_inner] using h


lemma lowerSolution_derivative_bounds {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hlip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (x a : p.X) :
    p.μ * ‖fderiv ℝ (lowerSolution I) x a‖ ≤ p.L * ‖a‖ ∧
      p.μ * ⟪lowerHessian I (x, lowerSolution I x) (fderiv ℝ (lowerSolution I) x a),
        fderiv ℝ (lowerSolution I) x a⟫ ≤ p.L ^ 2 * ‖a‖ ^ 2 := by
  let J := fderiv ℝ (lowerGradient I) (x, lowerSolution I x)
  let v := fderiv ℝ (lowerSolution I) x a
  have hfirst := BilevelImplicit.root_first_equation
    ((lowerGradient_contDiff hg).differentiable (by norm_num))
    ((lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num))
    (lowerGradient_root (hg.differentiable (by norm_num)) hμ hsc) x a
  have he : lowerHessian I (x, lowerSolution I x) v = -J (a, 0) := by
    rw [lowerHessian_eq hg]
    have hpair : (a, v) = (a, 0) + (0, v) := by simp
    change J (a, v) = 0 at hfirst
    rw [hpair, map_add] at hfirst
    change J (0, v) = -J (a, 0)
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hfirst)
  have hJ : ‖J‖ ≤ p.L := norm_fderiv_le_of_lip' ℝ hL
    (Filter.Eventually.of_forall (fun z => lowerGradient_lipschitz hlip z _))
  have hb : ‖-J (a, 0)‖ ≤ p.L * ‖a‖ := by
    rw [norm_neg]
    calc
      _ ≤ ‖J‖ * ‖(a, (0 : p.Y))‖ := J.le_opNorm _
      _ ≤ p.L * ‖a‖ := by simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg (a, (0 : p.Y)))
  have hc : ∀ u, p.μ * ‖u‖ ^ 2 ≤ ⟪lowerHessian I (x, lowerSolution I x) u, u⟫ := by
    intro u
    rw [lowerHessian_eq hg]
    exact lowerHessian_coercive hg hsc x (lowerSolution I x) u
  refine ⟨(BilevelCurvature.coercive_solution_norm _ hc he).trans hb, ?_⟩
  have hh := BilevelCurvature.coercive_solution_energy _ hμ hc he
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow] at hb2
  exact hh.trans hb2



lemma lowerSolution_lipschitz {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hlip : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (x y : p.X) : ‖lowerSolution I x - lowerSolution I y‖ ≤ (p.L / p.μ) * ‖x - y‖ := by
  have hd := (lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num)
  have hb : ∀ x, ‖fderiv ℝ (lowerSolution I) x‖ ≤ p.L / p.μ := by
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hL hμ.le)
    intro a
    have hh := (lowerSolution_derivative_bounds hg hμ hL hsc hlip x a).1
    apply (mul_le_mul_iff_right₀ hμ).mp
    calc
      _ ≤ p.L * ‖a‖ := by nlinarith
      _ = p.μ * (p.L / p.μ * ‖a‖) := by field_simp
  have hh := lipschitzWith_of_nnnorm_fderiv_le (C := ⟨p.L / p.μ, div_nonneg hL hμ.le⟩)
    hd (fun x => show ‖fderiv ℝ (lowerSolution I) x‖₊ ≤ ⟨p.L / p.μ, div_nonneg hL hμ.le⟩ from hb x)
  exact hh.norm_sub_le x y

lemma lowerSolution_second_identity {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a b : p.X) :
    lowerHessian I (x, lowerSolution I x) (fderiv ℝ (fderiv ℝ (lowerSolution I)) x b a) =
      -lowerRestriction p (fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) (x, lowerSolution I x)
        (b, fderiv ℝ (lowerSolution I) x b) (a, fderiv ℝ (lowerSolution I) x a)) := by
  have h := BilevelImplicit.root_second_equation (lowerGradient_contDiff hg)
    (lowerSolution_contDiff hg hμ hsc)
    (lowerGradient_root (hg.differentiable (by norm_num)) hμ hsc) x a b
  rw [lowerGradient_second_derivative hg] at h
  rw [lowerHessian_eq hg]
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm, lowerJacobianMap_apply] using h)

lemma lowerSolution_second_energy_identity {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a b : p.X) :
    let z := fderiv ℝ (fderiv ℝ (lowerSolution I)) x b a
    ⟪lowerHessian I (x, lowerSolution I x) z, z⟫ =
      -fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) (x, lowerSolution I x) (0, z)
        (b, fderiv ℝ (lowerSolution I) x b) (a, fderiv ℝ (lowerSolution I) x a) := by
  dsimp only
  rw [lowerSolution_second_identity hg hμ hsc, inner_neg_left, lowerRestriction_inner]
  rw [BilevelImplicitEstimates.third_swap_last hg (x, lowerSolution I x),
    BilevelImplicitEstimates.third_swap_first hg (x, lowerSolution I x)]

end LongTails.Proofs.BilevelGeometry
