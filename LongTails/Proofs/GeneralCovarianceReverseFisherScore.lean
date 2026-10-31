import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherScore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def precision (A : E ≃L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) ∘L (A.symm : E →L[ℝ] E)

lemma inner_precision (A : E ≃L[ℝ] E) (u v : E) :
    ⟪u, precision A v⟫ = ⟪A.symm u, A.symm v⟫ := by
  simp [precision, ContinuousLinearMap.adjoint_inner_right]

lemma precision_inner (A : E ≃L[ℝ] E) (u v : E) :
    ⟪precision A u, v⟫ = ⟪A.symm u, A.symm v⟫ := by
  rw [real_inner_comm, inner_precision, real_inner_comm]

noncomputable def weight (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) (i : Fin k) : ℝ :=
  Real.exp (-‖A.symm (x - c i)‖ ^ 2 / 2)

noncomputable def total (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) : ℝ :=
  ∑ i, weight A c x i

noncomputable def resp (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) (i : Fin k) : ℝ :=
  weight A c x i / total A c x

omit [CompleteSpace E] in
lemma weight_pos (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) (i : Fin k) :
    0 < weight A c x i := Real.exp_pos _

omit [CompleteSpace E] in
lemma total_pos (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    0 < total A c x :=
  Finset.sum_pos (fun i _ => weight_pos A c x i) Finset.univ_nonempty

omit [CompleteSpace E] in
lemma resp_nonneg (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) (i : Fin k) :
    0 ≤ resp A c x i :=
  div_nonneg (weight_pos A c x i).le (total_pos A c x).le

omit [CompleteSpace E] in
lemma sum_resp (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    ∑ i, resp A c x i = 1 := by
  unfold resp
  rw [← Finset.sum_div]
  exact div_self (total_pos A c x).ne'

lemma hasFDerivAt_exponent (A : E ≃L[ℝ] E) (c x : E) :
    HasFDerivAt (fun y => -‖A.symm (y - c)‖ ^ 2 / 2)
      (innerSL ℝ (precision A (c - x))) x := by
  have h1 : HasFDerivAt (fun y => A.symm (y - c)) (A.symm : E →L[ℝ] E) x := by
    have := ((A.symm : E →L[ℝ] E).hasFDerivAt (x := x)).sub_const (A.symm c)
    convert this using 1
    ext y
    simp
  have h2 := (h1.norm_sq).const_mul (-1 / 2 : ℝ)
  convert h2 using 1
  · ext y
    ring
  · ext v
    simp only [map_sub, sub_apply, innerSL_apply_apply, smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, precision_inner]
    ring

lemma hasGradientAt_logSumExp (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    HasGradientAt (fun y => Real.log (∑ i, Real.exp (-‖A.symm (y - c i)‖ ^ 2 / 2)))
      (∑ i, resp A c x i • precision A (c i - x)) x := by
  have hs : HasFDerivAt (fun y => ∑ i, Real.exp (-‖A.symm (y - c i)‖ ^ 2 / 2))
      (∑ i, weight A c x i • innerSL ℝ (precision A (c i - x))) x :=
    HasFDerivAt.fun_sum (fun i _ => (hasFDerivAt_exponent A (c i) x).exp)
  have hl := hs.log (total_pos A c x).ne'
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hl using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, sum_inner, inner_smul_left, conj_trivial,
    smul_apply, FunLike.coe_sum, Finset.sum_apply, innerSL_apply_apply, smul_eq_mul,
    Finset.mul_sum, resp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold total weight
  ring

lemma gradient_logSumExp (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    gradient (fun y => Real.log (∑ i, Real.exp (-‖A.symm (y - c i)‖ ^ 2 / 2))) x =
      ∑ i, resp A c x i • precision A (c i - x) :=
  (hasGradientAt_logSumExp A c x).gradient

noncomputable def posteriorMean (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) : E :=
  ∑ i, resp A c x i • c i

lemma score_difference (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (t x : E) :
    gradient (fun y => Real.log (∑ i, Real.exp (-‖A.symm (y - c i)‖ ^ 2 / 2))) x -
      gradient (fun y => Real.log (∑ _i : Fin 1, Real.exp (-‖A.symm (y - t)‖ ^ 2 / 2))) x =
      precision A (posteriorMean A c x - t) := by
  rw [gradient_logSumExp A c x,
    gradient_logSumExp A (fun _ : Fin 1 => t) x]
  have h1 := sum_resp A (fun _ : Fin 1 => t) x
  simp only [Finset.univ_unique, Finset.sum_singleton] at h1 ⊢
  rw [h1, one_smul, posteriorMean, map_sub (precision A) _ t, map_sum]
  simp_rw [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    sum_resp A c x, one_smul]
  abel

end LongTails.Proofs.GeneralCovarianceReverseFisherScore
