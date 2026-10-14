import LongTails.Setups.HessianLipschitzTemporalDiscrepancy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic
import LongTails.Proofs.QuadraticTemporalEnergy

open scoped RealInnerProductSpace

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma gradient_contDiff_one {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) := by
  have hh : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp hf).2.2
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp hh

lemma hessian_symmetric {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u : E) :
    (fderiv ℝ (gradient f) u).toLinearMap.IsSymmetric := by
  have hg := ((gradient_contDiff_one hf).differentiable (by norm_num) u).hasFDerivAt
  have hh := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp u hg
  have he : fderiv ℝ (fderiv ℝ f) u =
      (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
        (fderiv ℝ (gradient f) u) := by
    have he' := hh.fderiv
    change fderiv ℝ ((InnerProductSpace.toDual ℝ E) ∘ gradient f) u = _ at he'
    rw [toDual_comp_gradient] at he'
    exact he'
  intro x y
  have hfu : ContDiffAt ℝ 2 f u := hf.contDiffAt
  have hs := (hfu.isSymmSndFDerivAt (by norm_num)).eq x y
  rw [he] at hs
  change ⟪fderiv ℝ (gradient f) u x, y⟫ = ⟪fderiv ℝ (gradient f) u y, x⟫ at hs
  exact hs.trans (real_inner_comm _ _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma gradient_strong_monotonicity {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) (x y : E) :
    μ * ‖y - x‖ ^ 2 ≤ ⟪g y - g x, y - x⟫ := by
  have hxy := hs x y
  have hyx := hs y x
  rw [norm_sub_rev x y, show x - y = -(y - x) by abel, inner_neg_right] at hyx
  rw [inner_sub_left]
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma hessian_lower_bound {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hg : Differentiable ℝ g)
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) (u v : E) :
    μ * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ g u v, v⟫ := by
  let F := fun t : ℝ => ⟪g (u + t • v), v⟫ - μ * t * ‖v‖ ^ 2
  have hmono : Monotone F := by
    intro a b hab
    by_cases heq : a = b
    · subst b; rfl
    have hp : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
    have hh := gradient_strong_monotonicity hs (u + a • v) (u + b • v)
    have hd : u + b • v - (u + a • v) = (b - a) • v := by module
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hp, mul_pow,
      inner_smul_right, inner_sub_left] at hh
    have hh' : μ * (b - a) * ‖v‖ ^ 2 ≤ ⟪g (u + b • v), v⟫ - ⟪g (u + a • v), v⟫ := by
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith only [hh]
    dsimp [F]
    linarith
  have hline : HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hgu : HasFDerivAt g (fderiv ℝ g u) (u + (0 : ℝ) • v) := by
    simpa using (hg u).hasFDerivAt
  have hd := hgu.comp_hasDerivAt 0 hline
  have hi := hd.inner ℝ (hasDerivAt_const (0 : ℝ) v)
  have hm := ((hasDerivAt_id (0 : ℝ)).const_mul μ).mul_const (‖v‖ ^ 2)
  have hF : HasDerivAt F (⟪fderiv ℝ g u v, v⟫ - μ * ‖v‖ ^ 2) 0 := by
    convert hi.sub hm using 1 <;> simp [F]
    rfl
  have hh := hF.nonneg_of_monotone hmono
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma gradient_linearization_bound {g : E → E} {M : ℝ}
    (hM : 0 ≤ M) (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M * ‖x - y‖) (u x : E) :
    ‖g x - g u - fderiv ℝ g u (x - u)‖ ≤ M * ‖x - u‖ ^ 2 := by
  let R := fun y => g y - fderiv ℝ g u (y - u)
  have hR (y : E) : HasFDerivAt R (fderiv ℝ g y - fderiv ℝ g u) y := by
    have hh := (fderiv ℝ g u).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const u)
    have hb := (hg y).hasFDerivAt.sub hh
    simp only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] at hb
    convert hb using 1
  have hb (y : E) (hy : y ∈ Metric.closedBall u ‖x - u‖) :
      ‖fderiv ℝ g y - fderiv ℝ g u‖ ≤ M * ‖x - u‖ := by
    exact (hH y u).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy) hM)
  have hh := (convex_closedBall u ‖x - u‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y _ => (hR y).hasFDerivWithinAt) hb
    (show u ∈ Metric.closedBall u ‖x - u‖ by simp)
    (show x ∈ Metric.closedBall u ‖x - u‖ by simp [dist_eq_norm])
  dsimp [R] at hh
  simp only [sub_self, map_zero, sub_zero] at hh
  have he : g x - fderiv ℝ g u (x - u) - g u =
      g x - g u - fderiv ℝ g u (x - u) := by abel
  rw [he] at hh
  simpa only [pow_two, mul_assoc] using hh

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma hessian_upper_bound {g : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (u v : E) :
    ⟪fderiv ℝ g u v, v⟫ ≤ L * ‖v‖ ^ 2 := by
  have hH : ‖fderiv ℝ g u‖ ≤ L :=
    norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun x => hlip x u))
  calc
    _ ≤ ‖fderiv ℝ g u v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (L * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      (((fderiv ℝ g u).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hH (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

lemma objective_linearization_bound {f : E → ℝ} {M : ℝ}
    (hf : ContDiff ℝ 2 f) (hM : 0 ≤ M)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (u x : E) (hu : gradient f u = 0) (A : E →L[ℝ] E)
    (hA : A.adjoint.comp A = fderiv ℝ (gradient f) u) :
    |f x - f u - ‖A (x - u)‖ ^ 2 / 2| ≤ M * ‖x - u‖ ^ 3 := by
  let R := fun y => f y - ‖A (y - u)‖ ^ 2 / 2
  let dR := fun y => InnerProductSpace.toDual ℝ E
    (gradient f y - fderiv ℝ (gradient f) u (y - u))
  have hR (y : E) : HasFDerivAt R (dR y) y := by
    have hh := ((hf.differentiable (by norm_num) y).hasGradientAt.hasFDerivAt).sub
      (TemporalDiscrepancy.factorized_quadratic_gradient A u y).hasFDerivAt
    convert hh using 1
    simp only [dR, map_sub, ← hA, ContinuousLinearMap.comp_apply]
  have hbound (y : E) (hy : y ∈ Metric.closedBall u ‖x - u‖) :
      ‖dR y‖ ≤ M * ‖x - u‖ ^ 2 := by
    have hh := gradient_linearization_bound hM
      ((gradient_contDiff_one hf).differentiable (by norm_num)) hH u y
    rw [hu, sub_zero] at hh
    have hy' : ‖y - u‖ ≤ ‖x - u‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    change ‖InnerProductSpace.toDual ℝ E _‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hy' 2) hM)
  have hh := (convex_closedBall u ‖x - u‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y _ => (hR y).hasFDerivWithinAt) hbound
    (show u ∈ Metric.closedBall u ‖x - u‖ by simp)
    (show x ∈ Metric.closedBall u ‖x - u‖ by simp [dist_eq_norm])
  simp only [R, sub_self, map_zero, norm_zero, zero_pow (by omega : 2 ≠ 0),
    zero_div, sub_zero, Real.norm_eq_abs] at hh
  convert hh using 1
  · congr 1
    ring
  · ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma local_objective_upper {f : E → ℝ} {μ M : ℝ}
    (A : E →L[ℝ] E) (u x : E)
    (hlower : μ * ‖x - u‖ ^ 2 ≤ ‖A (x - u)‖ ^ 2)
    (hrem : |f x - f u - ‖A (x - u)‖ ^ 2 / 2| ≤ M * ‖x - u‖ ^ 3)
    (hlocal : 2 * M * ‖x - u‖ ≤ μ) :
    f x - f u ≤ ‖A (x - u)‖ ^ 2 := by
  have hh := (abs_le.mp hrem).2
  have hm := mul_le_mul_of_nonneg_right hlocal (sq_nonneg ‖x - u‖)
  nlinarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma local_quadratic_upper {f : E → ℝ} {μ M : ℝ}
    (A : E →L[ℝ] E) (u x : E)
    (hlower : μ / 2 * ‖x - u‖ ^ 2 ≤ f x - f u)
    (hrem : |f x - f u - ‖A (x - u)‖ ^ 2 / 2| ≤ M * ‖x - u‖ ^ 3)
    (hlocal : 6 * M * ‖x - u‖ ≤ μ) :
    ‖A (x - u)‖ ^ 2 ≤ (8 / 3 : ℝ) * (f x - f u) := by
  have hh := (abs_le.mp hrem).1
  have hm := mul_le_mul_of_nonneg_right hlocal (sq_nonneg ‖x - u‖)
  nlinarith

end OracleTemplate.NonlinearTemporalDiscrepancy
