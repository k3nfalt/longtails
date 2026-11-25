import LongTails.Proofs.LogisticCloudModel
import LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudModel
open LongTails.Proofs.LogisticCloudExecution

namespace LongTails.Proofs.LogisticCloudGradient

variable {d : ℕ}

lemma symmetric (a b : Features d) (w x : Weights d) :
    ⟪action a b w,x⟫ = ⟪action a b x,w⟫ := by
  simp only [action,inner_pack,inner_add_left,real_inner_smul_left]
  ring

lemma margin_derivative (b : Features d) (x : Weights d) :
    HasFDerivAt (margin b) (innerSL ℝ (direction b x)) x := by
  let a := sumFeature b
  let c := diffFeature b
  let A : Weights d →ₗ[ℝ] Weights d :=
    { toFun := action a c, map_add' := action_add a c, map_smul' := action_smul a c }
  let B := A.toContinuousLinearMap
  have hh := (B.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)
  change HasFDerivAt (score a c) (innerSL ℝ (action a c x)) x
  simp_rw [funext (score_inner a c)]
  simp only [div_eq_mul_inv]
  apply (hh.mul_const (2:ℝ)⁻¹).congr_fderiv
  ext v
  simp [fderivInnerCLM_apply,B,A,symmetric a c v x]
  ring

lemma sample_derivative (b : Features d) (x : Weights d) :
    HasFDerivAt (fun w => Real.log (1+Real.exp (-margin b w)))
      ((-Real.sigmoid (-margin b x)) • innerSL ℝ (direction b x)) x := by
  have h := (FiniteScaleConvolutionalSgdGeometry.logistic_value_derivative
    (margin b x)).comp_hasFDerivAt x (margin_derivative b x)
  simpa [SoftQuadraticDynamics.weight,Real.sigmoid,one_div,Function.comp_def] using h

lemma loss_gradient {p : Params} (D : Data p) (w : Weights p.d) :
    HasGradientAt (loss D) ((-1/(2*p.n):ℝ) • ∑ i, increment D w i) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold loss
  simp only [div_eq_mul_inv]
  have h := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Index p)))
    (fun i _ => sample_derivative (input D i) w)
  apply (h.mul_const (2*(p.n:ℝ))⁻¹).congr_fderiv
  ext v
  simp [increment,answer,Finset.sum_neg_distrib]

end LongTails.Proofs.LogisticCloudGradient
