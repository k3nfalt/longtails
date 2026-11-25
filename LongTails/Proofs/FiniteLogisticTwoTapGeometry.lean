import LongTails.Setups.FiniteLogisticTwoTap
import LongTails.Proofs.FiniteScaleConvolutionalSgdGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)

namespace LongTails.Proofs.FiniteLogisticTwoTapGeometry

lemma matrix_symmetric {d : ℕ} (b : Features d) (x h : Weights d) :
    ⟪sampleMatrix b h, x⟫ = ⟪sampleMatrix b x, h⟫ := by
  simp only [sampleMatrix, add_apply, inner_add_left,
    InnerProductSpace.rankOne_apply, real_inner_smul_left]
  ring

lemma first_layer_score {d : ℕ} (b : Features d) (x : Weights d) :
    (answer b x).margin =
      x (.inl 0) * ⟪liftReadout b, x⟫ + x (.inl 1) * ⟪liftReadout (shift b), x⟫ := by
  simp only [answer, sampleMatrix, add_apply, inner_add_left,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, EuclideanSpace.inner_single_left,
    map_one, one_mul]
  ring

lemma margin_derivative {d : ℕ} (b : Features d) (x : Weights d) :
    HasFDerivAt (fun y => (answer b y).margin) (innerSL ℝ (sampleMatrix b x)) x := by
  have hh := ((sampleMatrix b).hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)
  unfold answer
  simp only [div_eq_mul_inv]
  apply (hh.mul_const (2 : ℝ)⁻¹).congr_fderiv
  ext h
  simp [fderivInnerCLM_apply, matrix_symmetric b h x]
  ring

lemma sample_derivative {d : ℕ} (b : Features d) (x : Weights d) :
    HasFDerivAt (fun y => Real.log (1 + Real.exp (-(answer b y).margin)))
      ((-Real.sigmoid (-(answer b x).margin)) • innerSL ℝ (sampleMatrix b x)) x := by
  have h := (FiniteScaleConvolutionalSgdGeometry.logistic_value_derivative
    (answer b x).margin).comp_hasFDerivAt x (margin_derivative b x)
  simpa [SoftQuadraticDynamics.weight, Real.sigmoid, one_div, Function.comp_def] using h

lemma loss_gradient {d : ℕ} (μ : ℝ) (i : Fin d) (x : Weights d) :
    let a := answer (signedInput μ i false) x
    let b := answer (signedInput μ i true) x
    HasGradientAt (loss μ i) ((-1 / 2 : ℝ) •
      (Real.sigmoid (-a.margin) • a.direction + Real.sigmoid (-b.margin) • b.direction)) x := by
  dsimp only
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold loss
  simp only [div_eq_mul_inv]
  apply (((sample_derivative (signedInput μ i false) x).add
    (sample_derivative (signedInput μ i true) x)).mul_const (2 : ℝ)⁻¹).congr_fderiv
  ext v
  simp [answer]

end LongTails.Proofs.FiniteLogisticTwoTapGeometry
