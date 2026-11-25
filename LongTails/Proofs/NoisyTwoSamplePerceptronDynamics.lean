import LongTails.Algorithms.NoisyTwoSamplePerceptron
import LongTails.Proofs.FiniteLogisticTwoTapSpectrum

open MeasureTheory OracleTemplate ProbabilityTheory
open LongTails.Setups.FiniteLogisticTwoTap (Weights Reply signedInput answer sampleMatrix liftReadout)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Algorithms.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding (shift_ones)

namespace LongTails.Proofs.NoisyTwoSamplePerceptronDynamics

lemma algorithm_family (p : Params) {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    family p (algorithm p η σ) := by
  refine ⟨η, σ, fun k ω => ω k, id, hη, hσ, ⟨fun k => measurable_pi_apply k, ?_, ?_⟩,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  · exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · exact Measure.infinitePi_map_eval _

lemma slow_add {d : ℕ} (i : Fin d) (x y : Weights d) :
    slowProjection i (x + y) = slowProjection i x + slowProjection i y := by
  simp only [slowProjection, PiLp.add_apply]
  ring

lemma slow_smul {d : ℕ} (i : Fin d) (a : ℝ) (x : Weights d) :
    slowProjection i (a • x) = a * slowProjection i x := by
  simp only [slowProjection, PiLp.smul_apply, smul_eq_mul]
  ring

lemma slow_first {d : ℕ} (μ : ℝ) (i : Fin d) (x : Weights d) :
    slowProjection i (sampleMatrix (signedInput μ i false) x) = 0 := by
  simp only [signedInput, Bool.false_eq_true, ↓reduceIte, sampleMatrix, shift_ones]
  simp [InnerProductSpace.rankOne_apply, slowProjection,
    liftReadout, LongTails.Setups.TwoSampleQuadraticPerceptron.ones]

lemma slow_second {d : ℕ} (μ : ℝ) (i : Fin d) (hi : finRotate d i ≠ i) (x : Weights d) :
    slowProjection i (sampleMatrix (signedInput μ i true) x) = μ * slowProjection i x := by
  have hd : slowProjection i (sampleMatrix (EuclideanSpace.single i 1) x) = -slowProjection i x := by
    rw [defect_action]
    simp [slowProjection, -finRotate_apply, hi, Ne.symm hi]
    ring
  have h := congrArg (fun A : Weights d →L[ℝ] Weights d => slowProjection i (A x)) (sum_matrices μ i)
  simp only [add_apply, slow_add, slow_first, zero_add, smul_apply, slow_smul, hd] at h
  linarith

end LongTails.Proofs.NoisyTwoSamplePerceptronDynamics
