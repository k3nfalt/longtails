import LongTails.Proofs.SoftCutPredictableBatches
import LongTails.Proofs.SubGaussianNetProbability

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

noncomputable section

namespace LongTails.Proofs.SoftCutBatchConcentration

open LongTails.Setups.CovarianceBoundedConvex
open SoftCutPredictableBatches
open SubGaussianNetProbability

def extendCoefficients {T : ℕ} (a : EuclideanSpace ℝ (Fin T)) (i : ℕ) : ℝ :=
  if hi : i < T then a ⟨i, hi⟩ else 0

lemma extendCoefficients_square_sum {T : ℕ} (a : EuclideanSpace ℝ (Fin T)) :
    ∑ i ∈ Finset.range T, extendCoefficients a i ^ 2 = ‖a‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range, EuclideanSpace.real_norm_sq_eq]
  simp [extendCoefficients]

lemma batchError_eq_estimate_error (q : Params) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (t : ℕ) (ξ : ℕ → q.Ω) :
    batchError q α η b g v t ξ =
      LongTails.Algorithms.CovarianceSoftCut.batchMean q b t
        (CovarianceSoftCutProcess.sampleReplies q α η b g ξ) -
      v (CovarianceSoftCutProcess.samplePoint q α η b g t ξ) := by
  have hdiv (i : Fin b) : (t*b+i.val)/b = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt i.isLt]
    simp
  simp only [LongTails.Algorithms.CovarianceSoftCut.batchMean,
    CovarianceSoftCutProcess.sampleReplies, hdiv]
  rw [← one_div, OracleTemplate.RobustGradient.finite_mean_centered
    (v (CovarianceSoftCutProcess.samplePoint q α η b g t ξ)) b hb (fun i => ξ (t*b+i))]
  unfold batchError
  rw [one_div]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j =>
    g (CovarianceSoftCutProcess.samplePoint q α η b g t ξ) (ξ (t*b+j)) -
      v (CovarianceSoftCutProcess.samplePoint q α η b g t ξ)) b).symm

lemma batch_matrix_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (z : q.Ω) (variance : ℝ) (hvariance : 0 ≤ variance)
    (hmgf : ∀ x u t, Integrable (fun w => Real.exp (t * ⟪g x w - v x, u⟫)) p ∧
      (∫ w, Real.exp (t * ⟪g x w - v x, u⟫) ∂p) ≤
        Real.exp (variance * ‖u‖ ^ 2 * t ^ 2 / 2))
    (T : ℕ) (a : EuclideanSpace ℝ (Fin T)) (u : Space q)
    (ha : ‖a‖ ≤ 2) (hu : ‖u‖ ≤ 2) :
    HasSubgaussianMGF (fun ω =>
      ⟪columnOperator (fun i : Fin T => batchError q α η b g v i (fun j => ξ j ω)) a, u⟫)
      ⟨16*variance/b, by positivity⟩ P := by
  have hcoeff : ∑ i ∈ Finset.range T, extendCoefficients a i ^ 2 ≤ 4 := by
    rw [extendCoefficients_square_sum]
    nlinarith [norm_nonneg a]
  have hh := batch_direction_mgf q hR α η b hb g v hg hv p P ξ hξ hind hlaw z
    (fun _ => u) measurable_const (extendCoefficients a) variance 2 4
    hvariance (by norm_num) (by norm_num) (fun _ _ => hu) hmgf T hcoeff
  have he (ω : Ξ) :
      (∑ t ∈ Finset.range T, extendCoefficients a t *
        ⟪batchError q α η b g v t (fun j => ξ j ω), u⟫) =
      ⟪columnOperator (fun i : Fin T => batchError q α η b g v i (fun j => ξ j ω)) a, u⟫ := by
    rw [← Fin.sum_univ_eq_sum_range, columnOperator_apply, sum_inner]
    simp [extendCoefficients, real_inner_smul_left]
  simp_rw [he] at hh
  simpa only [show variance*2^2*(4/(b : ℝ)) = 16*variance/b by ring] using hh

lemma batch_intercept_mgf {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (hR : 0 < q.R) (α η : ℝ) (b : ℕ) (hb : 0 < b)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, P.map (ξ i) = p)
    (z : q.Ω) (variance : ℝ) (hvariance : 0 ≤ variance)
    (hmgf : ∀ x u t, Integrable (fun w => Real.exp (t * ⟪g x w - v x, u⟫)) p ∧
      (∫ w, Real.exp (t * ⟪g x w - v x, u⟫) ∂p) ≤
        Real.exp (variance * ‖u‖ ^ 2 * t ^ 2 / 2))
    (T : ℕ) (a : EuclideanSpace ℝ (Fin T)) (ha : ‖a‖ ≤ 2) :
    HasSubgaussianMGF (fun ω =>
      ⟪(WithLp.toLp 2 (fun i : Fin T =>
        ⟪batchError q α η b g v i (fun j => ξ j ω),
          CovarianceSoftCutProcess.samplePoint q α η b g i (fun j => ξ j ω)⟫) :
            EuclideanSpace ℝ (Fin T)), a⟫)
      ⟨16*variance*q.R^2/b, by positivity⟩ P := by
  have hcoeff : ∑ i ∈ Finset.range T, extendCoefficients a i ^ 2 ≤ 4 := by
    rw [extendCoefficients_square_sum]
    nlinarith [norm_nonneg a]
  have hh := batch_direction_mgf q hR α η b hb g v hg hv p P ξ hξ hind hlaw z
    id measurable_id (extendCoefficients a) variance (2*q.R) 4
    hvariance (by positivity) (by norm_num) (fun _ hx => hx) hmgf T hcoeff
  have he (ω : Ξ) :
      (∑ t ∈ Finset.range T, extendCoefficients a t *
        ⟪batchError q α η b g v t (fun j => ξ j ω),
          CovarianceSoftCutProcess.samplePoint q α η b g t (fun j => ξ j ω)⟫) =
      ⟪(WithLp.toLp 2 (fun i : Fin T =>
        ⟪batchError q α η b g v i (fun j => ξ j ω),
          CovarianceSoftCutProcess.samplePoint q α η b g i (fun j => ξ j ω)⟫) :
            EuclideanSpace ℝ (Fin T)), a⟫ := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [extendCoefficients, PiLp.inner_apply]
  simp only [id_eq] at hh
  simp_rw [he] at hh
  simpa only [show variance*(2*q.R)^2*(4/(b : ℝ)) = 16*variance*q.R^2/b by ring] using hh

end LongTails.Proofs.SoftCutBatchConcentration
