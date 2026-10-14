import LongTails.Proofs.MarkovQuadraticCovariance
import LongTails.Proofs.OperatorGeneratingSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 600000 in
lemma norm_dualConjugation_sub_one_le (W : V →L[ℂ] V) (hW : ‖W‖ ≤ 1) :
    ‖dualConjugation W - 1‖ ≤ 2 * ‖W - 1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  have he : (dualConjugation W - 1) X = (W.adjoint - 1) * X * W + X * (W - 1) := by
    simp only [sub_apply, dualConjugation_apply, one_apply_eq_self]
    noncomm_ring
  have had : ‖W.adjoint - 1‖ = ‖W - 1‖ := by
    have ha : (W - 1).adjoint = W.adjoint - 1 := by
      rw [map_sub, ContinuousLinearMap.adjoint_one]
    rw [← ha]
    exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (W - 1)
  rw [he]
  calc
    _ ≤ ‖W.adjoint - 1‖ * ‖X‖ * ‖W‖ + ‖X‖ * ‖W - 1‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · exact norm_mul_le _ _
    _ ≤ ‖W - 1‖ * ‖X‖ * 1 + ‖X‖ * ‖W - 1‖ := by rw [had]; gcongr
    _ = _ := by ring

section Transfer

variable {B G : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma transferCovariance_first_difference (D Q : G →L[ℂ] G) (M : G →L[ℂ] B)
    (J : B →L[ℂ] G) (hQJ : Q.comp J = J) (n : ℕ) :
    transferCovariance M (D * Q) J (n + 1) - transferCovariance M (D * Q) J n =
      M.comp (((D * Q) ^ n).comp ((D - 1).comp J)) := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_sub]
  have ht := transferCovariance_tail D Q J hQJ n
  rw [ht]
  simp only [transferCovariance, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

lemma norm_transferCovariance_first_difference_le (D Q : G →L[ℂ] G) (M : G →L[ℂ] B)
    (J : B →L[ℂ] G) (hQJ : Q.comp J = J)
    (hD : ‖D‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hM : ‖M‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    {b : ℝ} (hb : 0 ≤ b) (hsmall : ‖D - 1‖ ≤ b) (n : ℕ) :
    ‖transferCovariance M (D * Q) J (n + 1) - transferCovariance M (D * Q) J n‖ ≤ b := by
  rw [transferCovariance_first_difference D Q M J hQJ]
  have hDQ : ‖D * Q‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg D, norm_nonneg Q])
  have hp := norm_power_contraction (D * Q) hDQ n
  calc
    _ ≤ ‖M‖ * (‖(D * Q) ^ n‖ * (‖D - 1‖ * ‖J‖)) := by
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * (b * 1)) := by gcongr
    _ = b := by ring

end Transfer

section Geometric

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
lemma norm_censoredMean_sub_initial_le (f : ℕ → B) {b q : ℝ} (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hq1 : q < 1) (hd : ∀ k, ‖f (k + 1) - f k‖ ≤ b) (n : ℕ) :
    ‖censoredMean q n f - f 0‖ ≤ b / (1 - q) := by
  rw [censoredMean_telescope, add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖q ^ k • (f (k + 1) - f k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, q ^ k * b := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)]
      exact mul_le_mul_of_nonneg_left (hd k) (pow_nonneg hq k)
    _ = (∑ k ∈ Finset.range n, q ^ k) * b := (Finset.sum_mul _ _ _).symm
    _ ≤ b / (1 - q) := by
      apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
      calc
        _ = ((∑ k ∈ Finset.range n, q ^ k) * (1 - q)) * b := by ring
        _ = (1 - q ^ n) * b := by rw [geom_sum_mul_neg]
        _ ≤ b := by nlinarith [pow_nonneg hq n]

lemma norm_geometricMean_sub_initial_le (f : ℕ → B) {b q C : ℝ} (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hq1 : q < 1) (hf : ∀ k, ‖f k‖ ≤ C)
    (hd : ∀ k, ‖f (k + 1) - f k‖ ≤ b) :
    ‖geometricMean q f - f 0‖ ≤ b / (1 - q) := by
  apply le_of_tendsto ((tendsto_censoredMean hq hq1 f hf).sub_const (f 0)).norm
  exact Filter.Eventually.of_forall (norm_censoredMean_sub_initial_le f hb hq hq1 hd)

end Geometric

end OracleTemplate.MarkovProduct

namespace OracleTemplate.MarkovQuadratic

open MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma norm_quadratic_operator_le (H : E →L[ℝ] E) {L : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) : ‖H‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound _ hL.le
  intro x
  have hc := quadratic_cocoercivity H hL hs hp hb x
  have hu := mul_le_mul_of_nonneg_left (hb x) hL.le
  have hh : ‖H x‖ ^ 2 ≤ (L * ‖x‖) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))).mp hh

lemma norm_liftedStep_sub_one_le (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) :
    ‖liftedStep η H - 1‖ ≤ η * L := by
  have he : liftedStep η H - 1 = -((η : ℂ) • Complexified.lift H) := by
    rw [liftedStep, Complexified.lift_gradient_step]
    change (1 - (η : ℂ) • Complexified.lift H) - 1 = _
    abel
  rw [he, norm_neg, norm_smul]
  have hn : ‖(η : ℂ)‖ = η := by simp [abs_of_nonneg hη]
  rw [hn]
  exact mul_le_mul_of_nonneg_left ((Complexified.norm_lift_le H).trans
    (norm_quadratic_operator_le H hL hs hp hb)) hη

lemma norm_liftedStep_covariance_sub_one_le (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) :
    ‖dualConjugation (liftedStep η H) - 1‖ ≤ 2 * (η * L) :=
  (norm_dualConjugation_sub_one_le _ (norm_liftedStep_le_one H hL hs hp hb hη hηL)).trans
    (mul_le_mul_of_nonneg_left (norm_liftedStep_sub_one_le H hL hs hp hb hη) (by norm_num))

lemma quadratic_stateAction_bounds {S : Type*} [Fintype S] (H : S → E →L[ℝ] E)
    {L η : ℝ} (hL : 0 < L) (hs : ∀ i, (H i).adjoint = H i)
    (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫) (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2)
    (hη : 0 ≤ η) (hηL : η * L ≤ 2) :
    ‖stateAction (fun i => dualConjugation (liftedStep η (H i)))‖ ≤ 1 ∧
      ‖stateAction (fun i => dualConjugation (liftedStep η (H i))) - 1‖ ≤ 2 * (η * L) := by
  constructor
  · apply norm_stateAction_le _ zero_le_one
    intro i
    have hn := norm_liftedStep_le_one (H i) hL (hs i) (hp i) (hb i) hη hηL
    exact (norm_dualConjugation_le _).trans (by nlinarith [norm_nonneg (liftedStep η (H i))])
  · apply norm_stateAction_sub_one_le _ (by positivity)
    intro i
    exact norm_liftedStep_covariance_sub_one_le (H i) hL (hs i) (hp i) (hb i) hη hηL

open MeasureTheory ProbabilityTheory

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

set_option synthInstance.maxHeartbeats 100000 in
lemma markovCovariance_zero (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) (μ : ProbabilityMeasure S) : markovCovariance η H κ μ 0 = 1 := by
  simp only [markovCovariance, transferCovariance, pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  exact stateAverage_constant _ (finite_probability_weights _).2

lemma norm_markovCovariance_first_difference (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) {L : ℝ} (hL : 0 < L)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) (n : ℕ) :
    ‖markovCovariance η H κ μ (n + 1) - markovCovariance η H κ μ n‖ ≤ 2 * (η * L) := by
  obtain ⟨hD, hd⟩ := quadratic_stateAction_bounds H hL hs hp hb hη hηL
  apply norm_transferCovariance_first_difference_le
  · exact stateMix_constant _ (fun i => (finite_probability_weights (κ i)).2)
  · exact hD
  · exact norm_stateMix_le _ (fun i => (finite_probability_weights (κ i)).1)
      (fun i => (finite_probability_weights (κ i)).2)
  · exact norm_stateAverage_le _ (finite_probability_weights _).1 (finite_probability_weights _).2
  · exact norm_stateConstant_le
  · positivity
  · exact hd

lemma norm_markovCovariance_second_difference (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (π : ProbabilityMeasure S)
    (hstat : κ ∘ₘ (π : Measure S) = π) {L : ℝ} (hL : 0 < L)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) (n : ℕ) :
    ‖markovCovariance η H κ π (n + 2) - markovCovariance η H κ π (n + 1) -
      markovCovariance η H κ π (n + 1) + markovCovariance η H κ π n‖ ≤ 4 * (η * L) ^ 2 := by
  obtain ⟨hD, hd⟩ := quadratic_stateAction_bounds H hL hs hp hb hη hηL
  have h := norm_transferCovariance_endpoint_le
    (stateAction (fun i => dualConjugation (liftedStep η (H i))))
    (stateMix (fun i j => (κ i).real {j}))
    (stateAverage (fun i => (π : Measure S).real {i})) stateConstant
    (stateMix_constant _ (fun i => (finite_probability_weights (κ i)).2))
    (stateAverage_mix _ _ (finite_stationary_weights κ π hstat)) hD
    (norm_stateMix_le _ (fun i => (finite_probability_weights (κ i)).1)
      (fun i => (finite_probability_weights (κ i)).2))
    (norm_stateAverage_le _ (finite_probability_weights _).1 (finite_probability_weights _).2)
    norm_stateConstant_le (by positivity : 0 ≤ 2 * (η * L)) hd n
  have hc : (2 * (η * L)) ^ 2 = 4 * (η * L) ^ 2 := by ring
  rw [hc] at h
  simpa only [markovCovariance] using! h

end OracleTemplate.MarkovQuadratic
