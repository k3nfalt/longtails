import LongTails.Proofs.MarkovTransferLaw
import LongTails.Proofs.MarkovQuadraticBlocks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovProduct

lemma sum_censorWeight_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (f : ℕ → V) :
    (∑ i : Fin n ⊕ Unit, censorWeight q n i • f (censorTime n i)) = censoredMean q n f := by
  rw [Fintype.sum_sum_type]
  simp only [censorWeight, censorTime, Fintype.sum_unique, censoredMean]
  rw [Finset.smul_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => ((1 - q) * q ^ k) • f (k + 1))]
  simp only [mul_smul]

lemma censoredMean_sum {Ω V : Type*} [Fintype Ω] [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (N : ℕ) (f : Ω → ℕ → V) :
    censoredMean q N (fun k => ∑ ω, f ω k) = ∑ ω, censoredMean q N (f ω) := by
  simp only [censoredMean, Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

lemma censoredMean_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q c : ℝ) (N : ℕ) (f : ℕ → V) :
    censoredMean q N (fun k => c • f k) = c • censoredMean q N f := by
  simp only [censoredMean, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring
  · rw [mul_comm]

lemma norm_censoredMean_le_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (f : ℕ → V) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖censoredMean q N f‖ ≤ 1 := by
  rw [← sum_censorWeight_smul]
  calc
    _ ≤ ∑ i, ‖censorWeight q N i • f (censorTime N i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, censorWeight q N i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (censorWeight_nonneg hq hq1 N i)]
      simpa using mul_le_mul_of_nonneg_left (hf (censorTime N i)) (censorWeight_nonneg hq hq1 N i)
    _ = 1 := censorWeight_total q N

lemma norm_geometricMean_le_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (f : ℕ → V) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖geometricMean q f‖ ≤ 1 :=
  le_of_tendsto (tendsto_censoredMean hq hq1 f hf).norm
    (Filter.Eventually.of_forall (fun N => norm_censoredMean_le_one hq hq1.le N f hf))

end OracleTemplate.MarkovProduct

namespace OracleTemplate.MarkovQuadratic

noncomputable section

open MarkovProduct

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance : NormedSpace ℂ (Complexified E →L[ℂ] Complexified E) :=
  ContinuousLinearMap.toNormedSpace
local instance : Module ℝ (Complexified E →L[ℂ] Complexified E) :=
  Module.complexToReal _
local instance : NormedSpace ℝ (Complexified E →L[ℂ] Complexified E) :=
  NormedSpace.complexToReal
local instance : NormedSpace ℂ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := ContinuousLinearMap.toNormedSpace
local instance : Module ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := Module.complexToReal _
local instance : NormedSpace ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := NormedSpace.complexToReal

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma pathOperator_liftedProduct (η : ℝ) (H : S → E →L[ℝ] E) (ξ : ℕ → S) (n : ℕ) :
    pathOperator (fun i => dualConjugation (liftedStep η (H i))) ξ n =
      dualConjugation (liftedProduct η (fun k => H (ξ k)) n) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro X
    simp [pathOperator, liftedProduct, dualConjugation_apply]
  | succ n ih =>
    rw [pathOperator, liftedProduct, dualConjugation_mul, ih]

noncomputable def markovCovariance (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) (μ : ProbabilityMeasure S) (n : ℕ) :
    (Complexified E →L[ℂ] Complexified E) →L[ℂ] (Complexified E →L[ℂ] Complexified E) :=
  transferCovariance (stateAverage (fun i => (μ : Measure S).real {i}))
    (stateAction (fun i => dualConjugation (liftedStep η (H i))) *
      stateMix (fun i j => (κ i).real {j})) stateConstant n

lemma markovCovariance_integral (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) (n : ℕ)
    (X : Complexified E →L[ℂ] Complexified E) :
    markovCovariance η H κ μ n X =
      ∫ ξ, dualConjugation (liftedProduct η (fun k => H (ξ k)) n) X
        ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)) := by
  have h := pathOperator_integral_transfer κ μ
    (fun i => dualConjugation (liftedStep η (H i))) (fun _ => X) n
  simp only [pathOperator_liftedProduct] at h
  simpa only [markovCovariance, transferCovariance, ContinuousLinearMap.comp_apply,
    stateConstant, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply] using! h.symm

lemma markovCovariance_prefix (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) (n N : ℕ) (hn : n ≤ N + 1) :
    markovCovariance η H κ μ n =
      finiteCovariance
        (fun h => ((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map
          (frestrictLe N)).real {h})
        (fun h => liftedProduct η (fun k => H (extendHistory h k)) n) := by
  apply ContinuousLinearMap.ext
  intro X
  rw [markovCovariance_integral]
  simp only [finiteCovariance, sum_apply, smul_apply]
  change _ = ∑ h, ((((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map
    (frestrictLe N)).real {h}) : ℂ) •
      dualConjugation (liftedProduct η (fun k => H (extendHistory h k)) n) X
  rw [← finite_integral_complex, integral_map (by fun_prop)
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp_rw [← pathOperator_liftedProduct]
  rw [pathOperator_prefix _ ξ n N hn]

lemma norm_markovCovariance_le_one (η : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) {L : ℝ} (hL : 0 < L)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) (n : ℕ) :
    ‖markovCovariance η H κ μ n‖ ≤ 1 := by
  apply norm_transferCovariance_le
  · exact norm_stateAverage_le _ (finite_probability_weights _).1 (finite_probability_weights _).2
  · apply (norm_mul_le _ _).trans
    have hD : ‖stateAction (fun i => dualConjugation (liftedStep η (H i)))‖ ≤ 1 := by
      apply norm_stateAction_le _ zero_le_one
      intro i
      have hn := norm_liftedStep_le_one (H i) hL (hs i) (hp i) (hb i) hη hηL
      exact (norm_dualConjugation_le _).trans (by nlinarith [norm_nonneg (liftedStep η (H i))])
    have hQ : ‖stateMix (B := Complexified E →L[ℂ] Complexified E)
        (fun i j => (κ i).real {j})‖ ≤ 1 :=
      norm_stateMix_le _ (fun i => (finite_probability_weights (κ i)).1)
        (fun i => (finite_probability_weights (κ i)).2)
    nlinarith [norm_nonneg (stateAction (fun i => dualConjugation (liftedStep η (H i)))),
      norm_nonneg (stateMix (B := Complexified E →L[ℂ] Complexified E) (fun i j => (κ i).real {j}))]
  · exact norm_stateConstant_le

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma censoredCovariance_eq_mean {Ω : Type*} [Fintype Ω] (v : Ω → ℝ)
    (H : Ω → ℕ → E →L[ℝ] E) (η q : ℝ) (N : ℕ) :
    censoredCovariance v H η q N =
      censoredMean q N (fun n => finiteCovariance v (fun ω => liftedProduct η (H ω) n)) := by
  simp only [censoredCovariance, finiteCovariance, Fintype.sum_prod_type,
    Complex.ofReal_mul, mul_smul, ← Finset.smul_sum]
  simp only [Complex.coe_smul]
  rw [censoredMean_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  change (v ω : ℂ) • (∑ x, (censorWeight q N x : ℂ) •
    dualConjugation (liftedProduct η (H ω) (censorTime N x))) = _
  simp only [censoredMean, Fintype.sum_sum_type, censorWeight, censorTime,
    Fintype.sum_unique, smul_add, Finset.smul_sum, smul_smul, Complex.ofReal_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((v ω : ℂ) * (((1 - q : ℝ) : ℂ) * ((q ^ k : ℝ) : ℂ))) •
    dualConjugation (liftedProduct η (H ω) (k + 1)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    change ((v ω : ℂ) * (((1 - q : ℝ) : ℂ) * ((q ^ k : ℝ) : ℂ))) •
      dualConjugation (liftedProduct η (H ω) (k + 1)) =
      (((1 - q) * q ^ k : ℝ) : ℂ) • ((v ω : ℂ) •
        dualConjugation (liftedProduct η (H ω) (k + 1)))
    rw [smul_smul, Complex.ofReal_mul, mul_comm (v ω : ℂ)]
  · change ((v ω : ℂ) * ((q ^ N : ℝ) : ℂ)) • dualConjugation (liftedProduct η (H ω) N) =
      ((q ^ N : ℝ) : ℂ) • ((v ω : ℂ) • dualConjugation (liftedProduct η (H ω) N))
    rw [smul_smul, mul_comm (v ω : ℂ)]

lemma censoredMarkovCovariance_eq_mean (η q : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) (N : ℕ) :
    censoredCovariance
      (fun h => ((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map
        (frestrictLe N)).real {h})
      (fun h k => H (extendHistory h k)) η q N =
        censoredMean q N (markovCovariance η H κ μ) := by
  rw [censoredCovariance_eq_mean]
  unfold censoredMean
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [markovCovariance_prefix η H κ μ (k + 1) N (by have := Finset.mem_range.mp hk; omega)]
  · rw [markovCovariance_prefix η H κ μ N N (by omega)]

set_option maxHeartbeats 800000 in
lemma geometricMarkovCovariance_ritt (η q : ℝ) (H : S → E →L[ℝ] E)
    (κ : Kernel S S) [IsMarkovKernel κ] (μ : ProbabilityMeasure S) {L : ℝ} (hL : 0 < L)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hq : 0 ≤ q) (hq1 : q < 1) (hsmall : 8 * (η * L) ≤ 1 - q) (n : ℕ) :
    (n + 1 : ℝ) * ‖geometricMean q (markovCovariance η H κ μ) ^ n -
      geometricMean q (markovCovariance η H κ μ) ^ (n + 1)‖ ≤ 4 := by
  have hηL : η * L ≤ 2 := by nlinarith
  apply covariance_ritt_limit _ (fun N => censoredMean q N (markovCovariance η H κ μ))
    (tendsto_censoredMean hq hq1 _ (norm_markovCovariance_le_one η H κ μ hL hs hp hb hη hηL))
  intro N k
  rw [← censoredMarkovCovariance_eq_mean η q H κ μ N]
  have hr : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hr2 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hr1 : Real.sqrt q < 1 := by nlinarith
  have h := censoredCovariance_ritt
    (fun h => ((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)).map
      (frestrictLe N)).real {h})
    (finite_probability_weights _).1 (finite_probability_weights _).2
    (fun h k => H (extendHistory h k)) hL
    (fun h k => hs _) (fun h k => hp _) (fun h k => hb _) hη hr hr1
    (by rwa [hr2]) N k
  simpa only [hr2] using h

end

end OracleTemplate.MarkovQuadratic
