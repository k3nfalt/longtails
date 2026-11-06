import LongTails.Proofs.SurjectiveProxLinearEnergy
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory

namespace LongTails.Proofs.SurjectiveProxLinearSampling

lemma finite_uniform_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ)
    (f : Fin (N + 1) → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (f i) P) :
    Integrable (fun z : Fin (N + 1) × Ω => f z.1 z.2)
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod P) ∧
    (∫ z : Fin (N + 1) × Ω, f z.1 z.2
      ∂((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod P)) =
      (∑ i, ∫ ω, f i ω ∂P) / (N + 1 : ℕ) := by
  have hm : Measurable (fun z : Fin (N + 1) × Ω => f z.1 z.2) :=
    measurable_from_prod_countable_right hf
  have hprod : Integrable (fun z : Fin (N + 1) × Ω => f z.1 z.2)
      ((PMF.uniformOfFintype (Fin (N + 1))).toMeasure.prod P) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hi, Integrable.of_finite⟩
  refine ⟨hprod, ?_⟩
  rw [integral_prod _ hprod, integral_fintype Integrable.of_finite]
  have hw (i : Fin (N + 1)) :
      (PMF.uniformOfFintype (Fin (N + 1))).toMeasure.real {i} = 1 / (N + 1 : ℕ) := by
    rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
    simp only [Fintype.card_fin, Fintype.card_unique, Nat.cast_one, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_natCast]
  simp_rw [hw, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearEnergy
open LongTails.Proofs.SurjectiveProxLinearTuning

noncomputable def certificateEstimator (p : Params) (Z : p.E → p.Ω → JointSpace p)
    (ξ : ℕ → p.Ω) (t : ℕ) : JointSpace p :=
  (1 / (certificateBatch p : ℝ)) • ∑ i : Fin (certificateBatch p),
    Z (trajectory p Z ξ t).1 (ξ (initialBatch p + t + i))

lemma measurable_certificateEstimator (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z)) (t : ℕ) :
    Measurable (fun ξ => certificateEstimator p Z ξ t) := by
  have hx := (measurable_trajectory p hp Z hZ t).fst
  have hs : Measurable (fun ξ => ∑ i : Fin (certificateBatch p),
      Z (trajectory p Z ξ t).1 (ξ (initialBatch p + t + i.val))) := by
    apply Finset.measurable_sum
    intro i _
    exact hZ.comp (hx.prodMk (measurable_pi_apply (initialBatch p + t + i.val)))
  exact hs.const_smul (1 / (certificateBatch p : ℝ))

lemma certificate_variance (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) (t : ℕ) :
    Integrable (fun ξ => ‖certificateEstimator p (jointOracle p g v D) ξ t -
      jointMean p I (trajectory p (jointOracle p g v D) ξ t).1‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) ∧
    (∫ ξ, ‖certificateEstimator p (jointOracle p g v D) ξ t -
      jointMean p I (trajectory p (jointOracle p g v D) ξ t).1‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) ≤ p.σ ^ 2 / certificateBatch p := by
  let Z := jointOracle p g v D
  have hx := (measurable_trajectory p hp Z (jointOracle_measurable p I g v D μ O) t).fst
  obtain ⟨G, hG, hfactor⟩ := SymmetricThirdOrderSampling.measurable_prefix_factor
    (μ : Measure p.Ω) (initialBatch p + t) (fun ξ => (trajectory p Z ξ t).1) hx
    (fun ξ ζ h => congrArg Prod.fst (trajectory_congr p Z t h))
  have hb := adaptive_batch_variance p I hp H g v D μ O
    (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)) (fun k ξ => ξ k)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid (μ : Measure p.Ω))
    (initialBatch p + t) (certificateBatch p) (certificateBatch_pos p) G hG
  simp_rw [← hfactor] at hb
  exact hb

lemma selected_step_second_moment (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    Integrable (fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
      ‖exactModelStep p I (trajectory p (jointOracle p g v D) z.2 z.1.val).1‖ ^ 2)
      ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) ∧
    (∫ z : Fin (iterations p + 1) × (ℕ → p.Ω),
      ‖exactModelStep p I (trajectory p (jointOracle p g v D) z.2 z.1.val).1‖ ^ 2
      ∂((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)))) ≤ radius p ^ 2 / 128 := by
  have h := finite_uniform_integral (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))
    (iterations p) (fun t ξ => ‖exactModelStep p I (trajectory p (jointOracle p g v D) ξ t.val).1‖ ^ 2)
    (fun t => ((continuous_exactModelStep p I hp H).measurable.comp
      (measurable_trajectory p hp _ (jointOracle_measurable p I g v D μ O) t.val).fst).norm.pow_const 2)
    (fun t => exact_step_square_integrable p I hp H g v D μ O t.val)
  refine ⟨h.1, ?_⟩
  rw [h.2, Fin.sum_univ_eq_sum_range (fun k => ∫ ξ,
    ‖exactModelStep p I (trajectory p (jointOracle p g v D) ξ k).1‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)))]
  exact expected_average_small p I hp H g v D μ O

lemma selected_certificate_second_moment (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    Integrable (fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
      ‖certificateEstimator p (jointOracle p g v D) z.2 z.1.val -
        jointMean p I (trajectory p (jointOracle p g v D) z.2 z.1.val).1‖ ^ 2)
      ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) ∧
    (∫ z : Fin (iterations p + 1) × (ℕ → p.Ω),
      ‖certificateEstimator p (jointOracle p g v D) z.2 z.1.val -
        jointMean p I (trajectory p (jointOracle p g v D) z.2 z.1.val).1‖ ^ 2
      ∂((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)))) ≤ certificateError p ^ 2 / 8 := by
  let Z := jointOracle p g v D
  let Q := Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)
  let f := fun (t : Fin (iterations p + 1)) (ξ : ℕ → p.Ω) =>
    ‖certificateEstimator p Z ξ t.val - jointMean p I (trajectory p Z ξ t.val).1‖ ^ 2
  have hZ := jointOracle_measurable p I g v D μ O
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  have hf (t : Fin (iterations p + 1)) : Measurable (f t) :=
    ((measurable_certificateEstimator p hp Z hZ t.val).sub
      (hM.comp (measurable_trajectory p hp Z hZ t.val).fst)).norm.pow_const 2
  have hv (t : Fin (iterations p + 1)) := certificate_variance p I hp H g v D μ O t.val
  have h := finite_uniform_integral Q (iterations p) f hf (fun t => (hv t).1)
  refine ⟨h.1, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => (hv t).2)
  have hmean : (∑ t, ∫ ξ, f t ξ ∂Q) / (iterations p + 1 : ℕ) ≤
      p.σ ^ 2 / certificateBatch p := by
    apply (div_le_iff₀ (show (0 : ℝ) < (iterations p + 1 : ℕ) by positivity)).mpr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_comm] using hsum
  have he := (variance_scales_positive p hp).2.2.1
  have hbatch : 8 * p.σ ^ 2 / certificateError p ^ 2 ≤ (certificateBatch p : ℝ) := by
    have hceil := Nat.le_ceil (8 * p.σ ^ 2 / certificateError p ^ 2)
    unfold certificateBatch
    push_cast
    linarith
  have hbatch' := (div_le_iff₀ (sq_pos_of_pos he)).mp hbatch
  have hscale : p.σ ^ 2 / certificateBatch p ≤ certificateError p ^ 2 / 8 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (certificateBatch_pos p))).mpr
    nlinarith
  exact h.2.le.trans (hmean.trans hscale)

end LongTails.Proofs.SurjectiveProxLinearSampling
