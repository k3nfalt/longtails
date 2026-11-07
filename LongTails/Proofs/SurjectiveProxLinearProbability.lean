import LongTails.Proofs.SurjectiveProxLinearSampling
import LongTails.Proofs.SurjectiveProxLinearAccuracy

open MeasureTheory

namespace LongTails.Proofs.SurjectiveProxLinearProbability

lemma simultaneous_norm_control {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (Y : Ω → F)
    (hX : Measurable X) (hY : Measurable Y) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXi : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hYi : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    (hXm : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ r ^ 2 / 8)
    (hYm : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ s ^ 2 / 8) :
    ENNReal.ofReal (3 / 4) ≤ P {ω | ‖X ω‖ ≤ r ∧ ‖Y ω‖ ≤ s} := by
  have hA := OracleTemplate.RobustGradient.norm_tail_le_second_moment hXi hr hXm
  have hB := OracleTemplate.RobustGradient.norm_tail_le_second_moment hYi hs hYm
  have ha : P.real {ω | r < ‖X ω‖} ≤ 1 / 8 := by
    convert hA using 1
    field_simp [hr.ne']
  have hb : P.real {ω | s < ‖Y ω‖} ≤ 1 / 8 := by
    convert hB using 1
    field_simp [hs.ne']
  have hbad := measureReal_union_le (μ := P) {ω | r < ‖X ω‖} {ω | s < ‖Y ω‖}
  have hm : MeasurableSet ({ω | r < ‖X ω‖} ∪ {ω | s < ‖Y ω‖}) :=
    (measurableSet_lt measurable_const hX.norm).union
      (measurableSet_lt measurable_const hY.norm)
  have hid : {ω | ‖X ω‖ ≤ r ∧ ‖Y ω‖ ≤ s} =
      ({ω | r < ‖X ω‖} ∪ {ω | s < ‖Y ω‖})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, not_or, not_lt]
  rw [hid, ← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  rw [measureReal_compl hm, probReal_univ]
  linarith

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearSampling
open LongTails.Proofs.SurjectiveProxLinearAccuracy
open LongTails.Proofs.SurjectiveProxLinearTuning

lemma selected_output_measurable (p : Params) (hp : spec.valid p)
    (Z : p.E → p.Ω → JointSpace p) (hZ : Measurable (Function.uncurry Z)) :
    Measurable (fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
      ((trajectory p Z z.2 z.1.val).1,
        dualPoint p ((jointEquiv p).symm (certificateEstimator p Z z.2 z.1.val)))) := by
  apply measurable_from_prod_countable_right
  intro t
  exact (measurable_trajectory p hp Z hZ t.val).fst.prodMk
    ((measurable_dualPoint p hp).comp ((jointEquiv p).symm.continuous.measurable.comp
      (measurable_certificateEstimator p hp Z hZ t.val)))

lemma selected_output_success (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ) :
    ENNReal.ofReal (3 / 4) ≤
      ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω)))
      {z | accurate p I ((trajectory p (jointOracle p g v D) z.2 z.1.val).1,
        dualPoint p ((jointEquiv p).symm
          (certificateEstimator p (jointOracle p g v D) z.2 z.1.val)))} := by
  let Z := jointOracle p g v D
  let X := fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
    exactModelStep p I (trajectory p Z z.2 z.1.val).1
  let Y := fun z : Fin (iterations p + 1) × (ℕ → p.Ω) =>
    certificateEstimator p Z z.2 z.1.val - jointMean p I (trajectory p Z z.2 z.1.val).1
  have hZ := jointOracle_measurable p I g v D μ O
  have hM := (jointMean_continuous p I H (le_trans (by norm_num) hp.2.1)).measurable
  have hX : Measurable X := measurable_from_prod_countable_right (fun t =>
    (continuous_exactModelStep p I hp H).measurable.comp
      (measurable_trajectory p hp Z hZ t.val).fst)
  have hY : Measurable Y := measurable_from_prod_countable_right (fun t =>
    (measurable_certificateEstimator p hp Z hZ t.val).sub
      (hM.comp (measurable_trajectory p hp Z hZ t.val).fst))
  have hstep := selected_step_second_moment p I hp H g v D μ O
  have hcert := selected_certificate_second_moment p I hp H g v D μ O
  have hsc := variance_scales_positive p hp
  have hgood := simultaneous_norm_control
    ((PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))) X Y hX hY
    (show 0 < radius p / 4 by have := hsc.2.1; positivity) hsc.2.2.1
    hstep.1 hcert.1 (by convert hstep.2 using 1; ring) hcert.2
  apply hgood.trans
  apply measure_mono
  intro z hz
  apply certificate_accurate p I hp H _ _ hz.1
  rw [← SurjectiveProxLinearProcess.error_norm_identity]
  exact pow_le_pow_left₀ (norm_nonneg _) hz.2 2

end LongTails.Proofs.SurjectiveProxLinearProbability
