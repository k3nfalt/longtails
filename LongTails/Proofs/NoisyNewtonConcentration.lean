import LongTails.Proofs.NoisyNewtonProcess
import LongTails.Proofs.NoisyNewtonEstimators
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import LongTails.Proofs.RobustAdaptiveFailures
import LongTails.Proofs.StochasticGeneralizedConcentration

namespace LongTails.Proofs.NoisyNewtonConcentration

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonProcess
open LongTails.Proofs.NoisyNewtonEstimators

noncomputable def correctionNoise (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d) (n : ℕ)
    (t : Trial (Point p.d)) (ξ : Fin n → p.Ω) : ℝ :=
  let a := actualWeight t
  let e := updateEstimate p t (sampleReplies p n g (trialPoint t) ξ) - grad (trialPoint t)
  (-a * ⟪t.previous.z - a • grad (trialPoint t) - u, e⟫ + (1 / 2 : ℝ) * a ^ 2 * ‖e‖ ^ 2)

lemma updateEstimate_sampleReplies (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (t : Trial (Point p.d)) (ξ : Fin (updateSize p (actualWeight t)) → p.Ω) :
    updateEstimate p t (sampleReplies p (updateSize p (actualWeight t)) g (trialPoint t) ξ) =
      OracleTemplate.RobustGradient.centeredClip (updateRadius p (actualWeight t))
        (-(t.curvature • t.displacement))
        ((1 / (updateSize p (actualWeight t) : ℝ)) • ∑ j, g (trialPoint t) (ξ j)) := by
  simp [updateEstimate, OracleTemplate.RobustGeneralized.meanBlock, sampleReplies]

lemma correctionNoise_control (p : Params) (hp : spec.valid p)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (t : Trial (Point p.d)) (ht : CorrectionReady p grad u t) :
    Integrable (fun ξ => Real.exp ((confidence p / p.R ^ 2) *
      correctionNoise p grad u g (updateSize p (actualWeight t)) t ξ))
      (Measure.pi fun _ : Fin (updateSize p (actualWeight t)) => P) ∧
    (∫ ξ, Real.exp ((confidence p / p.R ^ 2) *
      correctionNoise p grad u g (updateSize p (actualWeight t)) t ξ)
      ∂Measure.pi (fun _ : Fin (updateSize p (actualWeight t)) => P)) ≤
      Real.exp (p.ε * actualWeight t / (4096 * p.R ^ 2)) := by
  have hx : Measurable (g (trialPoint t)) := hg.comp (measurable_const.prodMk measurable_id)
  have hh := correction_mgf p hp P (g (trialPoint t)) hx (hgi _) (grad (trialPoint t))
    (hmean _) (hg2i _) (hvar _) t ht.1 (by simpa only [sub_neg_eq_add] using ht.2.2)
    (t.previous.z - actualWeight t • grad (trialPoint t) - u) ht.2.1
  simpa only [correctionNoise, updateEstimate_sampleReplies] using hh

lemma correctionNoise_normalized_control (p : Params) (hp : spec.valid p)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (t : Trial (Point p.d)) (ht : CorrectionReady p grad u t) :
    let C := p.ε * actualWeight t / (4096 * p.R ^ 2)
    Integrable (fun ξ => Real.exp ((confidence p / p.R ^ 2) *
      correctionNoise p grad u g (updateSize p (actualWeight t)) t ξ - C))
      (Measure.pi fun _ : Fin (updateSize p (actualWeight t)) => P) ∧
    (∫ ξ, Real.exp ((confidence p / p.R ^ 2) *
      correctionNoise p grad u g (updateSize p (actualWeight t)) t ξ - C)
      ∂Measure.pi (fun _ : Fin (updateSize p (actualWeight t)) => P)) ≤ 1 := by
  dsimp only
  have hh := correctionNoise_control p hp grad u g P hg hgi hmean hg2i hvar t ht
  simp_rw [Real.exp_sub]
  refine ⟨hh.1.div_const _, ?_⟩
  rw [integral_div]
  exact (div_le_one (Real.exp_pos _)).mpr hh.2

noncomputable def phaseIncrement (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d) (n : ℕ)
    (s : State (Point p.d)) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact match s with
  | .correction t _ _ => if CorrectionReady p grad u t then
      (confidence p / p.R ^ 2) * correctionNoise p grad u g n t ξ -
        p.ε * actualWeight t / (4096 * p.R ^ 2) else 0
  | _ => 0

noncomputable def ghostIncrement (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if stopped p s then 0 else phaseIncrement p grad u g n s.1 ξ

lemma ghostIncrement_control (p : Params) (hp : spec.valid p)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2) (s : Ghost p) :
    Integrable (fun ξ => Real.exp (ghostIncrement p grad u g (ghostCost p s) s ξ))
      (Measure.pi fun _ : Fin (ghostCost p s) => P) ∧
    (∫ ξ, Real.exp (ghostIncrement p grad u g (ghostCost p s) s ξ)
      ∂Measure.pi (fun _ : Fin (ghostCost p s) => P)) ≤ 1 := by
  classical
  by_cases hs : stopped p s
  · simp only [ghostIncrement, ite_eq_left hs, Real.exp_zero]
    exact ⟨integrable_const 1, by simp⟩
  · rcases s with ⟨state, error, flags⟩
    cases state with
    | model it k v =>
      simp only [ghostIncrement, phaseIncrement, ite_eq_right hs, Real.exp_zero]
      exact ⟨integrable_const 1, by simp⟩
    | hessian it v =>
      simp only [ghostIncrement, phaseIncrement, ite_eq_right hs, Real.exp_zero]
      exact ⟨integrable_const 1, by simp⟩
    | correction t k v =>
      by_cases hr : CorrectionReady p grad u t
      · have hcost : ghostCost p (.correction t k v, error, flags) = updateSize p (actualWeight t) := by
          simp only [ghostCost, hs, ↓reduceIte, phaseCost]
        rw [hcost]
        simp only [ghostIncrement, phaseIncrement, ite_eq_right hs, ite_eq_left hr]
        exact correctionNoise_normalized_control p hp grad u g P hg hgi hmean hg2i hvar t hr
      · simp only [ghostIncrement, phaseIncrement, ite_eq_right hs, ite_eq_right hr, Real.exp_zero]
        exact ⟨integrable_const 1, by simp⟩
    | done it =>
      simp only [ghostIncrement, phaseIncrement, ite_eq_right hs, Real.exp_zero]
      exact ⟨integrable_const 1, by simp⟩

open LongTails.Proofs.NoisyNewtonMeasurability

lemma measurableSet_correctionReady (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (hg : Measurable grad) :
    MeasurableSet {t | CorrectionReady p grad u t} := by
  unfold CorrectionReady
  exact (measurableSet_lt measurable_const measurable_actualWeight).inter
    ((measurableSet_le (by fun_prop : Measurable (fun t : Trial (Point p.d) =>
      ‖t.previous.z - actualWeight t • grad (trialPoint t) - u‖)) measurable_const).inter
      (measurableSet_le (by fun_prop : Measurable (fun t : Trial (Point p.d) =>
        ‖grad (trialPoint t) + t.curvature • t.displacement‖))
        (by fun_prop : Measurable (fun t : Trial (Point p.d) => updateRadius p (actualWeight t) / 2))))

lemma measurable_correctionNoise (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (hgrad : Measurable grad) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (correctionNoise p grad u g n)) := by
  have hr := (measurable_sampleReplies p n g hg).comp
    ((measurable_trialPoint.comp measurable_fst).prodMk measurable_snd)
  have hu := (measurable_updateEstimate p).comp (measurable_fst.prodMk hr)
  have hu' : Measurable (fun w : Trial (Point p.d) × (Fin n → p.Ω) =>
      updateEstimate p w.1 (sampleReplies p n g (trialPoint w.1) w.2)) := by
    simpa only [Function.comp_def] using hu
  have ha : Measurable (fun w : Trial (Point p.d) × (Fin n → p.Ω) => actualWeight w.1) := by fun_prop
  have he := hu'.sub (hgrad.comp (measurable_trialPoint.comp measurable_fst))
  have hz : Measurable (fun w : Trial (Point p.d) × (Fin n → p.Ω) =>
      w.1.previous.z - actualWeight w.1 • grad (trialPoint w.1) - u) := by fun_prop
  have hh := (ha.neg.mul (hz.inner he)).add
    (((ha.pow_const 2).const_mul (1 / 2 : ℝ)).mul (he.norm.pow_const 2))
  convert hh using 1
  funext w
  rfl

lemma measurable_phaseIncrement (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (hgrad : Measurable grad) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (phaseIncrement p grad u g n)) := by
  classical
  apply measurable_state_uncurry
  · exact measurable_const
  · exact measurable_const
  · dsimp only [phaseIncrement]
    apply Measurable.ite ((measurableSet_correctionReady p grad u hgrad).preimage (by fun_prop))
    · have hn := (measurable_correctionNoise p grad u g hgrad hg n).comp
        (by fun_prop : Measurable (fun w : (Trial (Point p.d) × ℕ × (ℕ → Point p.d)) ×
          (Fin n → p.Ω) => (w.1.1, w.2)))
      fun_prop
    · exact measurable_const
  · exact measurable_const

lemma measurable_ghostIncrement (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (hgrad : Measurable grad) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (ghostIncrement p grad u g n)) := by
  classical
  unfold ghostIncrement Function.uncurry
  apply Measurable.ite ((measurableSet_stopped p).preimage measurable_fst) measurable_const
  exact (measurable_phaseIncrement p grad u g hgrad hg n).comp
    (by fun_prop : Measurable (fun w : Ghost p × (Fin n → p.Ω) => (w.1.1, w.2)))

open OracleTemplate.StochasticGeneralized (accumulated accumulated_exp_control)

lemma ghost_accumulated_control (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (k : ℕ) (s : Ghost p) :
    Integrable (fun ξ => Real.exp (accumulated (ghostCost p) (ghostNext p f u grad g H)
      (ghostIncrement p grad u g) k s ξ)) (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, Real.exp (accumulated (ghostCost p) (ghostNext p f u grad g H)
      (ghostIncrement p grad u g) k s ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 1 := by
  exact accumulated_exp_control P (measurable_ghostCost p)
    (measurable_ghostNext p f u grad g H hf hgrad hg hH)
    (measurable_ghostIncrement p grad u g hgrad hg)
    (fun s => (ghostIncrement_control p hp grad u g P hg hgi hmean hg2i hvar s).1)
    (fun s => (ghostIncrement_control p hp grad u g P hg hgi hmean hg2i hvar s).2) k s

open OracleTemplate.GeneralizedAccelerated (tentativeWeight coupling)

noncomputable def modelBad (p : Params) (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) : Prop :=
  ¬ stopped p s ∧ 0 < tentativeWeight (baseIterate s.1) ∧
    (ghostNext p f u grad g H n s ξ).2.2.1 = true

noncomputable def modelFailureIncrement (p : Params) (f : Point p.d → ℝ)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if modelBad p f grad u g H n s ξ then 1 else 0

lemma measurableSet_modelBad (p : Params) (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    MeasurableSet {w : Ghost p × (Fin n → p.Ω) | modelBad p f grad u g H n w.1 w.2} := by
  have hb : Measurable (fun w : Ghost p × (Fin n → p.Ω) => baseIterate w.1.1) :=
    (measurable_baseIterate p).comp (by fun_prop)
  have hw : Measurable (fun w : Ghost p × (Fin n → p.Ω) => tentativeWeight (baseIterate w.1.1)) := by
    fun_prop
  have hn := measurable_ghostNext p f u grad g H hf hgrad hg hH n
  have hflag := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hn))
  exact ((measurableSet_stopped p).preimage measurable_fst).compl.inter
    ((measurableSet_lt measurable_const hw).inter (measurableSet_eq_fun hflag measurable_const))

lemma measurable_modelFailureIncrement (p : Params) (f : Point p.d → ℝ)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (modelFailureIncrement p f grad u g H n)) := by
  classical
  unfold modelFailureIncrement Function.uncurry
  exact Measurable.ite (measurableSet_modelBad p f grad u g H hf hgrad hH hg n)
    measurable_const measurable_const

lemma modelFailureIncrement_bounds (p : Params) (f : Point p.d → ℝ)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) :
    0 ≤ modelFailureIncrement p f grad u g H n s ξ ∧
      modelFailureIncrement p f grad u g H n s ξ ≤ 1 := by
  unfold modelFailureIncrement
  split_ifs <;> norm_num

lemma modelFailureIncrement_mean (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2) (s : Ghost p) :
    (∫ ξ, modelFailureIncrement p f grad u g H (ghostCost p s) s ξ
      ∂Measure.pi (fun _ : Fin (ghostCost p s) => P)) ≤ (1 / 2 : ℝ) ^ modelGroups p := by
  classical
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ modelGroups p := by positivity
  by_cases hs : stopped p s
  · simp [modelFailureIncrement, modelBad, hs]
  · rcases s with ⟨state, error, flags⟩
    cases state with
    | model it k v =>
      by_cases ha : 0 < tentativeWeight it
      · have hcost : ghostCost p (.model it k v, error, flags) = modelCost p (tentativeWeight it) := by
          simp only [ghostCost, hs, ↓reduceIte, phaseCost]
        rw [hcost]
        let m := modelCost p (tentativeWeight it)
        let estimate : (Fin m → p.Ω) → Point p.d := fun ξ =>
          modelEstimate p (tentativeWeight it) (sampleReplies p m g (coupling it) ξ)
        have hr := (measurable_sampleReplies p m g hg).comp
          ((measurable_const (a := coupling it)).prodMk measurable_id)
        have hestimate : Measurable estimate := by
          have hh := (measurable_modelEstimate p).comp
            ((measurable_const (a := tentativeWeight it)).prodMk hr)
          simpa only [estimate, Function.comp_def, id_eq] using hh
        have hset : MeasurableSet {ξ | modelRadius p (tentativeWeight it) / 2 <
            ‖estimate ξ - grad (coupling it)‖} :=
          measurableSet_lt measurable_const (hestimate.sub_const _).norm
        have he (ξ : Fin m → p.Ω) : modelFailureIncrement p f grad u g H m
            (.model it k v, error, flags) ξ =
            ({ξ | modelRadius p (tentativeWeight it) / 2 < ‖estimate ξ - grad (coupling it)‖}).indicator
              (fun _ => (1 : ℝ)) ξ := by
          simp [modelFailureIncrement, modelBad, ghostNext, hs, ha, baseIterate, estimate, Set.indicator]
        change (∫ ξ : Fin m → p.Ω, modelFailureIncrement p f grad u g H m
          (.model it k v, error, flags) ξ ∂Measure.pi (fun _ : Fin m => P)) ≤ _
        rw [show (fun ξ : Fin m → p.Ω => modelFailureIncrement p f grad u g H m
          (.model it k v, error, flags) ξ) = _ from funext he]
        change (∫ ξ, ({ξ | modelRadius p (tentativeWeight it) / 2 <
          ‖estimate ξ - grad (coupling it)‖}).indicator (1 : (Fin m → p.Ω) → ℝ) ξ
          ∂Measure.pi (fun _ : Fin m => P)) ≤ _
        rw [integral_indicator_one hset]
        have hx : Measurable (g (coupling it)) := hg.comp (measurable_const.prodMk measurable_id)
        have hh := model_failure p hp P (g (coupling it)) hx (hgi _) (grad (coupling it))
          (hmean _) (hg2i _) (hvar _) (tentativeWeight it) ha
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hnonneg)
      · simp [modelFailureIncrement, modelBad, baseIterate, ha]
    | hessian it v =>
      simp [modelFailureIncrement, modelBad, ghostNext, hs]
    | correction t k v =>
      simp [modelFailureIncrement, modelBad, ghostNext, hs]
    | done it =>
      simp [modelFailureIncrement, modelBad, ghostNext, hs]

lemma modelFailure_accumulated_probability (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (k : ℕ) (s : Ghost p) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 1 ≤ accumulated (ghostCost p) (ghostNext p f u grad g H)
        (modelFailureIncrement p f grad u g H) k s ξ} ≤
      ENNReal.ofReal ((k : ℝ) * (1 / 2 : ℝ) ^ modelGroups p) := by
  exact OracleTemplate.RobustGradient.accumulated_failure_probability P (measurable_ghostCost p)
    (measurable_ghostNext p f u grad g H hf hgrad hg hH)
    (measurable_modelFailureIncrement p f grad u g H hf hgrad hH hg)
    (modelFailureIncrement_bounds p f grad u g H)
    (modelFailureIncrement_mean p hp f grad u g H P hg hgi hmean hg2i hvar) k s

noncomputable def modelFailureValue (p : Params) (s : Ghost p) : ℝ :=
  if s.2.2.1 = true then 1 else 0

lemma modelFailureIncrement_difference (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (n : ℕ) (s : Ghost p) (ξ : Fin n → p.Ω) (hs : StateBounds p s.1) :
    modelFailureIncrement p f grad u g H n s ξ =
      modelFailureValue p (ghostNext p f u grad g H n s ξ) - modelFailureValue p s := by
  by_cases hstop : stopped p s
  · simp [modelFailureIncrement, modelBad, hstop, ghostNext_of_stopped p f u grad g H n s ξ hstop]
  · have hf := live_flags p s hstop
    have hfloor : 0 < curvatureFloor p := by
      unfold curvatureFloor
      exact div_pos (by norm_num) (LongTails.Proofs.NoisyNewtonTuning.target_pos p hp)
    have hw := OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos (baseIterate s.1)
      (hfloor.trans_le hs.1.2.2)
    simp [modelFailureIncrement, modelBad, hstop, hw, modelFailureValue, hf.1]

open OracleTemplate.StochasticGeneralized (blockTrace blockTrace_start_succ)

lemma modelFailure_accumulated_eq (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (k : ℕ) (s : Ghost p) (ξ : ℕ → p.Ω) (hs : StateBounds p s.1) :
    accumulated (ghostCost p) (ghostNext p f u grad g H)
      (modelFailureIncrement p f grad u g H) k s ξ =
      modelFailureValue p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ k).1 -
        modelFailureValue p s := by
  induction k generalizing s ξ with
  | zero => simp [accumulated, OracleTemplate.StochasticGeneralized.blockTrace_zero]
  | succ k ih =>
    rw [accumulated, ih _ _ (ghostNext_bounds p hp f u grad g H _ _ _ hs),
      modelFailureIncrement_difference p hp f grad u g H _ _ _ hs, blockTrace_start_succ]
    ring

lemma modelFailure_probability (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (k : ℕ) (s : Ghost p) (hs : StateBounds p s.1) (hflag : s.2.2.1 = false) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ k).1.2.2.1 = true} ≤
      ENNReal.ofReal ((k : ℝ) * (1 / 2 : ℝ) ^ modelGroups p) := by
  apply le_trans (measure_mono ?_)
    (modelFailure_accumulated_probability p hp f grad u g H P hf hgrad hH hg hgi hmean hg2i hvar k s)
  intro ξ hξ
  change (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ k).1.2.2.1 = true at hξ
  change 1 ≤ accumulated (ghostCost p) (ghostNext p f u grad g H)
    (modelFailureIncrement p f grad u g H) k s ξ
  rw [modelFailure_accumulated_eq p hp f grad u g H k s ξ hs]
  simp only [modelFailureValue, hξ, hflag, ite_true, Bool.false_eq_true, ite_false, sub_zero, le_refl]

noncomputable def phaseGuardedWeight (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (s : State (Point p.d)) : ℝ := by
  classical
  exact match s with
  | .correction t _ _ => if CorrectionReady p grad u t then actualWeight t else 0
  | _ => 0

noncomputable def guardedWeight (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (s : Ghost p) : ℝ := by
  classical
  exact if stopped p s then 0 else phaseGuardedWeight p grad u s.1

noncomputable def ghostNoise (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if stopped p s then 0 else match s.1 with
  | .correction t _ _ => if CorrectionReady p grad u t then correctionNoise p grad u g n t ξ else 0
  | _ => 0

lemma ghostIncrement_eq (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d) (n : ℕ)
    (s : Ghost p) (ξ : Fin n → p.Ω) :
    ghostIncrement p grad u g n s ξ = (confidence p / p.R ^ 2) * ghostNoise p grad u g n s ξ -
      (p.ε / (4096 * p.R ^ 2)) * guardedWeight p grad u s := by
  rcases s with ⟨state, error, flags⟩
  cases state <;> simp only [ghostIncrement, phaseIncrement, ghostNoise, guardedWeight, phaseGuardedWeight]
  all_goals split_ifs <;> ring

lemma guardedWeight_bounds (p : Params) (hp : spec.valid p) (grad : Point p.d → Point p.d)
    (u : Point p.d) (s : Ghost p) (hs : StateBounds p s.1) :
    0 ≤ guardedWeight p grad u s ∧ guardedWeight p grad u s ≤ ghostWeight p s := by
  have hnonneg := ghostWeight_nonneg p hp s hs
  rcases s with ⟨state, error, flags⟩
  cases state <;> simp only [guardedWeight, phaseGuardedWeight, ghostWeight, phaseWeight] at *
  all_goals split_ifs at * <;> simp_all

lemma measurable_phaseGuardedWeight (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (hg : Measurable grad) : Measurable (phaseGuardedWeight p grad u) := by
  have hh : Measurable (fun w : State (Point p.d) × Unit => phaseGuardedWeight p grad u w.1) := by
    apply measurable_state_uncurry (F := fun s (_ : Unit) => phaseGuardedWeight p grad u s)
    · exact measurable_const
    · exact measurable_const
    · dsimp only [phaseGuardedWeight]
      exact Measurable.ite ((measurableSet_correctionReady p grad u hg).preimage (by fun_prop))
        (by fun_prop) measurable_const
    · exact measurable_const
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_guardedWeight (p : Params) (grad : Point p.d → Point p.d)
    (u : Point p.d) (hg : Measurable grad) : Measurable (guardedWeight p grad u) := by
  unfold guardedWeight
  exact Measurable.ite (measurableSet_stopped p) measurable_const
    ((measurable_phaseGuardedWeight p grad u hg).comp measurable_fst)

lemma measurable_ghostNoise (p : Params) (hp : spec.valid p) (grad : Point p.d → Point p.d)
    (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (hgrad : Measurable grad) (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (ghostNoise p grad u g n)) := by
  have hR := hp.2.2.2.2.2.1
  have hl := LongTails.Proofs.NoisyNewtonTuning.confidence_lower p hp
  have ht : confidence p / p.R ^ 2 ≠ 0 := ne_of_gt (div_pos (by linarith) (sq_pos_of_pos hR))
  have he : Function.uncurry (ghostNoise p grad u g n) = fun w : Ghost p × (Fin n → p.Ω) =>
      (ghostIncrement p grad u g n w.1 w.2 + (p.ε / (4096 * p.R ^ 2)) * guardedWeight p grad u w.1) /
        (confidence p / p.R ^ 2) := by
    funext w
    rw [ghostIncrement_eq]
    simp only [sub_add_cancel, mul_div_cancel_left₀ _ ht]
    rfl
  rw [he]
  have hi := measurable_ghostIncrement p grad u g hgrad hg n
  have hw : Measurable (fun w : Ghost p × (Fin n → p.Ω) => guardedWeight p grad u w.1) :=
    (measurable_guardedWeight p grad u hgrad).comp measurable_fst
  exact (hi.add (hw.const_mul _)).div_const _

lemma guardedWeight_accumulated_bound (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (k : ℕ) (s : Ghost p) (ξ : ℕ → p.Ω) (hs : StateBounds p s.1) :
    accumulated (ghostCost p) (ghostNext p f u grad g H)
      (fun _ s _ => guardedWeight p grad u s) k s ξ ≤ 3 * target p / 2 := by
  rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum]
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (guardedWeight_bounds p hp grad u _ (ghostTrace_bounds p hp f u grad g H s ξ i hs)).2))
  exact ghostWeight_sum_bound p hp f u grad g H s ξ k hs

lemma ghostIncrement_accumulated_eq (p : Params) (f : Point p.d → ℝ)
    (grad : Point p.d → Point p.d) (u : Point p.d) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (k : ℕ) (s : Ghost p) (ξ : ℕ → p.Ω) :
    accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostIncrement p grad u g) k s ξ =
      (confidence p / p.R ^ 2) *
        accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) k s ξ -
      (p.ε / (4096 * p.R ^ 2)) * accumulated (ghostCost p) (ghostNext p f u grad g H)
        (fun _ s _ => guardedWeight p grad u s) k s ξ := by
  have he : ghostIncrement p grad u g = fun n s ξ =>
      (confidence p / p.R ^ 2) * ghostNoise p grad u g n s ξ +
        (-(p.ε / (4096 * p.R ^ 2))) * guardedWeight p grad u s := by
    funext n s ξ
    rw [ghostIncrement_eq]
    ring
  rw [he, OracleTemplate.StochasticGeneralized.accumulated_linear]
  ring

lemma guardedWeight_compensation (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (k : ℕ) (s : Ghost p) (ξ : ℕ → p.Ω) (hs : StateBounds p s.1) :
    (p.ε / (4096 * p.R ^ 2)) * accumulated (ghostCost p) (ghostNext p f u grad g H)
      (fun _ s _ => guardedWeight p grad u s) k s ξ ≤ 48 / 4096 := by
  have hR := hp.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  have hh := mul_le_mul_of_nonneg_left (guardedWeight_accumulated_bound p hp f grad u g H k s ξ hs)
    (by positivity : 0 ≤ p.ε / (4096 * p.R ^ 2))
  refine hh.trans_eq ?_
  unfold target
  field_simp
  ring

lemma ghostNoise_accumulated_control (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (k : ℕ) (s : Ghost p) (hs : StateBounds p s.1) :
    Integrable (fun ξ => Real.exp ((confidence p / p.R ^ 2) *
      accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) k s ξ))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, Real.exp ((confidence p / p.R ^ 2) *
      accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) k s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ Real.exp (48 / 4096) := by
  have hh := ghost_accumulated_control p hp f grad u g H P hf hgrad hH hg hgi hmean hg2i hvar k s
  have hm : Measurable (accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) k s) :=
    (OracleTemplate.StochasticGeneralized.accumulated_measurable (measurable_ghostCost p)
    (measurable_ghostNext p f u grad g H hf hgrad hg hH)
    (measurable_ghostNoise p hp grad u g hgrad hg) k).comp measurable_prodMk_left
  apply OracleTemplate.StochasticGeneralized.remove_compensator hm hh.1 hh.2
  intro ξ
  rw [ghostIncrement_accumulated_eq]
  have hc := guardedWeight_compensation p hp f grad u g H k s ξ hs
  linarith

lemma ghostNoise_tail (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : Measure p.Ω) [IsProbabilityMeasure P]
    (hf : Measurable f) (hgrad : Measurable grad) (hH : Measurable H)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = grad x)
    (hg2i : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (k : ℕ) (s : Ghost p) (hs : StateBounds p s.1) :
    (Measure.infinitePi fun _ : ℕ => P) {ξ | 2 * p.R ^ 2 <
      accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) k s ξ} ≤
      ENNReal.ofReal (Real.exp (48 / 4096 - 2 * confidence p)) := by
  have hR := hp.2.2.2.2.2.1
  have hl := LongTails.Proofs.NoisyNewtonTuning.confidence_lower p hp
  have hh := ghostNoise_accumulated_control p hp f grad u g H P hf hgrad hH hg hgi hmean hg2i hvar k s hs
  have hb := OracleTemplate.StochasticGeneralized.exponential_tail
    (show 0 ≤ confidence p / p.R ^ 2 by positivity) hh.1 hh.2 (r := 2 * p.R ^ 2)
  have he : (confidence p / p.R ^ 2) * (2 * p.R ^ 2) = 2 * confidence p := by
    field_simp
  simpa only [he] using hb

end LongTails.Proofs.NoisyNewtonConcentration
