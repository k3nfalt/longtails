import LongTails.Proofs.StochasticEqualityExecution
import LongTails.Proofs.StochasticEqualityGeometry
import LongTails.Proofs.NoisyNewtonModel
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.StochasticEqualitySampling

open MeasureTheory OracleTemplate
open LongTails.Algorithms.StochasticEqualityDirection
open LongTails.Algorithms.StochasticEquality
open LongTails.Setups.StochasticRegularEqualities

section Operators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma isClosed_regular (ν : ℝ) : IsClosed {J : F →L[ℝ] E | regular ν J} := by
  simp only [regular, Set.ofPred_forall]
  exact isClosed_iInter (fun v => isClosed_le continuous_const
    (continuous_id.clm_apply continuous_const).norm)

lemma measurable_multiplier : Measurable (fun z : (F →L[ℝ] E) × E => multiplier z.1 z.2) := by
  have ha : Continuous (fun J : F →L[ℝ] E => J.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have hgram : Continuous (fun J : F →L[ℝ] E => J.adjoint.comp J) := ha.clm_comp continuous_id
  have hi : Measurable (fun J : F →L[ℝ] E => Ring.inverse (J.adjoint.comp J)) := by
    simpa only [ContinuousLinearMap.ringInverse_eq_inverse, Function.comp_def] using
      NoisyNewtonModel.measurable_inverse.comp hgram.measurable
  have heval : Continuous (fun z : (F →L[ℝ] F) × F => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  change Measurable (fun z : (F →L[ℝ] E) × E => -(Ring.inverse (z.1.adjoint.comp z.1))
    (z.1.adjoint z.2))
  convert (heval.measurable.comp ((hi.comp measurable_fst).prodMk
      ((ha.comp continuous_fst).clm_apply continuous_snd).measurable)).neg using 1
  ext z
  rfl

lemma measurable_thresholdedMultiplier (ν : ℝ) :
    Measurable (fun z : (F →L[ℝ] E) × E => thresholdedMultiplier ν z.1 z.2) := by
  classical
  exact measurable_multiplier.ite
    ((isClosed_regular (E := E) (F := F) (ν / 2)).measurableSet.preimage measurable_fst)
    measurable_const

lemma measurable_direction (ν : ℝ) :
    Measurable (fun z : ((F →L[ℝ] E) × E) × F => direction ν z.1.1 z.1.2 z.2) := by
  have hm : Measurable (fun z : ((F →L[ℝ] E) × E) × F =>
      thresholdedMultiplier ν z.1.1 z.1.2) :=
    (measurable_thresholdedMultiplier (E := E) (F := F) ν).comp measurable_fst
  have heval : Continuous (fun z : (F →L[ℝ] E) × F => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact ((measurable_snd.comp measurable_fst).add
    (heval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk hm))).neg.sub
      (heval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

end Operators

open LongTails.Proofs.StochasticEqualityExecution

lemma measurable_sampled_mean {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g)) (n offset : ℕ) :
    Measurable (fun z : Point p.d × (ℕ → Ω) =>
      QueryPlan.sampledEval g (fun i => z.2 (i / 2))
        (meanPlan p n (pairedSample p z.1)) (2 * offset)) := by
  simp_rw [sampled_mean]
  exact (Finset.measurable_sum _ (fun i _ => hg.comp
    (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)))).const_smul ((n : ℝ)⁻¹)

lemma measurable_sampled_robust {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (t : ℝ) (n k offset : ℕ) :
    Measurable (fun z : Point p.d × (ℕ → Ω) =>
      QueryPlan.sampledEval g (fun i => z.2 (i / 2))
        (LongTails.Algorithms.StochasticEquality.robustPlan p t n k z.1) (2 * offset)) := by
  simp_rw [sampled_robust]
  have hv (j : Fin k) : Measurable (fun z : Point p.d × (ℕ → Ω) =>
      (n : ℝ)⁻¹ • ∑ i : Fin n, g z.1 (z.2 (offset + n * j.val + i.val))) := by
    exact (Finset.measurable_sum _ (fun i _ => hg.comp
      (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd)))).const_smul ((n : ℝ)⁻¹)
  exact ((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
    (Measurable.of_eval fun j => (hv j).fst))).prodMk
      (((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
        (Measurable.of_eval fun j => (hv j).snd.fst))).prodMk
      ((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
        (Measurable.of_eval fun j => (hv j).snd.snd))))

lemma measurable_clipReply (p : Public) (G M : ℝ) : Measurable (clipReply p G M) := by
  exact ((measurable_clip G).comp measurable_fst).prodMk
    (((measurable_clip M).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_clip p.Lc).comp (measurable_snd.comp measurable_snd)))

set_option maxHeartbeats 1000000 in
lemma measurable_reply_direction (p : Public) : Measurable (fun v : Reply p =>
    direction p.ν (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m v.2.2) v.1 v.2.1) := by
  have hJ : Measurable (fun v : Reply p =>
      LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m v.2.2) :=
    (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m).continuous.measurable.comp
      (measurable_snd.comp measurable_snd)
  exact (measurable_direction (E := Point p.d) (F := Point p.m) p.ν).comp
    ((hJ.prodMk measurable_fst).prodMk (measurable_fst.comp measurable_snd))

lemma measurable_estimator_eval {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (s : X → TrainingState p) (hx : Measurable (fun z => (s z).point))
    (hy : Measurable (fun z => (s z).previous))
    (hv : Measurable (fun z => (s z).estimate)) (k offset : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (fun i => ξ z (i / 2))
      (estimatorPlan p cfg k (s z)) (2 * offset)) := by
  simp_rw [sampled_estimator]
  split_ifs with h
  · exact (Finset.measurable_sum _ (fun i _ => hg.comp
      (hx.prodMk ((measurable_pi_apply _).comp hξ)))).const_smul ((cfg.resetBatch : ℝ)⁻¹)
  · exact hv.add ((Finset.measurable_sum _ (fun i _ =>
      (hg.comp (hx.prodMk ((measurable_pi_apply _).comp hξ))).sub
        (hg.comp (hy.prodMk ((measurable_pi_apply _).comp hξ))))).const_smul
          ((cfg.incrementBatch : ℝ)⁻¹))

lemma measurable_training_update {X : Type*} [MeasurableSpace X]
    (p : Public) (cfg : Config) (k index : ℕ) (s : X → TrainingState p) (v : X → Reply p)
    (hx : Measurable (fun z => (s z).point))
    (hs : Measurable (fun z => (s z).selected)) (hv : Measurable v) :
    Measurable (fun z => (trainingUpdate p cfg k index (s z) (v z)).point) ∧
    Measurable (fun z => (trainingUpdate p cfg k index (s z) (v z)).previous) ∧
    Measurable (fun z => (trainingUpdate p cfg k index (s z) (v z)).estimate) ∧
    Measurable (fun z => (trainingUpdate p cfg k index (s z) (v z)).selected) := by
  have he := (measurable_clipReply p cfg.gradientCap cfg.constraintCap).comp hv
  refine ⟨hx.add (((measurable_reply_direction p).comp he).const_smul cfg.step), hx, he, ?_⟩
  by_cases h : k = index
  · simpa only [trainingUpdate, h, ↓reduceIte] using hx
  · simpa only [trainingUpdate, h, ↓reduceIte] using hs

open LongTails.Algorithms.StochasticEnvelopeProgram

lemma measurable_training_segment {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (n slot offset index : ℕ) (s : X → TrainingState p)
    (hx : Measurable (fun z => (s z).point))
    (hy : Measurable (fun z => (s z).previous))
    (hv : Measurable (fun z => (s z).estimate))
    (hs : Measurable (fun z => (s z).selected)) :
    let output := fun z => QueryPlan.sampledEval g (fun i => ξ z (i / 2))
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k index u))
          n slot (s z)) (2 * offset)
    Measurable (fun z => (output z).point) ∧
    Measurable (fun z => (output z).previous) ∧
    Measurable (fun z => (output z).estimate) ∧
    Measurable (fun z => (output z).selected) := by
  induction n generalizing slot offset s with
  | zero => exact ⟨hx, hy, hv, hs⟩
  | succ n ih =>
    dsimp only
    simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    rw [show 2 * offset + 2 * batchSize cfg slot = 2 * (offset + batchSize cfg slot) by omega]
    have he := measurable_estimator_eval p cfg g hg ξ hξ s hx hy hv slot offset
    have hu := measurable_training_update p cfg slot index s _ hx hs he
    exact ih (slot + 1) (offset + batchSize cfg slot) _ hu.1 hu.2.1 hu.2.2.1 hu.2.2.2

lemma measurable_training_output {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (index : Fin cfg.steps) (offset : ℕ) :
    Measurable (fun z : Point p.d × (ℕ → Ω) =>
      QueryPlan.sampledEval g (fun i => z.2 (i / 2))
        (trainingPlan p cfg index z.1) (2 * offset)) := by
  simp only [trainingPlan, trainingPrefixPlan, trainingCalls, QueryPlan.sampledEval_map]
  exact (measurable_training_segment p cfg g hg Prod.snd measurable_snd
    cfg.steps 0 offset index (fun z => ⟨z.1, z.1, 0, z.1⟩)
    measurable_fst measurable_fst measurable_const measurable_fst).2.2.2

set_option maxHeartbeats 1000000 in
lemma measurable_clipped_jacobian (p : Public) : Measurable (fun v : Reply p =>
    LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc v.2.2)) := by
  exact (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m).continuous.measurable.comp
    ((measurable_clip p.Lc).comp (measurable_snd.comp measurable_snd))

lemma measurable_restore_update (p : Public) (cfg : Config) :
    Measurable (fun z : Point p.d × Reply p => restoreUpdate p cfg z.1 z.2) := by
  have hJ := (measurable_clipped_jacobian p).comp
    (measurable_snd : Measurable (Prod.snd : Point p.d × Reply p → Reply p))
  have hC : Measurable (fun z : Point p.d × Reply p => clip cfg.restoreCap z.2.2.1) :=
    (measurable_clip cfg.restoreCap).comp ((measurable_fst.comp measurable_snd).comp measurable_snd)
  have heval : Continuous (fun z : (Point p.m →L[ℝ] Point p.d) × Point p.m => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact measurable_fst.sub ((heval.measurable.comp (hJ.prodMk hC)).const_smul cfg.restoreStep)

lemma measurable_restoration_segment {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (n slot offset : ℕ) (x : X → Point p.d) (hx : Measurable x) :
    Measurable (fun z => QueryPlan.sampledEval g (fun i => ξ z (i / 2))
      (slotPlan (fun _ => restoreUnitCalls cfg)
        (fun _ u => (LongTails.Algorithms.StochasticEquality.robustPlan p cfg.restoreTolerance
          cfg.restoreBatch cfg.restoreGroups u).map (restoreUpdate p cfg u)) n slot (x z))
        (2 * offset)) := by
  induction n generalizing slot offset x with
  | zero => exact hx
  | succ n ih =>
    simp only [slotPlan, slotCalls, restoreUnitCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    rw [show 2 * offset + 2 * cfg.restoreBatch * cfg.restoreGroups =
      2 * (offset + cfg.restoreBatch * cfg.restoreGroups) by ring]
    have hr := (measurable_sampled_robust p g hg cfg.restoreTolerance
      cfg.restoreBatch cfg.restoreGroups offset).comp (hx.prodMk hξ)
    exact ih (slot + 1) _ _ ((measurable_restore_update p cfg).comp (hx.prodMk hr))

lemma measurable_restoration_output {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (offset : ℕ) :
    Measurable (fun ξ : ℕ → Ω => QueryPlan.sampledEval g (fun i => ξ (i / 2))
      (restorePlan p cfg) (2 * offset)) := by
  exact measurable_restoration_segment p cfg g hg id measurable_id cfg.restoreSteps 0 offset
    (fun _ => p.x0) measurable_const

set_option maxHeartbeats 3000000 in
lemma measurable_validator_multiplier (p : Public) (cfg : Config) :
    Measurable (fun v : Reply p => thresholdedMultiplier p.ν
      (LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc v.2.2))
      (clip cfg.gradientCap v.1)) := by
  let J : Reply p → Point p.m →L[ℝ] Point p.d := fun v =>
    LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc v.2.2)
  let G : Reply p → Point p.d := fun v => clip cfg.gradientCap v.1
  have hJ : Measurable J := measurable_clipped_jacobian p
  have hG : Measurable G := (measurable_clip cfg.gradientCap).comp measurable_fst
  have hm : Measurable (fun z : (Point p.m →L[ℝ] Point p.d) × Point p.d =>
      thresholdedMultiplier p.ν z.1 z.2) := measurable_thresholdedMultiplier p.ν
  change Measurable (fun v => thresholdedMultiplier p.ν (J v) (G v))
  convert hm.comp (hJ.prodMk hG) using 1
  rfl

lemma measurableSet_validation_test {X : Type*} [MeasurableSpace X] (p : Public) (cfg : Config)
    (v : X → Reply p) (hv : Measurable v) :
    let J := fun z => LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc (v z).2.2)
    let lm := fun z => thresholdedMultiplier p.ν (J z) (clip cfg.gradientCap (v z).1)
    MeasurableSet {z | regular (p.ν / 2) (J z) ∧
      ‖(v z).1 + J z (lm z)‖ ^ 2 + ‖(v z).2.1‖ ^ 2 ≤ p.ε ^ 2 / 16} := by
  let J := fun z => LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc (v z).2.2)
  let lm :=  fun z => thresholdedMultiplier p.ν (J z) (clip cfg.gradientCap (v z).1)
  have hJ : Measurable J := (measurable_clipped_jacobian p).comp hv
  have hlm : Measurable lm := (measurable_validator_multiplier p cfg).comp hv
  have heval : Continuous (fun z : (Point p.m →L[ℝ] Point p.d) × Point p.m => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hres : Measurable (fun z => ‖(v z).1 + J z (lm z)‖ ^ 2 + ‖(v z).2.1‖ ^ 2) :=
    ((hv.fst.add (heval.measurable.comp (hJ.prodMk hlm))).norm.pow_const 2).add
      (hv.snd.fst.norm.pow_const 2)
  have hs : MeasurableSet {z | regular (p.ν / 2) (J z) ∧
      ‖(v z).1 + J z (lm z)‖ ^ 2 + ‖(v z).2.1‖ ^ 2 ≤ p.ε ^ 2 / 16} :=
    ((isClosed_regular (E := Point p.d) (F := Point p.m) (p.ν / 2)).measurableSet.preimage hJ).inter
      (measurableSet_le hres measurable_const)
  exact hs

lemma measurable_validate_getD {X : Type*} [MeasurableSpace X] (p : Public) (cfg : Config)
    (x : X → Point p.d) (v : X → Reply p) (fallback : X → Point p.d × Point p.m)
    (hx : Measurable x) (hv : Measurable v) (hf : Measurable fallback) :
    Measurable (fun z => (validate p cfg (x z) (v z)).getD (fallback z)) := by
  classical
  let J := fun z => LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc (v z).2.2)
  let lm := fun z => thresholdedMultiplier p.ν (J z) (clip cfg.gradientCap (v z).1)
  have hlm : Measurable lm := (measurable_validator_multiplier p cfg).comp hv
  have hs := measurableSet_validation_test p cfg v hv
  have he : (fun z => (validate p cfg (x z) (v z)).getD (fallback z)) =
      fun z => if regular (p.ν / 2) (J z) ∧
        ‖(v z).1 + J z (lm z)‖ ^ 2 + ‖(v z).2.1‖ ^ 2 ≤ p.ε ^ 2 / 16 then
        (x z, lm z) else fallback z := by
    funext z
    simp only [validate, J, lm]
    split_ifs <;> rfl
  rw [he]
  exact (hx.prodMk hlm).ite hs hf

lemma measurableSet_validate_none {X : Type*} [MeasurableSpace X] (p : Public) (cfg : Config)
    (x : X → Point p.d) (v : X → Reply p) (hv : Measurable v) :
    MeasurableSet {z | validate p cfg (x z) (v z) = none} := by
  classical
  let J := fun z => LongTails.Algorithms.MatrixPolar.operatorEquiv p.d p.m (clip p.Lc (v z).2.2)
  let lm := fun z => thresholdedMultiplier p.ν (J z) (clip cfg.gradientCap (v z).1)
  have hs := measurableSet_validation_test p cfg v hv
  have he : {z | validate p cfg (x z) (v z) = none} =
      {z | regular (p.ν / 2) (J z) ∧
        ‖(v z).1 + J z (lm z)‖ ^ 2 + ‖(v z).2.1‖ ^ 2 ≤ p.ε ^ 2 / 16}ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, validate]
    split_ifs <;> simp_all [J, lm]
  rw [he]
  exact hs.compl

lemma measurable_firstAccepted {X : Type*} [MeasurableSpace X] (p : Public)
    (values : List (X → Option (Point p.d × Point p.m)))
    (hv : ∀ v ∈ values, ∀ f : X → Point p.d × Point p.m, Measurable f →
      Measurable (fun z => (v z).getD (f z)))
    (fallback : X → Point p.d × Point p.m) (hf : Measurable fallback) :
    Measurable (fun z => firstAccepted (fallback z) (values.map (fun v => v z))) := by
  induction values with
  | nil => exact hf
  | cons v values ih =>
    have htail := ih (fun w hw => hv w (List.mem_cons_of_mem v hw))
    have he (z : X) : firstAccepted (fallback z) ((v :: values).map (fun w => w z)) =
        (v z).getD (firstAccepted (fallback z) (values.map (fun w => w z))) := by
      simp only [List.map_cons]
      cases v z <;> rfl
    simp_rw [he]
    exact hv v List.mem_cons_self _ htail

lemma measurable_raw_mean {Ω X : Type*} [MeasurableSpace X]
    (p : Public) (g : Point p.d → Ω → Reply p) (ξ : X → ℕ → Ω)
    (sample : X → Plan p (Reply p) 2)
    (h : ∀ call, Measurable (fun z => QueryPlan.sampledEval g (ξ z) (sample z) call))
    (n call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (meanPlan p n (sample z)) call) := by
  simp_rw [meanPlan, QueryPlan.sampledEval_map, StochasticQuasar.sampled_collect_plans]
  exact (Finset.measurable_sum _ (fun i _ => h (call + 2 * i.val))).const_smul ((n : ℝ)⁻¹)

lemma measurable_raw_pair {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (ξ : X → ℕ → Ω) (hξ : Measurable ξ) (x : X → Point p.d) (hx : Measurable x) (call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (pairedSample p (x z)) call) := by
  simp only [pairedSample, QueryPlan.sampledEval]
  exact hg.comp (hx.prodMk ((measurable_pi_apply call).comp hξ))

lemma measurable_raw_difference {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (ξ : X → ℕ → Ω) (hξ : Measurable ξ) (x y : X → Point p.d)
    (hx : Measurable x) (hy : Measurable y) (call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (pairedDifference p (x z) (y z)) call) := by
  simp only [pairedDifference, QueryPlan.sampledEval]
  exact (hg.comp (hx.prodMk ((measurable_pi_apply call).comp hξ))).sub
    (hg.comp (hy.prodMk ((measurable_pi_apply (call + 1)).comp hξ)))

lemma measurable_raw_robust {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (ξ : X → ℕ → Ω) (hξ : Measurable ξ) (x : X → Point p.d) (hx : Measurable x)
    (t : ℝ) (n k call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (robustPlan p t n k (x z)) call) := by
  simp_rw [LongTails.Algorithms.StochasticEquality.robustPlan, QueryPlan.sampledEval_map,
    StochasticQuasar.sampled_collect_plans]
  have hv (j : Fin k) := measurable_raw_mean p g ξ (fun z => pairedSample p (x z))
    (fun call => measurable_raw_pair p g hg ξ hξ x hx call) n (call + 2 * n * j.val)
  exact ((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
    (Measurable.of_eval fun j => (hv j).fst))).prodMk
      (((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
        (Measurable.of_eval fun j => (hv j).snd.fst))).prodMk
      ((RobustGradient.measurable_pilotCenter k).comp (measurable_const.prodMk
        (Measurable.of_eval fun j => (hv j).snd.snd))))

lemma measurable_raw_estimator {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (s : X → TrainingState p) (hx : Measurable (fun z => (s z).point))
    (hy : Measurable (fun z => (s z).previous))
    (hv : Measurable (fun z => (s z).estimate)) (k call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (estimatorPlan p cfg k (s z)) call) := by
  by_cases h : k % cfg.epoch = 0
  · simp only [estimatorPlan, h, ↓reduceDIte, sampled_cast]
    exact measurable_raw_mean p g ξ _ (fun call => measurable_raw_pair p g hg ξ hξ _ hx call) _ call
  · simp only [estimatorPlan, h, ↓reduceDIte, sampled_cast, QueryPlan.sampledEval_map]
    exact hv.add (measurable_raw_mean p g ξ _
      (fun call => measurable_raw_difference p g hg ξ hξ _ _ hx hy call) _ call)

lemma measurable_raw_training_segment {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (n slot call index : ℕ) (s : X → TrainingState p)
    (hx : Measurable (fun z => (s z).point))
    (hy : Measurable (fun z => (s z).previous))
    (hv : Measurable (fun z => (s z).estimate))
    (hs : Measurable (fun z => (s z).selected)) :
    let output := fun z => QueryPlan.sampledEval g (ξ z)
      (slotPlan (fun k => 2 * batchSize cfg k)
        (fun k u => (estimatorPlan p cfg k u).map (trainingUpdate p cfg k index u)) n slot (s z)) call
    Measurable (fun z => (output z).point) ∧ Measurable (fun z => (output z).previous) ∧
      Measurable (fun z => (output z).estimate) ∧ Measurable (fun z => (output z).selected) := by
  induction n generalizing slot call s with
  | zero => exact ⟨hx, hy, hv, hs⟩
  | succ n ih =>
    dsimp only
    simp only [slotPlan, slotCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    have he := measurable_raw_estimator p cfg g hg ξ hξ s hx hy hv slot call
    have hu := measurable_training_update p cfg slot index s _ hx hs he
    exact ih (slot + 1) (call + 2 * batchSize cfg slot) _ hu.1 hu.2.1 hu.2.2.1 hu.2.2.2

lemma measurable_raw_training_output {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (x : X → Point p.d) (hx : Measurable x) (index : Fin cfg.steps) (call : ℕ) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z) (trainingPlan p cfg index (x z)) call) := by
  simp only [trainingPlan, trainingPrefixPlan, trainingCalls, QueryPlan.sampledEval_map]
  exact (measurable_raw_training_segment p cfg g hg ξ hξ cfg.steps 0 call index
    (fun z => ⟨x z, x z, 0, x z⟩) hx hx measurable_const hx).2.2.2

lemma measurable_raw_restoration_segment {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (n slot call : ℕ) (x : X → Point p.d) (hx : Measurable x) :
    Measurable (fun z => QueryPlan.sampledEval g (ξ z)
      (slotPlan (fun _ => restoreUnitCalls cfg)
        (fun _ u => (LongTails.Algorithms.StochasticEquality.robustPlan p cfg.restoreTolerance
          cfg.restoreBatch cfg.restoreGroups u).map (restoreUpdate p cfg u)) n slot (x z)) call) := by
  induction n generalizing slot call x with
  | zero => exact hx
  | succ n ih =>
    simp only [slotPlan, slotCalls, restoreUnitCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
    have hr := measurable_raw_robust p g hg ξ hξ x hx cfg.restoreTolerance cfg.restoreBatch cfg.restoreGroups call
    exact ih (slot + 1) _ _ ((measurable_restore_update p cfg).comp (hx.prodMk hr))

lemma measurable_raw_trial_getD {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) (ξ : X → ℕ → Ω) (hξ : Measurable ξ)
    (index : Fin cfg.steps) (call : ℕ) (fallback : X → Point p.d × Point p.m)
    (hf : Measurable fallback) :
    Measurable (fun z => (QueryPlan.sampledEval g (ξ z) (trialPlan p cfg index) call).getD (fallback z)) := by
  have hr : Measurable (fun z => QueryPlan.sampledEval g (ξ z) (restorePlan p cfg) call) :=
    measurable_raw_restoration_segment p cfg g hg ξ hξ cfg.restoreSteps 0 call (fun _ => p.x0) measurable_const
  have hx := measurable_raw_training_output p cfg g hg ξ hξ _ hr index (call + restoreCalls cfg)
  have hv := measurable_raw_robust p g hg ξ hξ _ hx cfg.validationTolerance cfg.validationBatch
    cfg.validationGroups (call + restoreCalls cfg + trainingCalls cfg)
  simp only [trialPlan, trialCalls, validationCalls, QueryPlan.sampledEval_bind, QueryPlan.sampledEval_map]
  exact measurable_validate_getD p cfg _ _ fallback hx hv hf

lemma measurable_raw_output {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (cfg : Config) (g : Point p.d → Ω → Reply p)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Seed cfg × (ℕ → Ω) => QueryPlan.sampledEval g z.2 (plan p cfg z.1) 0) := by
  apply measurable_from_prod_countable_right
  intro seed
  let values := List.ofFn fun i : Fin cfg.trials => fun ξ : ℕ → Ω =>
    QueryPlan.sampledEval g ξ (trialPlan p cfg (seed i)) (trialCalls cfg * i.val)
  have hv : ∀ v ∈ values, ∀ f : (ℕ → Ω) → Point p.d × Point p.m,
      Measurable f → Measurable (fun z => (v z).getD (f z)) := by
    intro v hv f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact measurable_raw_trial_getD p cfg g hg id measurable_id (seed i) (trialCalls cfg * i.val) f hf
  have hh := measurable_firstAccepted p values hv (fun _ => (p.x0, 0)) measurable_const
  simpa only [sampled_trials, Nat.zero_add, values, List.map_ofFn, Function.comp_def] using hh

end LongTails.Proofs.StochasticEqualitySampling
