import LongTails.Proofs.StochasticMfcqEstimator

open MeasureTheory

namespace LongTails.Proofs.StochasticMfcqMeasurability

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq

lemma measurable_vectors (p : Params) : Measurable (vectors p) := by
  classical
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · change Measurable (fun v : Primitive p => if active p v j then v.2.2 j else v.1)
    apply Measurable.ite
    · unfold active
      exact measurableSet_le measurable_const (by fun_prop)
    · fun_prop
    · exact measurable_fst

lemma measurable_coefficients (p : Params) : Measurable (coefficients p) :=
  (FiniteHullDirection.measurable_weights (hullSteps p)).comp (measurable_vectors p)

lemma measurable_residual (p : Params) : Measurable (residual p) :=
  FiniteHullDirection.measurable_point.comp
    ((measurable_vectors p).prodMk (measurable_coefficients p))

lemma measurable_direction (p : Params) : Measurable (direction p) :=
  (((measurable_residual p).norm.inv).smul (measurable_residual p)).neg

lemma measurable_constraintWeight (p : Params) (i : Fin p.m) :
    Measurable (fun v => constraintWeight p v i) := by
  classical
  unfold constraintWeight
  apply Measurable.ite
  · unfold active
    exact measurableSet_le measurable_const (by fun_prop)
  · exact (measurable_pi_apply i.succ).comp (measurable_coefficients p)
  · exact measurable_const

lemma measurable_objectiveWeight (p : Params) : Measurable (objectiveWeight p) := by
  classical
  unfold objectiveWeight
  apply ((measurable_pi_apply 0).comp (measurable_coefficients p)).add
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · unfold active
    exact measurableSet_le measurable_const (by fun_prop)
  · exact measurable_const
  · exact (measurable_pi_apply i.succ).comp (measurable_coefficients p)

lemma measurable_multipliers (p : Params) : Measurable (multipliers p) := by
  unfold multipliers
  apply (PiLp.continuous_toLp 2 (fun _ : Fin p.m => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_constraintWeight p i).div (measurable_objectiveWeight p)

lemma measurable_robustEstimate (p : Params) : Measurable (robustEstimate p) := by
  exact (jointEquiv p).symm.continuous.measurable.comp
    ((OracleTemplate.RobustGradient.measurable_pilotCenter (replicas p)).comp
      (measurable_const.prodMk measurable_id))

lemma measurable_nextState (p : Params) :
    Measurable (Function.uncurry (nextState p)) := by
  have hv : Measurable (fun z : State p × (Fin (replicas p) → JointSpace p) =>
      robustEstimate p z.2) := (measurable_robustEstimate p).comp measurable_snd
  unfold nextState
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop
  · apply Measurable.ite
    · exact measurableSet_le ((measurable_residual p).comp hv).norm measurable_const
    · exact measurable_fst.fst.prodMk (measurable_fst.fst.prodMk
        (measurable_snd.prodMk (measurable_const.prodMk ((measurable_multipliers p).comp hv))))
    · exact (measurable_fst.fst.add (((measurable_direction p).comp hv).const_smul _)).prodMk
        (measurable_fst.fst.prodMk (measurable_snd.prodMk (measurable_const.prodMk measurable_const)))

lemma continuous_gradient (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : Continuous (gradient I.f) := by
  have hH : 0 ≤ p.H := by linarith [hp.2.1]
  apply (LipschitzWith.of_dist_le_mul (K := ⟨p.H, hH⟩) ?_).continuous
  intro x y
  simp only [dist_eq_norm]
  change ‖gradient I.f x - gradient I.f y‖ ≤ p.H * ‖x - y‖
  exact H.gradientLipschitz x y

lemma continuous_constraint (p : Params) (I : Problem p) (H : Regularity p I)
    (i : Fin p.m) : Continuous (fun x => I.c x i) :=
  continuous_iff_continuousAt.mpr (fun x => (H.constraintGradient x i).differentiableAt.continuousAt)

lemma continuous_jacobian_row (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (i : Fin p.m) : Continuous (fun x => I.J x i) := by
  have hH : 0 ≤ p.H := by linarith [hp.2.1]
  apply (LipschitzWith.of_dist_le_mul (K := ⟨p.H, hH⟩) ?_).continuous
  intro x y
  simp only [dist_eq_norm]
  change ‖I.J x i - I.J y i‖ ≤ p.H * ‖x - y‖
  exact H.jacobianLipschitz x y i

lemma measurableSet_feasible (p : Params) (I : Problem p) (H : Regularity p I) :
    MeasurableSet {x | feasible p I x} := by
  simp only [feasible, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (continuous_constraint p I H i).measurable
    measurable_const)

def validQueryState (p : Params) (I : Problem p) (s : State p) : Prop :=
  feasible p I s.1 ∧ feasible p I s.2.1 ∧ ‖s.1 - s.2.1‖ ≤ stepSize p

lemma measurableSet_validQueryState (p : Params) (I : Problem p) (H : Regularity p I) :
    MeasurableSet {s | validQueryState p I s} := by
  exact ((measurableSet_feasible p I H).preimage measurable_fst).inter
    (((measurableSet_feasible p I H).preimage measurable_snd.fst).inter
      (measurableSet_le (measurable_fst.sub measurable_snd.fst).norm measurable_const))

lemma initial_validQueryState (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) : validQueryState p I (initial p) := by
  refine ⟨H.initialFeasible, H.initialFeasible, ?_⟩
  simpa [initial] using (StochasticMfcqTuning.stepSize_pos p hp).le

lemma next_validQueryState (p : Params) (I : Problem p) (hp : spec.valid p)
    (s : State p) (estimates : Fin (replicas p) → JointSpace p)
    (hs : feasible p I s.1) (hn : feasible p I (nextState p s estimates).1) :
    validQueryState p I (nextState p s estimates) := by
  refine ⟨hn, ?_, ?_⟩
  · rw [StochasticMfcqPath.next_previous]
    exact hs
  · rw [StochasticMfcqPath.next_previous]
    exact StochasticMfcqPath.next_displacement p hp s estimates

end LongTails.Proofs.StochasticMfcqMeasurability
