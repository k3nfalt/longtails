import LongTails.Proofs.GapNoiseFinal
import LongTails.Proofs.GapNoiseStageConfidence
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.GapNoiseProcess

open OracleTemplate OracleTemplate.ConstrainedMonotone
open OracleTemplate.ProjectedClippedExtragradient (ProcessState analysisRoot)
open LongTails.Algorithms.GapNoisePastExtragradient
open OracleTemplate.StochasticGeneralized (accumulated blockTrace)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def finalError (t : Tuning) (F : E → E) (g : E → Ω → E)
    (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : E :=
  if hn : n = finalCalls t then
    finalBlockEstimate t state.2.2 g (fun i => ξ (Fin.cast hn.symm i)) - F state.2.2 else 0

variable [FiniteDimensional ℝ E]

noncomputable def phaseFailure {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : E)
    (g : E → Ω → E) (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : ℝ := by
  classical
  exact if state.1 < stages t ∧ GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s state ∧
      ProjectedClippedExtragradient.radius (geometry t) state.1 / 2 < ‖phaseReply P t g n state ξ -
        analysisRoot hP (geometry t) hF hR hε hx0 (min state.1 (stages t - 1)) state.2.1‖ then 1
    else if state.1 = stages t ∧ GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s state ∧
      t.ε / 32 < ‖finalError t F g n state ξ‖ then 1 else 0

lemma phaseFailure_bounds {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : E)
    (g : E → Ω → E) (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) :
    0 ≤ phaseFailure hP t hF hR hε hx0 s g n state ξ ∧
      phaseFailure hP t hF hR hε hx0 s g n state ξ ≤ 1 := by
  unfold phaseFailure
  split_ifs <;> norm_num

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

omit [FiniteDimensional ℝ E] in
lemma measurable_finalError {F : E → E} (hF : Measurable F) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) [SecondCountableTopology E] :
    Measurable (Function.uncurry (finalError t F g n)) := by
  change Measurable (fun w : ProcessState E × (Fin n → Ω) => finalError t F g n w.1 w.2)
  by_cases hn : n = finalCalls t
  · subst n
    simp only [finalError, dite_true, Fin.cast_refl, id_eq]
    exact ((GapNoiseSampling.measurable_finalBlockEstimate_joint hg t).comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).sub
        (hF.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  · simp only [finalError, hn, dite_false]
    exact measurable_const

lemma measurable_phaseFailure {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (s : E)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (phaseFailure hP t hF hR hε hx0 s g n)) := by
  classical
  have hp := (ProjectedClippedExtragradient.measurable_processRoot hP (geometry t) hF hR hε hx0).comp
    (measurable_fst : Measurable (Prod.fst : ProcessState E × (Fin n → Ω) → ProcessState E))
  have hgood := (GapNoiseOuter.measurableSet_refinedGood hP (geometry t) hF hR hε hx0 s).preimage
    (measurable_fst : Measurable (Prod.fst : ProcessState E × (Fin n → Ω) → ProcessState E))
  have hr : Measurable (fun w : ProcessState E × (Fin n → Ω) =>
      ProjectedClippedExtragradient.radius (geometry t) w.1.1 / 2) :=
    (((measurable_of_countable (ProjectedClippedExtragradient.radius (geometry t))).comp measurable_fst).comp
      measurable_fst).div_const 2
  have hbad := measurableSet_lt hr
    (((GapNoiseSampling.measurable_phaseReply hP.lipschitz.continuous.measurable hg t n).sub hp).norm)
  have hi : MeasurableSet {w : ProcessState E × (Fin n → Ω) | w.1.1 < stages t} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hf : MeasurableSet {w : ProcessState E × (Fin n → Ω) |
      w.1.1 = stages t ∧ t.ε / 32 < ‖finalError t F g n w.1 w.2‖} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_finalError hF.cont.measurable hg t n).norm)
  have hf' : MeasurableSet {w : ProcessState E × (Fin n → Ω) |
      w.1.1 = stages t ∧ GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s w.1 ∧
        t.ε / 32 < ‖finalError t F g n w.1 w.2‖} := by
    convert hf.inter hgood using 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    tauto
  exact Measurable.ite (hi.inter (hgood.inter hbad)) measurable_const
    (Measurable.ite hf' measurable_const measurable_const)

lemma phaseFailure_mean {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε) (hv : 0 ≤ t.v)
    {x0 s : E} (hx0 : x0 ∈ X) (hs : s ∈ X) (hns : Normal X s (-F s)) (hG : ‖F s‖ ≤ t.G)
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator Q X F g s t.σ t.v)
    (state : ProcessState E) :
    (∫ ξ, phaseFailure hP t hF hR hε hx0 s g (phaseCost t state) state ξ
      ∂Measure.pi (fun _ : Fin (phaseCost t state) => Q)) ≤ (1 / 2 : ℝ) ^ (outerGroups t + 1) := by
  classical
  by_cases hgood : GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s state
  · by_cases hj : state.1 < stages t
    · have hne : state.1 ≠ stages t := Nat.ne_of_lt hj
      have hmin : min state.1 (stages t - 1) = state.1 := Nat.min_eq_left (by omega)
      let root := analysisRoot hP (geometry t) hF hR hε hx0 state.1 state.2.1
      let A : Set (Fin (stageCalls t state.1) → Ω) :=
        {ξ | ProjectedClippedExtragradient.radius (geometry t) state.1 / 2 <
          ‖stageBlockOutput P t state.1 state.2.1 state.2.2 g ξ - root‖}
      have hA : MeasurableSet A := measurableSet_lt measurable_const
        (((GapNoiseSampling.measurable_stageBlockOutput_joint hP.lipschitz.continuous.measurable
          ho.measurable t state.1).comp (measurable_prodMk_left (x := state.2))).sub measurable_const).norm
      generalize hcost : phaseCost t state = n
      have hn : n = stageCalls t state.1 := hcost.symm.trans (ite_eq_left hj)
      clear hcost
      subst n
      have he : (fun ξ => phaseFailure hP t hF hR hε hx0 s g (stageCalls t state.1) state ξ) =
          A.indicator (fun _ => (1 : ℝ)) := by
        funext ξ
        simp only [phaseFailure, hj, hgood, hne, hmin, true_and, false_and, ite_false,
          phaseReply, ite_true, dite_true, Fin.cast_refl, id_eq, A, root, Set.indicator, Set.mem_ofPred_eq]
      rw [he]
      change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (stageCalls t state.1) => Q)) ≤ _
      rw [integral_indicator_one hA]
      have hb := ProjectedClippedExtragradient.stageGood_bounds hP (geometry t) hF hR hε hx0
        hs hns hG state hgood.1
      have hmin' : min state.1 (ProjectedClippedExtragradient.stageCount (geometry t) - 1) = state.1 := hmin
      simp only [hmin'] at hb
      have hp := ProjectedClippedExtragradient.analysisRoot_spec hP (geometry t) hF hR hε hx0 state.1 state.2.1
      have hc := hgood.1.2.1
      change ‖analysisRoot hP (geometry t) hF hR hε hx0 (min state.1 (stages t - 1)) state.2.1 - state.2.2‖ ≤
        (if state.1 < stages t then ProjectedClippedExtragradient.radius (geometry t) (min state.1 (stages t - 1))
         else ProjectedClippedExtragradient.radius (geometry t) (min state.1 (stages t - 1)) / 2) at hc
      simp only [hmin, hj, ite_true] at hc
      have hps := GapNoiseOuter.refinedGood_root_distance hP (geometry t) hF hR hε hx0 state hgood
      change ‖analysisRoot hP (geometry t) hF hR hε hx0 (min state.1 (stages t - 1)) state.2.1 - s‖ ≤ t.R at hps
      simp only [hmin] at hps
      have hh := GapNoiseStageConfidence.stageBlockOutput_confidence Q hP hX t hF.L0_pos h1 hR
        ((norm_nonneg _).trans hG) hε hv state.1 state.2.1 state.2.2 root s hF ho hgood.1.1 hp.1 hs
        hp.2 hns (by simpa only [norm_sub_rev] using hc) hps hG hb.2
        (by have hε' : 0 < (geometry t).ε := hε; dsimp [root]; change _ ≤ (geometry t).ε; linarith [hb.1])
      have hr := ENNReal.toReal_mono (by finiteness) hh
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (outerGroups t + 1)),
        Measure.real, A, root, stageConfig] using hr
    · by_cases hf : state.1 = stages t
      · generalize hcost : phaseCost t state = n
        have hn : n = finalCalls t := hcost.symm.trans (ite_eq_right hj)
        clear hcost
        subst n
        let A : Set (Fin (finalCalls t) → Ω) := {ξ | t.ε / 32 < ‖finalBlockEstimate t state.2.2 g ξ - F state.2.2‖}
        have hA : MeasurableSet A := measurableSet_lt measurable_const
          (((GapNoiseSampling.measurable_finalBlockEstimate_joint ho.measurable t).comp
            (measurable_prodMk_left (x := state.2.2))).sub measurable_const).norm
        have he : (fun ξ => phaseFailure hP t hF hR hε hx0 s g (finalCalls t) state ξ) =
            A.indicator (fun _ => (1 : ℝ)) := by
          funext ξ
          simp [phaseFailure, hf, hgood, finalError, A, Set.indicator]
        rw [he]
        change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (finalCalls t) => Q)) ≤ _
        rw [integral_indicator_one hA]
        have hg' : GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s
            (stages t, state.2.1, state.2.2) := by simpa only [← hf] using hgood
        have hgap := GapNoiseFinal.refinedGood_final_gap hP (geometry t) hF hR hε hx0 hs hns hG
          state.2.1 state.2.2 hg'
        have hh := GapNoiseFinal.finalBlockEstimate_confidence Q t hε hv s state.2.2 ho hgood.1.1 hgap
        have hr := ENNReal.toReal_mono (by finiteness) hh
        simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (outerGroups t + 1)),
          Measure.real, A] using hr
      · have he : (fun ξ => phaseFailure hP t hF hR hε hx0 s g (phaseCost t state) state ξ) =
            fun _ => (0 : ℝ) := by
          funext ξ
          simp [phaseFailure, hj, hf]
        rw [he, integral_zero]
        positivity
  · have he : (fun ξ => phaseFailure hP t hF hR hε hx0 s g (phaseCost t state) state ξ) =
        fun _ => (0 : ℝ) := by
      funext ξ
      simp [phaseFailure, hgood]
    rw [he, integral_zero]
    positivity

lemma accumulated_phase_failure {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (hδ : 0 < t.δ)
    {x0 s : E} (hx0 : x0 ∈ X) (hs : s ∈ X) (hns : Normal X s (-F s)) (hG : ‖F s‖ ≤ t.G)
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator Q X F g s t.σ t.v)
    (state : ProcessState E) :
    (Measure.infinitePi fun _ : ℕ => Q)
      {ξ | 1 ≤ accumulated (phaseCost t) (phaseNext P t g)
        (phaseFailure hP t hF hR hε hx0 s g) (stages t + 1) state ξ} ≤ ENNReal.ofReal t.δ := by
  have hc : Measurable (phaseCost (E := E) t) :=
    (measurable_of_countable (fun j : ℕ => if j < stages t then stageCalls t j else finalCalls t)).comp measurable_fst
  have hh := RobustGradient.accumulated_failure_probability Q hc
    (GapNoiseSampling.measurable_phaseNext hP.lipschitz.continuous.measurable ho.measurable t)
    (measurable_phaseFailure hP t hF hR hε hx0 s ho.measurable)
    (phaseFailure_bounds hP t hF hR hε hx0 s g)
    (phaseFailure_mean hP hX t hF h1 hR hε hv hx0 hs hns hG ho) (stages t + 1) state
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hN : (0 : ℝ) < stages t := Nat.cast_pos.mpr (ProjectedClippedExtragradient.stageCount_pos (geometry t))
  have hN1 : (1 : ℝ) ≤ stages t := by exact_mod_cast ProjectedClippedExtragradient.stageCount_pos (geometry t)
  have hb := (le_div_iff₀ (by positivity : 0 < 2 * (stages t : ℝ))).mp (GapNoiseTuning.outerGroups_confidence t hδ)
  have hm := mul_le_mul_of_nonneg_right (show (stages t : ℝ) + 1 ≤ 2 * stages t by linarith)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (outerGroups t + 1))
  push_cast
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma phaseReply_stage {P : E → E} (t : Tuning) (g : E → Ω → E) (state : ProcessState E)
    (hj : state.1 < stages t) (ξ : Fin (phaseCost t state) → Ω) :
    phaseReply P t g (phaseCost t state) state ξ =
      stageBlockOutput P t state.1 state.2.1 state.2.2 g
        (fun i => ξ (Fin.cast (show stageCalls t state.1 = phaseCost t state from (ite_eq_left hj).symm) i)) := by
  unfold phaseReply
  rw [ite_eq_left hj, dite_eq_left (show phaseCost t state = stageCalls t state.1 from ite_eq_left hj)]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma phaseNext_good {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (g : E → Ω → E) (state : ProcessState E) (hj : state.1 < stages t)
    (ξ : Fin (phaseCost t state) → Ω)
    (hg : GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s state)
    (hclose : ‖phaseReply P t g (phaseCost t state) state ξ -
      analysisRoot hP (geometry t) hF hR hε hx0 state.1 state.2.1‖ ≤
        ProjectedClippedExtragradient.radius (geometry t) state.1 / 2) :
    GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s (phaseNext P t g (phaseCost t state) state ξ) := by
  have hz : phaseReply P t g (phaseCost t state) state ξ ∈ X := by
    rw [phaseReply_stage t g state hj ξ]
    exact GapNoiseSampling.sampledStageOutput_mem hP hX (stageConfig t state.1 state.2.1 state.2.2)
      hg.1.1 g (stageBatch t state.1) (pilotBatch t state.1) (pilotGroups t state.1)
      (stageSteps t state.1) (outerGroups t) (GapNoiseTuning.stageSteps_pos t hF.L0_pos h1 hR hG hε state.1) _
  exact GapNoiseOuter.refinedGood_transition hP (geometry t) hF hR hε hx0 state.1 state.2.1 state.2.2
    (phaseReply P t g (phaseCost t state) state ξ) hj hg hz hclose

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma phaseTrace_index (P : E → E) (t : Tuning) (g : E → Ω → E)
    (state : ProcessState E) (ξ : ℕ → Ω) (k : ℕ) :
    (blockTrace (phaseCost t) (phaseNext P t g) state ξ k).1.1 = state.1 + k := by
  induction k generalizing state ξ with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ k ih =>
    rw [StochasticGeneralized.blockTrace_start_succ, ih]
    simp only [phaseNext]
    omega

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma phaseTrace_good {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hG : 0 ≤ t.G) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (g : E → Ω → E) (state : ProcessState E) (ξ : ℕ → Ω) (k : ℕ)
    (hindex : state.1 + k ≤ stages t)
    (hgood : GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s state)
    (hfailure : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 s g) k state ξ < 1) :
    GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s
      (blockTrace (phaseCost t) (phaseNext P t g) state ξ k).1 := by
  induction k generalizing state ξ with
  | zero => exact hgood
  | succ k ih =>
    have hnonneg := (RobustGradient.accumulated_unit_bounds (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 s g) (phaseFailure_bounds hP t hF hR hε hx0 s g)
      k (phaseNext P t g (phaseCost t state) state (fun i => ξ i))
      (fun i => ξ (phaseCost t state + i))).1
    have hinc := (phaseFailure_bounds hP t hF hR hε hx0 s g (phaseCost t state) state (fun i => ξ i)).1
    rw [accumulated] at hfailure
    have hj : state.1 < stages t := by omega
    have hmin : min state.1 (stages t - 1) = state.1 := Nat.min_eq_left (by omega)
    have hclose : ‖phaseReply P t g (phaseCost t state) state (fun i => ξ i) -
        analysisRoot hP (geometry t) hF hR hε hx0 state.1 state.2.1‖ ≤
          ProjectedClippedExtragradient.radius (geometry t) state.1 / 2 := by
      by_contra hh
      have hh := lt_of_not_ge hh
      have he : phaseFailure hP t hF hR hε hx0 s g (phaseCost t state) state (fun i => ξ i) = 1 := by
        simp only [phaseFailure, hj, hgood, hmin, hh, and_self, ite_true]
      rw [he] at hfailure
      linarith
    rw [StochasticGeneralized.blockTrace_start_succ]
    apply ih
    · change state.1 + 1 + k ≤ stages t
      omega
    · exact phaseNext_good hP hX t hF h1 hR hG hε hx0 g state hj _ hgood hclose
    · linarith

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma phaseTrace_correct {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε) {x0 s : E} (hx0 : x0 ∈ X)
    (hs : s ∈ X) (hns : Normal X s (-F s)) (hG : ‖F s‖ ≤ t.G) (hd : ‖x0 - s‖ ≤ t.R / 2)
    (g : E → Ω → E) (ξ : ℕ → Ω)
    (hfail : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 s g) (stages t + 1) (0, x0, x0) ξ < 1) :
    let y := (blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stages t + 1)).1.2.2
    y ∈ X ∧ ∃ η, Normal X y η ∧ ‖F y + η‖ ≤ t.ε := by
  let tr := blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stages t)
  let st := tr.1
  have hi : st.1 = stages t := by
    simpa only [Nat.zero_add] using phaseTrace_index P t g (0, x0, x0) ξ (stages t)
  have hsplit : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 s g) (stages t + 1) (0, x0, x0) ξ =
      accumulated (phaseCost t) (phaseNext P t g)
        (phaseFailure hP t hF hR hε hx0 s g) (stages t) (0, x0, x0) ξ +
      phaseFailure hP t hF hR hε hx0 s g (phaseCost t st) st (fun i => tr.2 i) := by
    rw [StochasticGeneralized.accumulated_eq_sum, Finset.sum_range_succ,
      ← StochasticGeneralized.accumulated_eq_sum]
  rw [hsplit] at hfail
  have hnon := (phaseFailure_bounds hP t hF hR hε hx0 s g (phaseCost t st) st (fun i => tr.2 i)).1
  have hpre := (RobustGradient.accumulated_unit_bounds (phaseCost t) (phaseNext P t g)
    (phaseFailure hP t hF hR hε hx0 s g) (phaseFailure_bounds hP t hF hR hε hx0 s g)
    (stages t) (0, x0, x0) ξ).1
  have hgood := phaseTrace_good hP hX t hF h1 hR ((norm_nonneg _).trans hG) hε hx0 g (0, x0, x0) ξ (stages t)
    (by simp) (GapNoiseOuter.refinedGood_initial hP (geometry t) hF hR hε hx0 hs hns hd) (by linarith)
  change GapNoiseOuter.RefinedGood hP (geometry t) hF hR hε hx0 s st at hgood
  have hcost : phaseCost t st = finalCalls t := by simp only [phaseCost, hi, lt_self_iff_false, ite_false]
  let samples : Fin (finalCalls t) → Ω := fun i => tr.2 (Fin.cast hcost.symm i)
  have herr : ‖finalError t F g (phaseCost t st) st (fun i => tr.2 i)‖ ≤ t.ε / 32 := by
    by_contra hh
    have hh := lt_of_not_ge hh
    have he : phaseFailure hP t hF hR hε hx0 s g (phaseCost t st) st (fun i => tr.2 i) = 1 := by
      simp [phaseFailure, hi, hgood, hh]
    rw [he] at hfail
    linarith
  have herr' : ‖finalBlockEstimate t st.2.2 g samples - F st.2.2‖ ≤ t.ε / 32 := by
    simpa only [finalError, dite_eq_left hcost] using herr
  have hg' : ProjectedClippedExtragradient.StageGood hP (geometry t) hF hR hε hx0 s
      (stages t, st.2.1, st.2.2) := by simpa only [← hi] using hgood.1
  have hc := GapNoiseFinal.finalBlockOutput_correct hP t hF hR hε hx0 hs hns hG
    st.2.1 st.2.2 hg' g samples herr'
  have hout : (blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stages t + 1)).1.2.2 =
      finalBlockOutput P t st.2.1 st.2.2 g samples := by
    rw [StochasticGeneralized.blockTrace_succ]
    change phaseReply P t g (phaseCost t st) st (fun i => tr.2 i) = _
    unfold phaseReply
    rw [ite_eq_right (by omega : ¬ st.1 < stages t), dite_eq_left hcost]
  simpa only [hout] using hc

end LongTails.Proofs.GapNoiseProcess
