import LongTails.Proofs.ProjectedClippedInvariant
import LongTails.Proofs.ProjectedClippedSampling
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ProjectedClippedExtragradient

open ConstrainedMonotone
open StochasticGeneralized (accumulated blockTrace)

variable {E : Type} {Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def finalError (t : Tuning) (F : E → E) (g : E → Ω → E)
    (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : E :=
  if hn : n = finalCalls t then
    finalEstimate t state.2.2 g (fun i => ξ (Fin.cast hn.symm i)) - F state.2.2 else 0

variable [FiniteDimensional ℝ E]

noncomputable def phaseFailure {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (xstar : E)
    (g : E → Ω → E) (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) : ℝ := by
  classical
  exact if state.1 < stageCount t ∧ StageGood hP t hF hR hε hx0 xstar state ∧
      radius t state.1 / 2 < ‖phaseReply P t g n state ξ -
        analysisRoot hP t hF hR hε hx0 (min state.1 (stageCount t - 1)) state.2.1‖ then 1
    else if state.1 = stageCount t ∧ t.ε / 32 < ‖finalError t F g n state ξ‖ then 1 else 0

lemma phaseFailure_bounds {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (xstar : E)
    (g : E → Ω → E) (n : ℕ) (state : ProcessState E) (ξ : Fin n → Ω) :
    0 ≤ phaseFailure hP t hF hR hε hx0 xstar g n state ξ ∧
      phaseFailure hP t hF hR hε hx0 xstar g n state ξ ≤ 1 := by
  unfold phaseFailure
  split_ifs <;> norm_num

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [FiniteDimensional ℝ E] in
lemma measurable_finalError {F : E → E} (hF : Measurable F) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (finalError t F g n)) := by
  change Measurable (fun w : ProcessState E × (Fin n → Ω) => finalError t F g n w.1 w.2)
  by_cases hn : n = finalCalls t
  · subst n
    simp only [finalError, dite_true, Fin.cast_refl, id_eq]
    exact ((measurable_finalEstimate_joint hg t).comp
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).sub
        (hF.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  · simp only [finalError, hn, dite_false]
    exact measurable_const

lemma measurable_phaseFailure {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 : E} (hx0 : x0 ∈ X) (xstar : E)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (Function.uncurry (phaseFailure hP t hF hR hε hx0 xstar g n)) := by
  classical
  have hp := (measurable_processRoot hP t hF hR hε hx0).comp
    (measurable_fst : Measurable (Prod.fst : ProcessState E × (Fin n → Ω) → ProcessState E))
  have hgood := (measurableSet_stageGood hP t hF hR hε hx0 xstar).preimage
    (measurable_fst : Measurable (Prod.fst : ProcessState E × (Fin n → Ω) → ProcessState E))
  have hr : Measurable (fun w : ProcessState E × (Fin n → Ω) => radius t w.1.1 / 2) :=
    (((measurable_of_countable (radius t)).comp measurable_fst).comp measurable_fst).div_const 2
  have hbad := measurableSet_lt hr
    (((measurable_phaseReply hP.lipschitz.continuous.measurable hg t n).sub hp).norm)
  have hi : MeasurableSet {w : ProcessState E × (Fin n → Ω) | w.1.1 < stageCount t} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hf : MeasurableSet {w : ProcessState E × (Fin n → Ω) |
      w.1.1 = stageCount t ∧ t.ε / 32 < ‖finalError t F g n w.1 w.2‖} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_finalError hF.cont.measurable hg t n).norm)
  exact Measurable.ite (hi.inter (hgood.inter hbad)) measurable_const
    (Measurable.ite hf measurable_const measurable_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma phaseReply_stage {P : E → E} (t : Tuning) (g : E → Ω → E) (state : ProcessState E)
    (hs : state.1 < stageCount t) (ξ : Fin (phaseCost t state) → Ω) :
    phaseReply P t g (phaseCost t state) state ξ =
      blockOutput P t state.1 state.2.1 state.2.2 g
        (fun i => ξ (Fin.cast (show stageCalls t state.1 = phaseCost t state from (ite_eq_left hs).symm) i)) := by
  unfold phaseReply
  rw [ite_eq_left hs, dite_eq_left (show phaseCost t state = stageCalls t state.1 from ite_eq_left hs)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma phaseNext_good {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (g : E → Ω → E) (state : ProcessState E) (hs : state.1 < stageCount t)
    (ξ : Fin (phaseCost t state) → Ω)
    (hgood : StageGood hP t hF hR hε hx0 xstar state)
    (hclose : ‖phaseReply P t g (phaseCost t state) state ξ -
      analysisRoot hP t hF hR hε hx0 state.1 state.2.1‖ ≤ radius t state.1 / 2) :
    StageGood hP t hF hR hε hx0 xstar (phaseNext P t g (phaseCost t state) state ξ) := by
  have hz : phaseReply P t g (phaseCost t state) state ξ ∈ X := by
    rw [phaseReply_stage t g state hs ξ]
    exact blockOutput_mem hP hX t hR state.1 state.2.1 state.2.2 hgood.1 g _
  exact stageGood_transition hP t hF hR hε hx0 state.1 state.2.1 state.2.2
    (phaseReply P t g (phaseCost t state) state ξ) hs hgood hz hclose

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma phaseTrace_index (P : E → E) (t : Tuning) (g : E → Ω → E)
    (state : ProcessState E) (ξ : ℕ → Ω) (k : ℕ) :
    (blockTrace (phaseCost t) (phaseNext P t g) state ξ k).1.1 = state.1 + k := by
  induction k generalizing state ξ with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ k ih =>
    rw [StochasticGeneralized.blockTrace_start_succ, ih]
    simp only [phaseNext]
    omega

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma phaseTrace_good {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (g : E → Ω → E) (state : ProcessState E) (ξ : ℕ → Ω) (k : ℕ)
    (hindex : state.1 + k ≤ stageCount t) (hgood : StageGood hP t hF hR hε hx0 xstar state)
    (hfailure : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 xstar g) k state ξ < 1) :
    StageGood hP t hF hR hε hx0 xstar (blockTrace (phaseCost t) (phaseNext P t g) state ξ k).1 := by
  induction k generalizing state ξ with
  | zero => exact hgood
  | succ k ih =>
    have hnonneg := (RobustGradient.accumulated_unit_bounds (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 xstar g) (phaseFailure_bounds hP t hF hR hε hx0 xstar g)
      k (phaseNext P t g (phaseCost t state) state (fun i => ξ i))
      (fun i => ξ (phaseCost t state + i))).1
    have hinc := (phaseFailure_bounds hP t hF hR hε hx0 xstar g
      (phaseCost t state) state (fun i => ξ i)).1
    rw [accumulated] at hfailure
    have hs : state.1 < stageCount t := by omega
    have hmin : min state.1 (stageCount t - 1) = state.1 := Nat.min_eq_left (by omega)
    have hclose : ‖phaseReply P t g (phaseCost t state) state (fun i => ξ i) -
        analysisRoot hP t hF hR hε hx0 state.1 state.2.1‖ ≤ radius t state.1 / 2 := by
      by_contra hh
      have hh := lt_of_not_ge hh
      have he : phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t state) state (fun i => ξ i) = 1 := by
        simp only [phaseFailure, hs, hgood, hmin, hh, and_self, ite_true]
      rw [he] at hfailure
      linarith
    rw [StochasticGeneralized.blockTrace_start_succ]
    apply ih
    · change state.1 + 1 + k ≤ stageCount t
      omega
    · exact phaseNext_good hP hX t hF hR hε hx0 g state hs _ hgood hclose
    · linarith

variable [CompleteSpace E]

lemma phaseFailure_mean {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    {g : E → Ω → E}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator Q F g t.σ)
    (state : ProcessState E) :
    (∫ ξ, phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t state) state ξ
      ∂Measure.pi (fun _ : Fin (phaseCost t state) => Q)) ≤ (1 / 2 : ℝ) ^ repetitions t := by
  classical
  by_cases hs : state.1 < stageCount t
  · have hne : state.1 ≠ stageCount t := Nat.ne_of_lt hs
    by_cases hgood : StageGood hP t hF hR hε hx0 xstar state
    · have hmin : min state.1 (stageCount t - 1) = state.1 := Nat.min_eq_left (by omega)
      let root := analysisRoot hP t hF hR hε hx0 state.1 state.2.1
      let A : Set (Fin (stageCalls t state.1) → Ω) :=
        {ξ | radius t state.1 / 2 < ‖blockOutput P t state.1 state.2.1 state.2.2 g ξ - root‖}
      have hA : MeasurableSet A := measurableSet_lt measurable_const
        (((measurable_blockOutput_joint hP.lipschitz.continuous.measurable hg.measurable t state.1).comp
          (measurable_prodMk_left (x := state.2))).sub measurable_const).norm
      generalize hcost : phaseCost t state = n
      have hn : n = stageCalls t state.1 := hcost.symm.trans (ite_eq_left hs)
      clear hcost
      subst n
      have he : (fun ξ => phaseFailure hP t hF hR hε hx0 xstar g (stageCalls t state.1) state ξ) =
          A.indicator (fun _ => (1 : ℝ)) := by
        funext ξ
        simp only [phaseFailure, hs, hgood, hne, hmin, true_and, false_and, ite_false,
          phaseReply, ite_true, dite_true, Fin.cast_refl, id_eq, A, root, Set.indicator, Set.mem_ofPred_eq]
      rw [he]
      change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (stageCalls t state.1) => Q)) ≤ _
      rw [integral_indicator_one hA]
      have hb := stageGood_bounds hP t hF hR hε hx0 hstar hnstar hG state hgood
      simp only [hmin] at hb
      have hp := analysisRoot_spec hP t hF hR hε hx0 state.1 state.2.1
      have hc := hgood
      simp only [StageGood, hmin, ite_eq_left hs] at hc
      have hh := blockOutput_confidence hP hX t hF hR ((norm_nonneg (F xstar)).trans hG)
        hε hg state.1 state.2.1 state.2.2 root hp.1 hc.1 hc.2.1 hp.2 hb.2 (by linarith [hb.1])
      have hreal := ENNReal.toReal_mono (by finiteness) hh
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ repetitions t),
        Measure.real, A, root] using hreal
    · have he : (fun ξ => phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t state) state ξ) =
          fun _ => (0 : ℝ) := by
        funext ξ
        simp [phaseFailure, hgood, hne]
      rw [he, integral_zero]
      positivity
  · by_cases hf : state.1 = stageCount t
    · generalize hcost : phaseCost t state = n
      have hn : n = finalCalls t := hcost.symm.trans (ite_eq_right hs)
      clear hcost
      subst n
      let A : Set (Fin (finalCalls t) → Ω) := {ξ | t.ε / 32 < ‖finalEstimate t state.2.2 g ξ - F state.2.2‖}
      have hA : MeasurableSet A := measurableSet_lt measurable_const
        (((measurable_finalEstimate_joint hg.measurable t).comp
          (measurable_prodMk_left (x := state.2.2))).sub measurable_const).norm
      have he : (fun ξ => phaseFailure hP t hF hR hε hx0 xstar g (finalCalls t) state ξ) =
          A.indicator (fun _ => (1 : ℝ)) := by
        funext ξ
        simp [phaseFailure, hf, finalError, A, Set.indicator]
      rw [he]
      change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (finalCalls t) => Q)) ≤ _
      rw [integral_indicator_one hA]
      have hh := ENNReal.toReal_mono (by finiteness) (finalEstimate_confidence t hε hg state.2.2)
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ repetitions t),
        Measure.real, A] using hh
    · have he : (fun ξ => phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t state) state ξ) =
          fun _ => (0 : ℝ) := by
        funext ξ
        simp [phaseFailure, hs, hf]
      rw [he, integral_zero]
      positivity

lemma accumulated_phase_failure {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (hδ : 0 < t.δ) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    {g : E → Ω → E}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator Q F g t.σ)
    (state : ProcessState E) :
    (Measure.infinitePi fun _ : ℕ => Q)
      {ξ | 1 ≤ accumulated (phaseCost t) (phaseNext P t g)
        (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t + 1) state ξ} ≤ ENNReal.ofReal t.δ := by
  have hc : Measurable (phaseCost (E := E) t) :=
    (measurable_of_countable (fun s : ℕ => if s < stageCount t then stageCalls t s else finalCalls t)).comp measurable_fst
  have hh := RobustGradient.accumulated_failure_probability Q hc
    (measurable_phaseNext hP.lipschitz.continuous.measurable hg.measurable t)
    (measurable_phaseFailure hP t hF hR hε hx0 xstar hg.measurable)
    (phaseFailure_bounds hP t hF hR hε hx0 xstar g)
    (phaseFailure_mean hP hX t hF hR hε hx0 hstar hnstar hG hg) (stageCount t + 1) state
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hN : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hN1 : (1 : ℝ) ≤ stageCount t := by exact_mod_cast stageCount_pos t
  have hb := (le_div_iff₀ (by positivity : 0 < 2 * (stageCount t : ℝ))).mp (repetitions_confidence t hδ)
  have hm := mul_le_mul_of_nonneg_right (show (stageCount t : ℝ) + 1 ≤ 2 * stageCount t by linarith)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (repetitions t))
  push_cast
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] [CompleteSpace E] in
lemma finalPhase_correct {X : Set E} {P F : E → E} (hP : Proj X P)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    (g : E → Ω → E) (state : ProcessState E) (hs : state.1 = stageCount t)
    (hgood : StageGood hP t hF hR hε hx0 xstar state) (ξ : Fin (finalCalls t) → Ω)
    (he : ‖finalEstimate t state.2.2 g ξ - F state.2.2‖ ≤ t.ε / 32) :
    finalBlock P t state.2.1 state.2.2 g ξ ∈ X ∧
      ∃ η, Normal X (finalBlock P t state.2.1 state.2.2 g ξ) η ∧
        ‖F (finalBlock P t state.2.1 state.2.2 g ξ) + η‖ ≤ t.ε := by
  have hmin : min state.1 (stageCount t - 1) = stageCount t - 1 := by omega
  have hb := stageGood_bounds hP t hF hR hε hx0 hstar hnstar hG state hgood
  simp only [hmin] at hb
  have hp := analysisRoot_spec hP t hF hR hε hx0 (stageCount t - 1) state.2.1
  have hc := hgood.2.1
  change ‖analysisRoot hP t hF hR hε hx0 (min state.1 (stageCount t - 1)) state.2.1 - state.2.2‖ ≤
    (if state.1 < stageCount t then radius t (min state.1 (stageCount t - 1)) else
      radius t (min state.1 (stageCount t - 1)) / 2) at hc
  rw [hmin] at hc
  simp only [hs, lt_self_iff_false, ite_false] at hc
  have hh := tuned_residual_certificate hP t hF hR ((norm_nonneg (F xstar)).trans hG) hε
    _ state.2.1 state.2.2 (finalEstimate t state.2.2 g ξ - F state.2.2)
    hp.1 hp.2 hb.2 (by simpa only [norm_sub_rev] using hc) he (by linarith [hb.1])
  have heq : F state.2.2 + (finalEstimate t state.2.2 g ξ - F state.2.2) = finalEstimate t state.2.2 g ξ := by abel
  simpa only [heq, finalBlock] using hh

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] [CompleteSpace E] in
lemma phaseTrace_correct {X : Set E} {P F : E → E} (hP : Proj X P) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    (hd : ‖x0 - xstar‖ ≤ t.R) (g : E → Ω → E) (ξ : ℕ → Ω)
    (hfail : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t + 1) (0, x0, x0) ξ < 1) :
    let y := (blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stageCount t + 1)).1.2.2
    y ∈ X ∧ ∃ η, Normal X y η ∧ ‖F y + η‖ ≤ t.ε := by
  let tr := blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stageCount t)
  let st := tr.1
  have hi : st.1 = stageCount t := by
    simpa only [Nat.zero_add] using phaseTrace_index P t g (0, x0, x0) ξ (stageCount t)
  have hsplit : accumulated (phaseCost t) (phaseNext P t g)
      (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t + 1) (0, x0, x0) ξ =
      accumulated (phaseCost t) (phaseNext P t g)
        (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t) (0, x0, x0) ξ +
      phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t st) st (fun i => tr.2 i) := by
    rw [StochasticGeneralized.accumulated_eq_sum, Finset.sum_range_succ,
      ← StochasticGeneralized.accumulated_eq_sum]
  rw [hsplit] at hfail
  have hnon := (phaseFailure_bounds hP t hF hR hε hx0 xstar g (phaseCost t st) st (fun i => tr.2 i)).1
  have hpre := (RobustGradient.accumulated_unit_bounds (phaseCost t) (phaseNext P t g)
    (phaseFailure hP t hF hR hε hx0 xstar g) (phaseFailure_bounds hP t hF hR hε hx0 xstar g)
    (stageCount t) (0, x0, x0) ξ).1
  have hgood := phaseTrace_good hP hX t hF hR hε hx0 g (0, x0, x0) ξ (stageCount t)
    (by simp) (stageGood_initial hP t hF hR hε hx0 hstar hnstar hd) (by linarith)
  have hcost : phaseCost t st = finalCalls t := by simp only [phaseCost, hi, lt_self_iff_false, ite_false]
  let samples : Fin (finalCalls t) → Ω := fun i => tr.2 (Fin.cast hcost.symm i)
  have herr : ‖finalError t F g (phaseCost t st) st (fun i => tr.2 i)‖ ≤ t.ε / 32 := by
    by_contra hh
    have hh := lt_of_not_ge hh
    have he : phaseFailure hP t hF hR hε hx0 xstar g (phaseCost t st) st (fun i => tr.2 i) = 1 := by
      simp [phaseFailure, hi, hh]
    rw [he] at hfail
    linarith
  have herr' : ‖finalEstimate t st.2.2 g samples - F st.2.2‖ ≤ t.ε / 32 := by
    simpa only [finalError, dite_eq_left hcost] using herr
  have hc := finalPhase_correct hP t hF hR hε hx0 hstar hnstar hG g st hi hgood samples herr'
  have hout : (blockTrace (phaseCost t) (phaseNext P t g) (0, x0, x0) ξ (stageCount t + 1)).1.2.2 =
      finalBlock P t st.2.1 st.2.2 g samples := by
    rw [StochasticGeneralized.blockTrace_succ]
    change phaseReply P t g (phaseCost t st) st (fun i => tr.2 i) = _
    unfold phaseReply
    rw [ite_eq_right (by omega : ¬ st.1 < stageCount t), dite_eq_left hcost]
  simpa only [hout] using hc

end OracleTemplate.ProjectedClippedExtragradient
