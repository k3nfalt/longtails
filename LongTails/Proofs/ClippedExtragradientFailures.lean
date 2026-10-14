import LongTails.Proofs.ClippedExtragradientInvariant
import LongTails.Proofs.ClippedExtragradientOracle

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

open StochasticGeneralized (accumulated blockTrace)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def stageFailure (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (g : E → Ω → E) (n : ℕ) (state : StageState E) (ξ : Fin n → Ω) : ℝ := by
  classical
  exact if state.1 < stageCount t ∧ StageGood t hR hε F hc hm state ∧
    radius t state.1 / 2 < ‖blockReply t g n state ξ - analysisRoot t hR hε F hc hm state‖
    then 1 else 0

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stageFailure_bounds (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (g : E → Ω → E) (n : ℕ) (state : StageState E) (ξ : Fin n → Ω) :
    0 ≤ stageFailure t hR hε F hc hm g n state ξ ∧
      stageFailure t hR hε F hc hm g n state ξ ≤ 1 := by
  unfold stageFailure
  split_ifs <;> norm_num

omit [CompleteSpace E] in
lemma measurable_stageFailure (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
     (n : ℕ) :
    Measurable (Function.uncurry (stageFailure t hR hε F hc hm g n)) := by
  have hroot := (measurable_analysisRoot t hR hε F hc hm).comp
    (measurable_fst : Measurable (Prod.fst : StageState E × (Fin n → Ω) → StageState E))
  have hgood := (measurableSet_stageGood t hR hε F hc hm).preimage
    (measurable_fst : Measurable (Prod.fst : StageState E × (Fin n → Ω) → StageState E))
  have hr : Measurable (fun w : StageState E × (Fin n → Ω) => radius t w.1.1 / 2) :=
    (((measurable_of_countable (radius t)).comp measurable_fst).comp measurable_fst).div_const 2
  have hbad := measurableSet_lt hr (((measurable_blockReply hg t n).sub hroot).norm)
  have hi : MeasurableSet {w : StageState E × (Fin n → Ω) | w.1.1 < stageCount t} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  exact Measurable.ite (hi.inter (hgood.inter hbad)) measurable_const measurable_const

lemma stageFailure_mean (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (F : E → E) (hc : Continuous F)
    (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    {g : E → Ω → E} (P : Measure Ω) [IsProbabilityMeasure P]
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (state : StageState E) :
    (∫ ξ, stageFailure t hR hε F hc hm g (stageCost t state) state ξ
      ∂Measure.pi (fun _ : Fin (stageCost t state) => P)) ≤ (1 / 2 : ℝ) ^ repetitions t := by
  classical
  dsimp only [stageCost]
  by_cases hactive : state.1 < stageCount t ∧ StageGood t hR hε F hc hm state
  · let root := analysisRoot t hR hε F hc hm state
    let A : Set (Fin (stageCalls t state.1) → Ω) :=
      {ξ | radius t state.1 / 2 < ‖blockOutput t state.1 state.2.1 state.2.2 g ξ - root‖}
    have hA : MeasurableSet A := measurableSet_lt measurable_const
      (((measurable_blockOutput_joint hg.measurable t state.1).comp
        measurable_prodMk_left).sub measurable_const).norm
    have he : (fun ξ => stageFailure t hR hε F hc hm g (stageCalls t state.1) state ξ) =
        A.indicator (fun _ => (1 : ℝ)) := by
      funext ξ
      simp only [stageFailure, hactive.1, hactive.2, true_and, blockReply, dite_true, Fin.cast_refl, id_eq, Set.indicator, Set.mem_ofPred_eq, A, root]
    rw [he]
    change (∫ ξ, A.indicator 1 ξ ∂Measure.pi (fun _ : Fin (stageCalls t state.1) => P)) ≤ _
    rw [integral_indicator_one hA]
    have hF := stageGood_signal t hR hε F hc hm state hactive.1.le hactive.2
    have hp := blockOutput_confidence t h0 h1 hR hε hc hm hlip hg state.1
      (analysisRoot_spec t hR hε F hc hm state) (by linarith) hactive.2.1
    have hreal := ENNReal.toReal_mono (by finiteness) hp
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ repetitions t),
      Measure.real, A, root, stageCost] using hreal
  · have he : (fun ξ => stageFailure t hR hε F hc hm g (stageCalls t state.1) state ξ) =
        fun _ => (0 : ℝ) := by
      funext ξ
      unfold stageFailure
      split_ifs with h
      · exact False.elim (hactive ⟨h.1, h.2.1⟩)
      · rfl
    erw [he, integral_zero]
    positivity

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stageTrace_index (t : Tuning) (g : E → Ω → E)
    (state : StageState E) (ξ : ℕ → Ω) (k : ℕ) :
    (blockTrace (stageCost t) (stageNext t g) state ξ k).1.1 = state.1 + k := by
  induction k generalizing state ξ with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ k ih =>
      rw [StochasticGeneralized.blockTrace_start_succ, ih]
      simp only [stageNext]
      omega

omit [MeasurableSpace Ω] in
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma stageTrace_good (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (g : E → Ω → E) (state : StageState E) (ξ : ℕ → Ω) (k : ℕ)
    (hindex : state.1 + k ≤ stageCount t) (hgood : StageGood t hR hε F hc hm state)
    (hfailure : accumulated (stageCost t) (stageNext t g)
      (stageFailure t hR hε F hc hm g) k state ξ < 1) :
    StageGood t hR hε F hc hm
      (blockTrace (stageCost t) (stageNext t g) state ξ k).1 := by
  induction k generalizing state ξ with
  | zero => exact hgood
  | succ k ih =>
      have hnonneg := (RobustGradient.accumulated_unit_bounds (stageCost t) (stageNext t g)
        (stageFailure t hR hε F hc hm g) (stageFailure_bounds t hR hε F hc hm g)
        k (stageNext t g (stageCost t state) state (fun i => ξ i))
        (fun i => ξ (stageCost t state + i))).1
      have hinc := (stageFailure_bounds t hR hε F hc hm g
        (stageCost t state) state (fun i => ξ i)).1
      rw [accumulated] at hfailure
      have hclose : ‖blockReply t g (stageCost t state) state (fun i => ξ i) -
          analysisRoot t hR hε F hc hm state‖ ≤ radius t state.1 / 2 := by
        by_contra hh
        have hh := lt_of_not_ge hh
        have hactive : state.1 < stageCount t := by omega
        have he : stageFailure t hR hε F hc hm g (stageCost t state) state (fun i => ξ i) = 1 := by
          simp only [stageFailure, hactive, hgood, hh, and_self, ite_true]
        rw [he] at hfailure
        linarith
      rw [StochasticGeneralized.blockTrace_start_succ]
      apply ih
      · change state.1 + 1 + k ≤ stageCount t
        omega
      · exact stageGood_next t hR hε F hc hm g state _ hgood hclose
      · linarith

lemma accumulated_stage_failure (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (F : E → E) (hc : Continuous F)
    (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    {g : E → Ω → E} (P : Measure Ω) [IsProbabilityMeasure P]
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (hδ : 0 < t.δ) (state : StageState E) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 1 ≤ accumulated (stageCost t) (stageNext t g)
        (stageFailure t hR hε F hc hm g) (stageCount t) state ξ} ≤ ENNReal.ofReal t.δ := by
  have hcost : Measurable (stageCost (E := E) t) :=
    (measurable_of_countable (stageCalls t)).comp measurable_fst
  have hh := RobustGradient.accumulated_failure_probability P hcost
    (measurable_stageNext hg.measurable t)
    (measurable_stageFailure t hR hε F hc hm hg.measurable)
    (stageFailure_bounds t hR hε F hc hm g)
    (stageFailure_mean t h0 h1 hR hε F hc hm hlip P hg) (stageCount t) state
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := repetitions_confidence t hδ
  have hT : (0 : ℝ) < stageCount t := Nat.cast_pos.mpr (stageCount_pos t)
  have hh := (le_div_iff₀ hT).mp hb
  nlinarith

end OracleTemplate.ClippedExtragradient
