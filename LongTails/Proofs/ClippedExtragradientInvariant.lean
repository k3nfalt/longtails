import LongTails.Algorithms.ClippedExtragradientSamples
import LongTails.Proofs.ClippedExtragradientOuter
import LongTails.Proofs.ClippedExtragradientBudget
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def analysisRoot (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (state : StageState E) : E :=
  regularizedZero F hc hm (regularization t state.1) (regularization_pos t hR hε state.1) state.2.1

def StageGood (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (state : StageState E) : Prop :=
  ‖analysisRoot t hR hε F hc hm state - state.2.2‖ ≤ radius t state.1 ∧
    ‖F (analysisRoot t hR hε F hc hm state)‖ ≤
      (state.1 + 1 : ℕ) * (t.ε / (8 * stageCount t))

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma analysisRoot_spec (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (state : StageState E) :
    HolderMonotone.reg F (regularization t state.1) state.2.1
      (analysisRoot t hR hε F hc hm state) = 0 :=
  regularizedZero_spec F hc hm _ _ _

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma measurable_analysisRoot (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) :
    Measurable (analysisRoot t hR hε F hc hm) := by
  have hf (s : ℕ) : Measurable (fun a : E × E =>
      analysisRoot t hR hε F hc hm (s, a)) :=
    (regularizedZero_continuous F hc hm (regularization t s) (regularization_pos t hR hε s)).measurable.comp
      measurable_fst
  exact measurable_from_prod_countable_right (f := analysisRoot t hR hε F hc hm) hf

omit [CompleteSpace E] in
lemma measurableSet_stageGood (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫) :
    MeasurableSet {state | StageGood t hR hε F hc hm state} := by
  have hr := measurable_analysisRoot t hR hε F hc hm
  have hd : Measurable (fun state : StageState E => radius t state.1) :=
    (measurable_of_countable (radius t)).comp measurable_fst
  have hb : Measurable (fun state : StageState E =>
      (state.1 + 1 : ℕ) * (t.ε / (8 * stageCount t))) := by fun_prop
  exact (measurableSet_le (hr.sub (measurable_snd.comp measurable_snd)).norm hd).inter
    (measurableSet_le (hc.measurable.comp hr).norm hb)

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma stageGood_initial (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (x0 xstar : E) (hstar : F xstar = 0) (hd : ‖x0 - xstar‖ ≤ t.R) :
    StageGood t hR hε F hc hm (0, x0, x0) := by
  have hh := initial_regularized_root t hR hε hm x0 xstar
    (analysisRoot t hR hε F hc hm (0, x0, x0)) hstar hd
    (analysisRoot_spec t hR hε F hc hm (0, x0, x0))
  simpa only [StageGood, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul] using hh

omit [MeasurableSpace Ω] in
omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma stageGood_next (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (g : E → Ω → E) (state : StageState E) (ξ : Fin (stageCost t state) → Ω)
    (hgood : StageGood t hR hε F hc hm state)
    (hclose : ‖blockReply t g (stageCost t state) state ξ -
      analysisRoot t hR hε F hc hm state‖ ≤ radius t state.1 / 2) :
    StageGood t hR hε F hc hm (stageNext t g (stageCost t state) state ξ) := by
  exact transport_stage t hR hε hm state.1 state.2.1
    (blockReply t g (stageCost t state) state ξ)
    (analysisRoot t hR hε F hc hm state)
    (analysisRoot t hR hε F hc hm (stageNext t g (stageCost t state) state ξ))
    (analysisRoot_spec t hR hε F hc hm state)
    (analysisRoot_spec t hR hε F hc hm (stageNext t g (stageCost t state) state ξ)) hclose hgood.2

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma stageGood_signal (t : Tuning) (hR : 0 < t.R) (hε : 0 < t.ε)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (state : StageState E) (hs : state.1 ≤ stageCount t)
    (hgood : StageGood t hR hε F hc hm state) :
    ‖F (analysisRoot t hR hε F hc hm state)‖ ≤ t.ε / 4 := by
  have hT : (1 : ℝ) ≤ stageCount t := by exact_mod_cast (Nat.succ_le_of_lt (stageCount_pos t))
  have hs' : (state.1 : ℝ) ≤ stageCount t := by exact_mod_cast hs
  have hb : (state.1 + 1 : ℕ) * (t.ε / (8 * stageCount t)) ≤ t.ε / 4 := by
    push_cast
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  exact hgood.2.trans hb

end OracleTemplate.ClippedExtragradient
