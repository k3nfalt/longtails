import LongTails.Proofs.AffineSoftmaxSearchOracle
import LongTails.Algorithms.CappedProximal

namespace LongTails.Proofs.AffineSoftmaxPredictor

open LongTails.Algorithms.CappedProximal

lemma ratio_properties {μ A : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) :
    let a := nextWeight μ A
    let q := a / (A + a)
    0 < a ∧ 0 ≤ q ∧ q ≤ 1 ∧ μ * A * q ^ 2 + q = 1 := by
  have ha := CappedProximalGeometry.accelerated_weight_properties hμ hA
  change 0 < nextWeight μ A ∧ μ * (nextWeight μ A) ^ 2 = A + nextWeight μ A at ha
  have hden : 0 < A + nextWeight μ A := by linarith [ha.1]
  refine ⟨ha.1, div_nonneg ha.1.le hden.le, (div_le_one hden).mpr (by linarith), ?_⟩
  apply (mul_right_cancel₀ (show (A + nextWeight μ A) ^ 2 ≠ 0 by positivity))
  field_simp
  nlinarith [congrArg (fun t : ℝ => A * t) ha.2]

lemma predictor_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) (state : State E) {μ : ℝ}
    (hμ : 0 < μ) (hA : 0 ≤ state.weight) (hx : state.primal ∈ C) (hv : state.dual ∈ C) :
    predictor μ state ∈ C := by
  have ha := (ratio_properties hμ hA).1
  have hden : 0 < state.weight + nextWeight μ state.weight := by linarith
  apply hC hx hv (div_nonneg hA hden.le) (div_nonneg ha.le hden.le)
  rw [← add_div, div_self hden.ne']

lemma predictor_ratio_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (state : State E) {μ : ℝ} (hμ : 0 < μ) (hA : 0 ≤ state.weight) :
    predictor μ state =
      (1 - nextWeight μ state.weight / (state.weight + nextWeight μ state.weight)) • state.primal +
      (nextWeight μ state.weight / (state.weight + nextWeight μ state.weight)) • state.dual := by
  have ha := (ratio_properties hμ hA).1
  have hden : state.weight + nextWeight μ state.weight ≠ 0 := by linarith
  have he : state.weight / (state.weight + nextWeight μ state.weight) =
      1 - nextWeight μ state.weight / (state.weight + nextWeight μ state.weight) := by
    field_simp
    ring
  simp only [predictor, he]

lemma predictor_perturbation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (state : State E) {μ ν D : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hA : 0 ≤ state.weight) (hdiam : ‖state.dual - state.primal‖ ≤ D) :
    μ * ‖predictor μ state - predictor ν state‖ ≤ D * |μ - ν| := by
  have hq := ratio_properties hμ hA
  have hp := ratio_properties hν hA
  rw [predictor_ratio_form state hμ hA, predictor_ratio_form state hν hA]
  exact AffineSoftmaxSearch.predictor_center_perturbation hA hμ.le hν.le hq.2.1 hp.2.1
    hq.2.2.2 hp.2.2.2 state.primal state.dual hdiam

lemma nextWeight_measurable {Z : Type*} [MeasurableSpace Z] (μ A : Z → ℝ)
    (hμ : Measurable μ) (hA : Measurable A) : Measurable (fun z => nextWeight (μ z) (A z)) := by
  unfold nextWeight
  exact (measurable_const.add (Real.continuous_sqrt.measurable.comp
    (measurable_const.add ((measurable_const.mul hμ).mul hA)))).div (measurable_const.mul hμ)

lemma predictor_param_measurable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    (state : Z → State E) (μ : Z → ℝ) (hμ : Measurable μ)
    (hA : Measurable (fun z => (state z).weight))
    (hx : Measurable (fun z => (state z).primal)) (hv : Measurable (fun z => (state z).dual)) :
    Measurable (fun z => predictor (μ z) (state z)) := by
  have ha := nextWeight_measurable μ (fun z => (state z).weight) hμ hA
  exact ((hA.div (hA.add ha)).smul hx).add ((ha.div (hA.add ha)).smul hv)

lemma predictor_continuous {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace Z] (state : State E) (hA : 0 ≤ state.weight)
    (μ : Z → ℝ) (hμ : Continuous μ) (hpos : ∀ z, 0 < μ z) :
    Continuous (fun z => predictor (μ z) state) := by
  have ha : Continuous (fun z => nextWeight (μ z) state.weight) := by
    unfold nextWeight
    exact (continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_const.mul hμ).mul continuous_const)))).div
        (continuous_const.mul hμ) (fun z => mul_ne_zero (by norm_num) (hpos z).ne')
  have hden z : state.weight + nextWeight (μ z) state.weight ≠ 0 :=
    (add_pos_of_nonneg_of_pos hA (ratio_properties (hpos z) hA).1).ne'
  exact ((continuous_const.div (continuous_const.add ha) hden).smul continuous_const).add
    ((ha.div (continuous_const.add ha) hden).smul continuous_const)

lemma proximal_predictor_displacement_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : Set E} {f : E → ℝ} {g : E → E}
    (hcompact : IsCompact X) (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X)
    (hg : ∀ x ∈ X, HasGradientAt f (g x) x) {G : ℝ} (hG : 0 ≤ G)
    (hbound : ∀ x ∈ X, ‖g x‖ ≤ G) (state : State E) (hA : 0 ≤ state.weight)
    (hx : state.primal ∈ X) (hv : state.dual ∈ X) {μ : ℝ} (hμ : 0 < μ) :
    ‖AffineSoftmaxRegularization.exactProx X f μ (predictor μ state) - predictor μ state‖ ≤ G / μ := by
  have hy := predictor_mem hf.1 state hμ hA hx hv
  have hu := AffineSoftmaxRegularization.exactProx_spec hcompact ⟨state.primal, hx⟩ hfc μ (predictor μ state)
  have hdiff := SmoothFiniteMaximumGeometry.bounded_gradient_value_difference hf hg hbound hy hu.1
  have hb := AffineSoftmaxOuter.proximal_displacement_bound hf hg hμ hG hy hu.1 hu.2
    ((le_abs_self _).trans hdiff)
  simpa only [norm_sub_rev] using hb

lemma proximal_predictor_modulus {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {X : Set E} {f : E → ℝ} {g : E → E}
    (hcompact : IsCompact X) (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X)
    (hg : ∀ x ∈ X, HasGradientAt f (g x) x) {G D floor cap : ℝ}
    (hG : 0 ≤ G) (hfloor : 0 < floor) (hbound : ∀ x ∈ X, ‖g x‖ ≤ G)
    (state : State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    (hdiam : ‖state.dual - state.primal‖ ≤ D)
    {μ ν : ℝ} (hμ : μ ∈ Set.Icc floor cap) (hν : ν ∈ Set.Icc floor cap) :
    |‖AffineSoftmaxRegularization.exactProx X f μ (predictor μ state) - predictor μ state‖ -
      ‖AffineSoftmaxRegularization.exactProx X f ν (predictor ν state) - predictor ν state‖| ≤
        (2 * D + G / floor) * |μ - ν| / min μ ν := by
  have hμpos := hfloor.trans_le hμ.1
  have hνpos := hfloor.trans_le hν.1
  have hu := AffineSoftmaxRegularization.exactProx_spec hcompact ⟨state.primal, hx⟩ hfc μ (predictor μ state)
  have hw := AffineSoftmaxRegularization.exactProx_spec hcompact ⟨state.primal, hx⟩ hfc ν (predictor ν state)
  have hres := (proximal_predictor_displacement_bound hcompact hf hfc hg hG hbound state hA hx hv hνpos).trans
    (div_le_div_of_nonneg_left hG hfloor hν.1)
  rw [norm_sub_rev] at hres
  have hscaled := AffineSoftmaxSearchGeometry.proximal_displacement_scaled_modulus hf hg hμpos ν D G floor
    (predictor μ state) (predictor ν state) hu.1 hw.1 hu.2 hw.2
    (predictor_perturbation state hμpos hνpos hA hdiam) hres
  rw [norm_sub_rev (predictor μ state), norm_sub_rev (predictor ν state)] at hscaled
  apply (le_div_iff₀ (lt_min hμpos hνpos)).mpr
  have hm := mul_le_mul_of_nonneg_left (min_le_left μ ν)
    (abs_nonneg (‖AffineSoftmaxRegularization.exactProx X f μ (predictor μ state) - predictor μ state‖ -
      ‖AffineSoftmaxRegularization.exactProx X f ν (predictor ν state) - predictor ν state‖))
  nlinarith only [hm, hscaled]

lemma proximal_predictor_displacement_continuous {E Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace Z]
    {X : Set E} {f : E → ℝ} (hcompact : IsCompact X) (hne : X.Nonempty)
    (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X)
    (state : State E) (hA : 0 ≤ state.weight)
    (μ : Z → ℝ) (hμ : Continuous μ) (hpos : ∀ z, 0 < μ z) :
    Continuous (fun z => ‖AffineSoftmaxRegularization.exactProx X f (μ z) (predictor (μ z) state) -
      predictor (μ z) state‖) := by
  have hp := predictor_continuous state hA μ hμ hpos
  exact ((AffineSoftmaxRegularization.exactProx_continuous hcompact hne hf hfc μ
    (fun z => predictor (μ z) state) hμ hp hpos).sub hp).norm

end LongTails.Proofs.AffineSoftmaxPredictor
