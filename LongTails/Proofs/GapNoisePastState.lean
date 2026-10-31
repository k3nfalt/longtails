import LongTails.Algorithms.GapNoisePastExtragradient
import LongTails.Proofs.MultiplicativeRobustSampling
import LongTails.Proofs.MultiplicativeRobustClipping

open MeasureTheory

namespace LongTails.Proofs.GapNoisePastState

open LongTails.Algorithms.GapNoisePastExtragradient

variable {E : Type}

private def encode (state : StageState E) : E × E × E × ℝ × ℝ × E × Bool :=
  (state.base, state.previousQuery, state.previousReply, state.pilotDenominator,
    state.previousStep, state.total, state.active)

instance [MeasurableSpace E] : MeasurableSpace (StageState E) :=
  MeasurableSpace.comap encode inferInstance

variable [MeasurableSpace E]

@[fun_prop] lemma measurable_base : Measurable (StageState.base (E := E)) :=
  measurable_fst.comp (comap_measurable encode)

@[fun_prop] lemma measurable_previousQuery : Measurable (StageState.previousQuery (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable encode))

@[fun_prop] lemma measurable_previousReply : Measurable (StageState.previousReply (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encode)))

@[fun_prop] lemma measurable_pilotDenominator : Measurable (StageState.pilotDenominator (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (comap_measurable encode))))

@[fun_prop] lemma measurable_previousStep : Measurable (StageState.previousStep (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (comap_measurable encode)))))

@[fun_prop] lemma measurable_total : Measurable (StageState.total (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encode))))))

@[fun_prop] lemma measurable_active : Measurable (StageState.active (E := E)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encode))))))

@[fun_prop] lemma measurable_state_mk {A : Type*} [MeasurableSpace A]
    {w x g total : A → E} {pilot η : A → ℝ} {active : A → Bool}
    (hw : Measurable w) (hx : Measurable x) (hg : Measurable g)
    (hp : Measurable pilot) (hη : Measurable η) (ht : Measurable total) (ha : Measurable active) :
    Measurable (fun a => StageState.mk (w a) (x a) (g a) (pilot a) (η a) (total a) (active a)) := by
  apply measurable_comap_iff.mpr
  exact hw.prodMk (hx.prodMk (hg.prodMk (hp.prodMk (hη.prodMk (ht.prodMk ha)))))

private def encodeConfig (c : StageConfig (E := E)) : ℝ × ℝ × ℝ × ℝ × E × E :=
  (c.curvature, c.scale, c.radius, c.regularization, c.anchor, c.center)

instance : MeasurableSpace (StageConfig (E := E)) :=
  MeasurableSpace.comap encodeConfig inferInstance

@[fun_prop] lemma measurable_config_curvature : Measurable (StageConfig.curvature (E := E)) :=
  measurable_fst.comp (comap_measurable encodeConfig)

@[fun_prop] lemma measurable_config_scale : Measurable (StageConfig.scale (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable encodeConfig))

@[fun_prop] lemma measurable_config_radius : Measurable (StageConfig.radius (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encodeConfig)))

@[fun_prop] lemma measurable_config_regularization : Measurable (StageConfig.regularization (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encodeConfig))))

@[fun_prop] lemma measurable_config_anchor : Measurable (StageConfig.anchor (E := E)) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encodeConfig)))))

@[fun_prop] lemma measurable_config_center : Measurable (StageConfig.center (E := E)) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable encodeConfig)))))

@[fun_prop] lemma measurable_config_mk {A : Type*} [MeasurableSpace A]
    {b S d r : A → ℝ} {anchor center : A → E}
    (hb : Measurable b) (hS : Measurable S) (hd : Measurable d) (hr : Measurable r)
    (ha : Measurable anchor) (hc : Measurable center) :
    Measurable (fun a => StageConfig.mk (b a) (S a) (d a) (r a) (anchor a) (center a)) := by
  apply measurable_comap_iff.mpr
  exact hb.prodMk (hS.prodMk (hd.prodMk (hr.prodMk (ha.prodMk hc))))

@[fun_prop] lemma measurable_nextStep : Measurable (nextStep (E := E)) := by
  unfold nextStep
  fun_prop

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]

@[fun_prop] lemma measurable_regularizedReply (c : StageConfig (E := E)) :
    Measurable (Function.uncurry (regularizedReply c)) := by
  unfold regularizedReply Function.uncurry
  fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_pilotScale (c : StageConfig (E := E)) :
    Measurable (pilotDenominator c) := by
  unfold pilotDenominator
  fun_prop

@[fun_prop] lemma measurable_clippedReply (c : StageConfig (E := E)) :
    Measurable (Function.uncurry (clippedReply c)) := by
  unfold clippedReply Function.uncurry
  have hm : Measurable (fun w : ℝ × E => 1 / (1024 * c.curvature * w.1)) := by fun_prop
  exact OracleTemplate.MultiplicativeRobustEstimator.measurable_variable_clip.comp
    (hm.prodMk measurable_snd)

@[fun_prop] lemma measurable_initialState (c : StageConfig (E := E)) :
    Measurable (Function.uncurry (initialState c)) := by
  unfold initialState initialWithDenominator Function.uncurry
  apply measurable_state_mk <;> fun_prop

@[fun_prop] lemma measurable_updatedState {A : Type*} [MeasurableSpace A]
    (c : StageConfig (E := E)) {state : A → StageState E} {x pilot raw nextBase : A → E}
    (hs : Measurable state) (hx : Measurable x) (hp : Measurable pilot)
    (hr : Measurable raw) (hb : Measurable nextBase) :
    Measurable (fun a => updatedState c (state a) (x a) (pilot a) (raw a) (nextBase a)) := by
  unfold updatedState
  apply measurable_state_mk <;> fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurableSet_permitted {A : Type*} [MeasurableSpace A] (c : StageConfig (E := E))
    {state : A → StageState E} {x : A → E} (hs : Measurable state) (hx : Measurable x) :
    MeasurableSet {a | permitted c (state a) (x a)} := by
  have ha : MeasurableSet {a | (state a).active = true} := by
    change MeasurableSet ((StageState.active ∘ state) ⁻¹' {true})
    exact (measurable_active.comp hs) (measurableSet_singleton true)
  unfold permitted
  have hw : Measurable (fun a => ‖(state a).base - c.center‖) := by fun_prop
  have hx' : Measurable (fun a => ‖x a - c.center‖) := by fun_prop
  exact ha.inter ((measurableSet_le hw measurable_const).inter
    (measurableSet_le hx' measurable_const))

@[fun_prop] lemma measurable_advance {A : Type*} [MeasurableSpace A]
    (proj : E → E) (hproj : Measurable proj) (c : StageConfig (E := E))
    {state : A → StageState E} {x pilot raw : A → E}
    (hs : Measurable state) (hx : Measurable x) (hp : Measurable pilot) (hr : Measurable raw) :
    Measurable (fun a => advance proj c (state a) (x a) (pilot a) (raw a)) := by
  classical
  unfold advance
  apply Measurable.ite (measurableSet_permitted c hs hx)
  · apply measurable_updatedState c hs hx hp hr
    fun_prop
  · apply measurable_state_mk <;> fun_prop

omit [SecondCountableTopology E] in
@[fun_prop] lemma measurable_trialOutput (c : StageConfig (E := E)) (steps : ℕ) :
    Measurable (trialOutput c steps) := by
  unfold trialOutput
  apply Measurable.ite
  · change MeasurableSet (StageState.active ⁻¹' {true})
    exact measurable_active (E := E) (measurableSet_singleton true)
  · fun_prop
  · fun_prop

@[fun_prop] lemma measurable_predictor {proj : E → E} (hp : Measurable proj) :
    Measurable (predictor proj) := by
  unfold predictor
  fun_prop

@[fun_prop] lemma measurable_regularizedReply_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {x raw : A → E}
    (hc : Measurable c) (hx : Measurable x) (hr : Measurable raw) :
    Measurable (fun a => regularizedReply (c a) (x a) (raw a)) := by
  unfold regularizedReply
  fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_pilotDenominator_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {pilot : A → E}
    (hc : Measurable c) (hp : Measurable pilot) :
    Measurable (fun a => pilotDenominator (c a) (pilot a)) := by
  unfold pilotDenominator
  fun_prop

@[fun_prop] lemma measurable_clippedReply_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {η : A → ℝ} {reply : A → E}
    (hc : Measurable c) (hη : Measurable η) (hr : Measurable reply) :
    Measurable (fun a => clippedReply (c a) (η a) (reply a)) := by
  unfold clippedReply
  have hm : Measurable (fun a => 1 / (1024 * (c a).curvature * η a)) := by fun_prop
  exact OracleTemplate.MultiplicativeRobustEstimator.measurable_variable_clip.comp (hm.prodMk hr)

@[fun_prop] lemma measurable_initialState_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {pilot raw : A → E}
    (hc : Measurable c) (hp : Measurable pilot) (hr : Measurable raw) :
    Measurable (fun a => initialState (c a) (pilot a) (raw a)) := by
  unfold initialState initialWithDenominator
  apply measurable_state_mk <;> fun_prop

@[fun_prop] lemma measurable_updatedState_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {state : A → StageState E} {x pilot raw nextBase : A → E}
    (hc : Measurable c) (hs : Measurable state) (hx : Measurable x) (hp : Measurable pilot)
    (hr : Measurable raw) (hb : Measurable nextBase) :
    Measurable (fun a => updatedState (c a) (state a) (x a) (pilot a) (raw a) (nextBase a)) := by
  unfold updatedState
  apply measurable_state_mk <;> fun_prop

omit [InnerProductSpace ℝ E] in
lemma measurableSet_permitted_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {state : A → StageState E} {x : A → E}
    (hc : Measurable c) (hs : Measurable state) (hx : Measurable x) :
    MeasurableSet {a | permitted (c a) (state a) (x a)} := by
  have ha : MeasurableSet {a | (state a).active = true} :=
    (measurable_active.comp hs) (measurableSet_singleton true)
  unfold permitted
  have hw : Measurable (fun a => ‖(state a).base - (c a).center‖) := by fun_prop
  have hx' : Measurable (fun a => ‖x a - (c a).center‖) := by fun_prop
  have hd : Measurable (fun a => 64 * (c a).radius) := by fun_prop
  exact ha.inter ((measurableSet_le hw hd).inter (measurableSet_le hx' hd))

@[fun_prop] lemma measurable_advance_of {A : Type*} [MeasurableSpace A]
    {proj : E → E} (hproj : Measurable proj)
    {c : A → StageConfig (E := E)} {state : A → StageState E} {x pilot raw : A → E}
    (hc : Measurable c) (hs : Measurable state) (hx : Measurable x)
    (hp : Measurable pilot) (hr : Measurable raw) :
    Measurable (fun a => advance proj (c a) (state a) (x a) (pilot a) (raw a)) := by
  classical
  unfold advance
  apply Measurable.ite (measurableSet_permitted_of hc hs hx)
  · apply measurable_updatedState_of hc hs hx hp hr
    fun_prop
  · apply measurable_state_mk <;> fun_prop

omit [SecondCountableTopology E] in
@[fun_prop] lemma measurable_trialOutput_of {A : Type*} [MeasurableSpace A]
    {c : A → StageConfig (E := E)} {state : A → StageState E}
    (hc : Measurable c) (hs : Measurable state) (steps : ℕ) :
    Measurable (fun a => trialOutput (c a) steps (state a)) := by
  unfold trialOutput
  apply Measurable.ite
  · exact (measurable_active.comp hs) (measurableSet_singleton true)
  · fun_prop
  · fun_prop

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pilotDenominator_pos (c : StageConfig (E := E)) (estimate : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) : 0 < pilotDenominator c estimate := by
  unfold pilotDenominator
  positivity

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
lemma nextStep_pos (state : StageState E) (hη : 0 < state.previousStep)
    (hp : 0 < state.pilotDenominator) : 0 < nextStep state := by
  unfold nextStep
  positivity

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma clippedReply_cap (c : StageConfig (E := E)) (reply : E) {η : ℝ}
    (hb : 0 < c.curvature) (hη : 0 < η) :
    c.curvature * η * ‖clippedReply c η reply‖ ≤ 1 / 1024 := by
  unfold clippedReply
  have hn := OracleTemplate.norm_clip_le (by positivity : 0 ≤ 1 / (1024 * c.curvature * η)) reply
  calc
    c.curvature * η * ‖OracleTemplate.clip (1 / (1024 * c.curvature * η)) reply‖ ≤
        c.curvature * η * (1 / (1024 * c.curvature * η)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 1 / 1024 := by field_simp

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pilotDenominator_comparable (c : StageConfig (E := E)) (estimate u : E)
    (hb : 0 < c.curvature) (hS : 0 ≤ c.scale)
    (herror : ‖estimate - u‖ ≤ (‖u‖ + c.scale / c.curvature) / 8) :
    c.scale + c.curvature * (‖u‖ + c.scale / c.curvature) ≤ pilotDenominator c estimate ∧
      pilotDenominator c estimate ≤ 3 * (c.scale + c.curvature * (‖u‖ + c.scale / c.curvature)) := by
  have h1 := norm_add_le (estimate - u) u
  rw [sub_add_cancel] at h1
  have h2 := norm_add_le (u - estimate) estimate
  rw [sub_add_cancel, norm_sub_rev u estimate] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 hb.le
  have h2' := mul_le_mul_of_nonneg_left h2 hb.le
  have he := mul_le_mul_of_nonneg_left herror hb.le
  have hH : 0 ≤ c.scale / c.curvature := div_nonneg hS hb.le
  have hu : 0 ≤ c.curvature * ‖u‖ := by positivity
  have hh : 0 ≤ c.curvature * (c.scale / c.curvature) := mul_nonneg hb.le hH
  unfold pilotDenominator
  constructor <;> nlinarith

end LongTails.Proofs.GapNoisePastState
