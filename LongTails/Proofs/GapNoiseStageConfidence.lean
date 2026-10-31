import LongTails.Proofs.GapNoiseStageDrift
import LongTails.Proofs.GapNoisePilot

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseStageConfidence

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseStopped

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma query_pilot_confidence (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E}
    (c : StageConfig (E := E)) {F : E → E} {g : E → Ω → E} (s x : E) {σ v D : ℝ}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s σ v)
    (hx : x ∈ X) (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hv : 0 ≤ v) (hD : 0 ≤ D) (hxs : ‖x - s‖ ≤ D)
    (hscale : c.curvature * (‖F s‖ + c.regularization * ‖x - c.anchor‖) ≤ c.scale)
    (batch groups : ℕ) (hbatch : 0 < batch)
    (hsize : 2 ^ 20 * (σ ^ 2 / (c.scale / c.curvature) ^ 2 + v * D / (c.scale / c.curvature)) ≤ (batch : ℝ)) :
    (Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin batch => μ)
      {ξ | (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) / 8 <
        ‖pilotFromSamples c g x batch groups ξ - regularizedReply c x (F x)‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  have hgap := GapNoiseStageDrift.query_gap_bound c F x s hb hS hr hxs hscale
  have hvar : (∫ ω, ‖g x ω - F x‖ ^ 2 ∂μ) ≤
      σ ^ 2 + v * D * (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) := by
    have hh := mul_le_mul_of_nonneg_left hgap hv
    nlinarith [ho.variance x hx]
  have hbatchSize := GapNoisePilot.relative_variance_batch hv hD
    (norm_nonneg (regularizedReply c x (F x))) (div_pos hS hb) hsize
  exact GapNoisePilot.sampled_pilot_confidence c x (ho.measurable.comp measurable_prodMk_left)
    (ho.integrable x hx) (ho.unbiased x hx) (ho.variance_integrable x hx) hvar
    hb hS hbatch hbatchSize groups

def GoodPilot (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E) (ξ : StepSamples Ω batch pilotBatch groups) : Prop :=
  permitted c state (predictor proj state) →
    ‖pilotFromSamples c g (predictor proj state) pilotBatch groups ξ.1 -
        regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (‖regularizedReply c (predictor proj state) (F (predictor proj state))‖ + c.scale / c.curvature) / 8

omit [CompleteSpace E] in
lemma measurableSet_goodPilot {proj : E → E} (hproj : Measurable proj) (c : StageConfig (E := E))
    {F : E → E} (hF : Measurable F) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups : ℕ) :
    MeasurableSet {w : StageState E × StepSamples Ω batch pilotBatch groups |
      GoodPilot proj c F g batch pilotBatch groups w.1 w.2} := by
  have hx : Measurable (fun w : StageState E × StepSamples Ω batch pilotBatch groups => predictor proj w.1) :=
    (GapNoisePastState.measurable_predictor hproj).comp measurable_fst
  have hH := (GapNoisePastState.measurable_regularizedReply c).comp (hx.prodMk (hF.comp hx))
  have hp := GapNoiseSampling.measurable_pilotFromSamples c hg hx pilotBatch groups
    (measurable_fst.comp measurable_snd)
  have he := measurableSet_le ((hp.sub hH).norm) ((hH.norm.add_const (c.scale / c.curvature)).div_const 8)
  have hm := (GapNoisePastState.measurableSet_permitted c measurable_fst hx).compl.union he
  convert hm using 1
  ext w
  simp [GoodPilot, imp_iff_not_or]

lemma goodPilot_failure_probability (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {g : E → Ω → E} (s : E) {σ v R : ℝ}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s σ v)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hv : 0 ≤ v) (hR : 0 < R) (hdR : c.radius ≤ R) (hcs : ‖c.center - s‖ ≤ 2 * R)
    (hscale : ∀ x, ‖x - c.center‖ ≤ 64 * c.radius →
      c.curvature * (‖F s‖ + c.regularization * ‖x - c.anchor‖) ≤ c.scale)
    (batch pilotBatch groups : ℕ) (hbatch : 0 < pilotBatch)
    (hsize : 2 ^ 20 * (σ ^ 2 / (c.scale / c.curvature) ^ 2 +
      v * (66 * R) / (c.scale / c.curvature)) ≤ (pilotBatch : ℝ)) (state : StageState E) :
    ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => μ).prod
      (Measure.pi fun _ : Fin batch => μ)) {ξ | ¬ GoodPilot proj c F g batch pilotBatch groups state ξ} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  classical
  by_cases hguard : permitted c state (predictor proj state)
  · let x := predictor proj state
    have hxc : ‖x - c.center‖ ≤ 64 * c.radius := hguard.2.2
    have hxs : ‖x - s‖ ≤ 66 * R := by
      have ht := norm_sub_le_norm_sub_add_norm_sub x c.center s
      linarith
    have hp := query_pilot_confidence μ c s x ho (hproj.mem _) hb hS hr hv
      (by positivity : 0 ≤ 66 * R) hxs (hscale x hxc) pilotBatch groups hbatch hsize
    have hm := GapNoiseSampling.measurable_pilotFromSamples c ho.measurable
      (measurable_const (a := x)) pilotBatch groups measurable_id
    have hset : MeasurableSet {ξ : Fin (groups + 1) → Fin pilotBatch → Ω |
        (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) / 8 <
          ‖pilotFromSamples c g x pilotBatch groups ξ - regularizedReply c x (F x)‖} :=
      measurableSet_lt measurable_const ((hm.sub_const _).norm)
    have he : {ξ : StepSamples Ω batch pilotBatch groups | ¬ GoodPilot proj c F g batch pilotBatch groups state ξ} =
        Prod.fst ⁻¹' {ξ | (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) / 8 <
          ‖pilotFromSamples c g x pilotBatch groups ξ - regularizedReply c x (F x)‖} := by
      ext ξ
      simp only [GoodPilot, hguard, true_implies, not_le, Set.mem_preimage, Set.mem_ofPred_eq, x]
    rw [he, measurePreserving_fst.measure_preimage hset.nullMeasurableSet]
    exact hp
  · simp only [GoodPilot, hguard, false_implies, not_true_eq_false, Set.ofPred_false, measure_empty]
    exact bot_le

def InitialGood (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups) : Prop :=
  ‖pilotFromSamples c g c.center pilotBatch groups ξ.1 - regularizedReply c c.center (F c.center)‖ ≤
    (‖regularizedReply c c.center (F c.center)‖ + c.scale / c.curvature) / 8

omit [CompleteSpace E] in
lemma measurableSet_initialGood (c : StageConfig (E := E)) (F : E → E)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ) :
    MeasurableSet {ξ | InitialGood c F g batch pilotBatch groups ξ} := by
  have hm := GapNoiseSampling.measurable_pilotFromSamples c hg (measurable_const (a := c.center))
    pilotBatch groups (measurable_fst (β := Fin batch → Ω))
  exact measurableSet_le ((hm.sub_const _).norm) measurable_const

lemma initialGood_failure_probability (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E}
    (c : StageConfig (E := E)) {F : E → E} {g : E → Ω → E} (s : E) {σ v D : ℝ}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s σ v)
    (hc : c.center ∈ X) (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hv : 0 ≤ v) (hD : 0 ≤ D) (hcs : ‖c.center - s‖ ≤ D)
    (hscale : c.curvature * (‖F s‖ + c.regularization * ‖c.center - c.anchor‖) ≤ c.scale)
    (batch pilotBatch groups : ℕ) (hbatch : 0 < pilotBatch)
    (hsize : 2 ^ 20 * (σ ^ 2 / (c.scale / c.curvature) ^ 2 + v * D / (c.scale / c.curvature)) ≤ (pilotBatch : ℝ)) :
    ((Measure.pi fun _ : Fin (groups + 1) => Measure.pi fun _ : Fin pilotBatch => μ).prod
      (Measure.pi fun _ : Fin batch => μ)) {ξ | ¬ InitialGood c F g batch pilotBatch groups ξ} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
  have hp := query_pilot_confidence μ c s c.center ho hc hb hS hr hv hD hcs hscale pilotBatch groups hbatch hsize
  have hm := GapNoiseSampling.measurable_pilotFromSamples c ho.measurable
    (measurable_const (a := c.center)) pilotBatch groups measurable_id
  have hset : MeasurableSet {ξ : Fin (groups + 1) → Fin pilotBatch → Ω |
      (‖regularizedReply c c.center (F c.center)‖ + c.scale / c.curvature) / 8 <
        ‖pilotFromSamples c g c.center pilotBatch groups ξ - regularizedReply c c.center (F c.center)‖} :=
    measurableSet_lt measurable_const ((hm.sub_const _).norm)
  have he : {ξ : StepSamples Ω batch pilotBatch groups | ¬ InitialGood c F g batch pilotBatch groups ξ} =
      Prod.fst ⁻¹' {ξ | (‖regularizedReply c c.center (F c.center)‖ + c.scale / c.curvature) / 8 <
        ‖pilotFromSamples c g c.center pilotBatch groups ξ - regularizedReply c c.center (F c.center)‖} := by
    ext ξ
    simp only [InitialGood, not_le, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [he, measurePreserving_fst.measure_preimage hset.nullMeasurableSet]
  exact hp

omit [CompleteSpace E] in
lemma trial_disagreement_probability {proj : E → E} (hproj : Measurable proj) (c : StageConfig (E := E))
    {F : E → E} (hF : Measurable F) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups steps : ℕ) (ν : Measure (StepSamples Ω batch pilotBatch groups))
    [IsProbabilityMeasure ν] {δ : ENNReal} (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hinitial : ν {ξ | ¬ InitialGood c F g batch pilotBatch groups ξ} ≤ δ)
    (hstep : ∀ state, ν {ξ | ¬ GoodPilot proj c F g batch pilotBatch groups state ξ} ≤ δ) :
    (ν.prod (Measure.pi fun _ : Fin steps => ν))
      {w | OracleTemplate.ContinuizedSimilarQuasar.iterateSamples (idealStep proj c F g batch pilotBatch groups)
          steps (idealInitial c F g batch pilotBatch groups w.1) w.2 ≠
        sampledTrialState proj c g batch pilotBatch groups steps w.1 w.2} ≤ (steps + 1 : ℕ) * δ := by
  have ha := measurable_idealStep hproj c hF hg batch pilotBatch groups
  have hgood := measurableSet_goodPilot hproj c hF hg batch pilotBatch groups
  have hi := measurable_idealInitial c hF hg batch pilotBatch groups
  have hgi := measurableSet_initialGood c F hg batch pilotBatch groups
  have hh := GapNoiseIteration.initialized_goodSamples_failure_probability
    ha hgood hi hgi ν ν (Inv := fun _ => True) (fun _ _ _ => trivial) (fun _ => trivial)
    (fun state _ => hstep state) hinitial steps
  have hsub : {w : StepSamples Ω batch pilotBatch groups × (Fin steps → StepSamples Ω batch pilotBatch groups) |
        OracleTemplate.ContinuizedSimilarQuasar.iterateSamples (idealStep proj c F g batch pilotBatch groups)
          steps (idealInitial c F g batch pilotBatch groups w.1) w.2 ≠
          sampledTrialState proj c g batch pilotBatch groups steps w.1 w.2} ⊆
      {w | ¬ (InitialGood c F g batch pilotBatch groups w.1 ∧
        GapNoiseIteration.GoodSamples (idealStep proj c F g batch pilotBatch groups)
          (GoodPilot proj c F g batch pilotBatch groups) steps
          (idealInitial c F g batch pilotBatch groups w.1) w.2)} := by
    intro w hbad hgood
    apply hbad
    exact ideal_trial_eq proj c F g batch pilotBatch groups steps w.1 w.2 hb hS hgood.1
      ((GapNoiseIteration.goodSamples_iff _ _ _ _ _).mp hgood.2)
  have hbound := (measure_mono hsub).trans hh
  convert hbound using 1
  push_cast
  ring

omit [CompleteSpace E] in
lemma tuned_initial_energy_bound [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    let c := stageConfig t j anchor center
    let z := p + stageShift t j • (s - p)
    (∫ ξ : StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j),
      GapNoiseStageEnergy.energy c F z (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ξ)
      ∂(Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
        (Measure.pi fun _ : Fin (stageBatch t j) => μ)) ≤ 3 * c.radius ^ 2 / 2 := by
  let c := stageConfig t j anchor center
  let τ := stageShift t j
  change ‖center - p‖ ≤ c.radius at hcp
  change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
  have hb : 0 < c.curvature := (GapNoiseTuning.effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < c.radius := GapNoiseTuning.stageRadius_pos t hR j
  have hr : 0 < c.regularization := GapNoiseTuning.stageRegularization_pos t hR hε j
  have hS : 0 < c.scale := GapNoiseTuning.stageScale_pos t h0 h1 hR hG hε j
  have hrS : c.regularization ≤ c.scale := GapNoiseTuning.stageScale_lower t h0 h1 hR hG hε j
  have hdR : c.radius ≤ t.R := OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le j
  have hJ : 1 ≤ (stages t : ℝ) := Nat.one_le_cast.mpr (GapNoiseTuning.stages_pos t)
  have hτ : τ = c.radius / (2 ^ 100 * (stages t : ℝ) * t.R * (1 + c.curvature * t.R)) := rfl
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hrd : c.regularization * c.radius = t.ε / (2 ^ 20 * stages t) :=
    OracleTemplate.ProjectedClippedExtragradient.regularization_radius (geometry t) hR j
  have heps : t.ε = 2 ^ 20 * (stages t : ℝ) * c.regularization * c.radius := by
    have hh := (eq_div_iff (by positivity : (2 : ℝ) ^ 20 * stages t ≠ 0)).mp hrd
    nlinarith
  have ha : c.regularization * ‖center - anchor‖ ≤ t.ε + 3 * c.regularization * c.radius := by
    have ht := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub center p anchor) hr.le
    have hc' := mul_le_mul_of_nonneg_left hcp hr.le
    change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
    nlinarith [mul_pos hr hd]
  have hshiftScale : c.curvature * (‖F s‖ + c.regularization * ‖center - anchor‖) ≤ c.scale :=
    GapNoiseTuning.stageScale_oracle_shift t h0 h1 hR hG hε j anchor center center (F s) hFs ha
      (by change ‖center - center‖ ≤ 64 * c.radius; simp only [sub_self, norm_zero]; positivity)
  have hsolutionScale : c.curvature * ‖F s‖ ≤ c.scale := by
    nlinarith [mul_nonneg (mul_nonneg hb.le hr.le) (norm_nonneg (center - anchor))]
  have hanchorScale : c.curvature * c.regularization * ‖center - anchor‖ ≤ c.scale := by
    nlinarith [mul_nonneg hb.le (norm_nonneg (F s))]
  have hrootGap := GapNoiseStageDrift.regularized_root_gap c F p s hp hs hr.le hroot hsolution
  change ⟪F p - F s, p - s⟫ ≤ c.regularization * ‖p - anchor‖ * ‖p - s‖ at hrootGap
  have hrootGap' : ⟪F p - F s, p - s⟫ ≤ t.ε * t.R := by
    have ha' := mul_le_mul_of_nonneg_right hres (norm_nonneg (p - s))
    have hd' := mul_le_mul_of_nonneg_left hps hε.le
    nlinarith
  have hM := GapNoiseTuning.rootBound_ge t h0 h1 hR hG hε
  have hsl := GapNoiseTuning.stageScale_operator_slope t h0 h1 hR hG hε j
  have hFp' := mul_le_mul_of_nonneg_left hFp hb.le
  have hG' := mul_le_mul_of_nonneg_left hM hb.le
  have hrootSlope : 2 * (t.L0 + c.curvature * ‖F p‖) ≤ c.scale := by
    change 4 * (t.L0 + c.curvature * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)) ≤ c.scale at hsl
    nlinarith [mul_nonneg hb.le (norm_nonneg (F p))]
  have hsolutionSlope : 4 * (t.L0 + c.curvature * t.G) ≤ c.scale := by
    change 4 * (t.L0 + c.curvature * OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)) ≤ c.scale at hsl
    nlinarith
  have hnormalized := GapNoiseStageDrift.initial_gap_normalized c hF p s hb hd hR hJ hr hrS
    hdR hcp hps hFs hrootGap' hrootSlope hsolutionSlope hsolutionScale hanchorScale heps hτ
  have hshift : τ * ‖p - s‖ ≤ c.radius / 24 := by
    have hh := (GapNoiseTuning.shift_geometry hd hR hdR hJ hb.le hτ).2.1
    have hm := mul_le_mul_of_nonneg_left hps hτ0
    linarith
  have hbatch := GapNoiseTuning.stageBatch_terms t h0 h1 hR hG hε hv j
  exact GapNoiseStageDrift.initial_energy_small μ c hF.cont p s ho (stageBatch t j) (pilotBatch t j)
    (pilotGroups t j) (GapNoiseTuning.stageBatch_pos t j) hc hb hS hd hrS hv (hF.mono center s)
    hcp hτ0 hshift hbatch.1 hbatch.2 hnormalized

lemma tuned_step_drift (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε)
    (state : StageState E) (hst : StableState X (stageConfig t j anchor center) F state) :
    let c := stageConfig t j anchor center
    let τ := stageShift t j
    let z := p + τ • (s - p)
    let floor := c.regularization * (τ ^ 2 * ‖p - anchor + (p - s)‖ ^ 2 +
      2 * τ * (‖p - anchor‖ * ‖p - s‖))
    (∫ ξ : StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j),
      GapNoiseStageEnergy.energy c F z (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) state ξ)
      ∂(Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
        (Measure.pi fun _ : Fin (stageBatch t j) => μ)) +
      (c.regularization / (2 ^ 25 * c.scale)) * activeLoss proj c z state ≤
    GapNoiseStageEnergy.energy c F z state + 2 * (1 / (16384 * c.scale)) * floor +
      (30 + 4096 * c.curvature * (66 * c.radius)) * (1 / (16384 * c.scale)) ^ 2 * t.σ ^ 2 / stageBatch t j := by
  let c := stageConfig t j anchor center
  let τ := stageShift t j
  let z := p + τ • (s - p)
  let h := c.radius / (1 + 132 * c.curvature * c.radius)
  let M := OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t)
  let B := M + t.ε + 65 * c.regularization * c.radius + 132 * (t.L0 + c.curvature * M) * c.radius
  change ‖center - p‖ ≤ c.radius at hcp
  change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
  have hb : 0 < c.curvature := (GapNoiseTuning.effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < c.radius := GapNoiseTuning.stageRadius_pos t hR j
  have hr : 0 < c.regularization := GapNoiseTuning.stageRegularization_pos t hR hε j
  have hS : 0 < c.scale := GapNoiseTuning.stageScale_pos t h0 h1 hR hG hε j
  have hdR : c.radius ≤ t.R := OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le j
  have hJ : 1 ≤ (stages t : ℝ) := Nat.one_le_cast.mpr (GapNoiseTuning.stages_pos t)
  have hτ : τ = c.radius / (2 ^ 100 * (stages t : ℝ) * t.R * (1 + c.curvature * t.R)) := rfl
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hshift := GapNoiseTuning.shift_geometry hd hR hdR hJ hb.le hτ
  have hprobe := GapNoiseTuning.probe_radius_bounds hb.le hd
  have hnormShift : ‖z - p‖ = τ * ‖p - s‖ := by
    have he : z - p = τ • (s - p) := by dsimp [z]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, norm_sub_rev s p]
  have hτps := mul_le_mul_of_nonneg_left hps hτ0
  have hzp : ‖z - p‖ ≤ c.radius := by rw [hnormShift]; linarith [hshift.2.1]
  have hz : z ∈ X := hX.add_smul_sub_mem hp hs ⟨hτ0, by linarith [hshift.1]⟩
  have hgeometry (hg : permitted c state (predictor proj state)) :
      ‖predictor proj state - p‖ ≤ 65 * c.radius ∧ ‖predictor proj state - z‖ ≤ 66 * c.radius := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (predictor proj state) center p
    have hxc : ‖predictor proj state - center‖ ≤ 64 * c.radius := hg.2.2
    have hxp : ‖predictor proj state - p‖ ≤ 65 * c.radius := by linarith
    have ht' := norm_sub_le_norm_sub_add_norm_sub (predictor proj state) p z
    rw [norm_sub_rev p z] at ht'
    exact ⟨hxp, by linarith⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans hFp
  have hB : ‖F p‖ + c.regularization * (‖p - c.anchor‖ + 65 * c.radius) +
      2 * (t.L0 + c.curvature * ‖F p‖) * (65 * c.radius + h) ≤ B := by
    have hm := mul_le_mul_of_nonneg_left hFp hb.le
    have hlength : 65 * c.radius + h ≤ 66 * c.radius := by dsimp [h]; linarith [hprobe.2.1]
    have hprod : 2 * (t.L0 + c.curvature * ‖F p‖) * (65 * c.radius + h) ≤
        2 * (t.L0 + c.curvature * M) * (66 * c.radius) := by gcongr
    change ‖F p‖ + c.regularization * (‖p - anchor‖ + 65 * c.radius) +
      2 * (t.L0 + c.curvature * ‖F p‖) * (65 * c.radius + h) ≤ _
    dsimp only [B]
    nlinarith
  have hoffset : 2 * c.curvature * B ≤ c.scale := GapNoiseTuning.stageScale_coercivity t h0 h1 hR hG hε j
  have hscale : c.regularization * c.curvature * (66 * c.radius) ^ 2 ≤ 4 * c.scale * h :=
    GapNoiseTuning.stageScale_distance t h0 h1 hR hG hε j
  have ha : c.regularization * ‖center - anchor‖ ≤ t.ε + 3 * c.regularization * c.radius := by
    have ht := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub center p anchor) hr.le
    have hc' := mul_le_mul_of_nonneg_left hcp hr.le
    nlinarith [mul_pos hr hd]
  have hlocal : t.L0 + c.regularization + c.curvature * c.regularization *
      ‖state.previousQuery - c.anchor‖ ≤ c.scale :=
    GapNoiseTuning.stageScale_query t h0 h1 hR hG hε j anchor center state.previousQuery ha hst.bounds.2.1
  have hbatch := GapNoiseTuning.stageBatch_terms t h0 h1 hR hG hε hv j
  have hK : 30 + 4096 * c.curvature * (66 * c.radius) ≤ 2 ^ 20 * (1 + c.curvature * c.radius) := by
    nlinarith [mul_pos hb hd]
  have hsize := GapNoiseTuning.batch_gap_bound hS (by positivity : 0 ≤ 1 + c.curvature * c.radius) hv hK hbatch.2
  exact GapNoiseStageDrift.ideal_step_drift μ hproj c hF state p s ho (stageBatch t j) (pilotBatch t j)
    (pilotGroups t j) (GapNoiseTuning.stageBatch_pos t j) hb hS hr.le hv hst hroot hsolution hz
    hτ0 hshift.1 hprobe.1 hprobe.2.2 (hτps.trans hshift.2.2) (by positivity : 0 ≤ 66 * c.radius)
    hgeometry hB hoffset hscale hlocal hsize

omit [CompleteSpace E] in
lemma tuned_accumulated_energy [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    let c := stageConfig t j anchor center
    let z := p + stageShift t j • (s - p)
    let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
      (Measure.pi fun _ : Fin (stageBatch t j) => μ)
    let A := fun w : StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ×
        (Fin (stageSteps t j) → StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j)) =>
      GapNoiseIteration.accumulatedEnergy (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j))
        (GapNoiseStageEnergy.energy c F z) (activeLoss proj c z) (c.regularization / (2 ^ 25 * c.scale))
        (stageSteps t j) (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1) w.2
    Integrable A (ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)) ∧
      (∫ w, A w ∂ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)) ≤ 2 * c.radius ^ 2 := by
  let c := stageConfig t j anchor center
  let τ := stageShift t j
  let z := p + τ • (s - p)
  let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
    (Measure.pi fun _ : Fin (stageBatch t j) => μ)
  let κ := c.regularization / (2 ^ 25 * c.scale)
  let floor := c.regularization * (τ ^ 2 * ‖p - anchor + (p - s)‖ ^ 2 +
    2 * τ * (‖p - anchor‖ * ‖p - s‖))
  let β := 2 * (1 / (16384 * c.scale)) * floor +
    (30 + 4096 * c.curvature * (66 * c.radius)) * (1 / (16384 * c.scale)) ^ 2 * t.σ ^ 2 / stageBatch t j
  have hb : 0 < c.curvature := (GapNoiseTuning.effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < c.radius := GapNoiseTuning.stageRadius_pos t hR j
  have hr : 0 < c.regularization := GapNoiseTuning.stageRegularization_pos t hR hε j
  have hS : 0 < c.scale := GapNoiseTuning.stageScale_pos t h0 h1 hR hG hε j
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have ha : c.regularization * ‖center - anchor‖ ≤ t.ε + 3 * c.regularization * c.radius := by
    have ht := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub center p anchor) hr.le
    have hc' := mul_le_mul_of_nonneg_left hcp hr.le
    change c.regularization * ‖center - p‖ ≤ c.regularization * c.radius at hc'
    change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
    nlinarith [mul_pos hr hd]
  have hquery (x : E) (hx : ‖x - c.center‖ ≤ 64 * c.radius) :
      t.L0 + c.regularization + c.curvature * c.regularization * ‖x - c.anchor‖ ≤ c.scale :=
    GapNoiseTuning.stageScale_query t h0 h1 hR hG hε j anchor center x ha hx
  have hinv (st : StageState E) (hst : StableState X c F st)
      (ξ : StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j)) :
      StableState X c F (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) st ξ) :=
    idealStep_stable hproj c hc hF g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) st ξ
      hb hS hr.le hst (hquery st.previousQuery hst.bounds.2.1)
  have hinit (ξ : StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j)) :
      StableState X c F (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ξ) :=
    idealInitial_stable c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ξ hb hS hd.le hc
  obtain ⟨M, hM⟩ := local_trueReply_bounded c hF.cont
  let bound := (64 * c.radius + 1 / (1024 * c.curvature) + ‖z - c.center‖) ^ 2 +
    (128 * c.radius + 1 / (1024 * c.curvature)) ^ 2 / 4 +
    24 * (1 / (1024 * c.curvature) + (1 / (16384 * c.scale)) * M) ^ 2
  have henergy (st : StageState E) (hst : StableState X c F st) :
      0 ≤ GapNoiseStageEnergy.energy c F z st ∧ GapNoiseStageEnergy.energy c F z st ≤ bound :=
    ⟨GapNoiseStageEnergy.energy_nonneg _ _ _ _, state_energy_bound c F z st hb hst.bounds hM⟩
  have hloss (st : StageState E) (_ : StableState X c F st) :
      0 ≤ activeLoss proj c z st ∧ activeLoss proj c z st ≤ (64 * c.radius + ‖c.center - z‖) ^ 2 :=
    ⟨activeLoss_nonneg _ _ _ _, activeLoss_bound _ _ _ _⟩
  have hmstep := measurable_idealStep hproj.lipschitz.continuous.measurable c hF.cont.measurable ho.measurable
    (stageBatch t j) (pilotBatch t j) (pilotGroups t j)
  have hmenergy := GapNoiseStageEnergy.measurable_energy c hF.cont.measurable z
  have hmloss := measurable_activeLoss hproj.lipschitz.continuous.measurable c z
  have hminit := measurable_idealInitial c hF.cont.measurable ho.measurable (stageBatch t j) (pilotBatch t j) (pilotGroups t j)
  have hi := GapNoiseIteration.initialized_accumulatedEnergy_integrable hmstep hmenergy hmloss hminit
    ν ν hinv hκ henergy hloss hinit (stageSteps t j)
  have hstep (st : StageState E) (hst : StableState X c F st) :
      (∫ ξ, GapNoiseStageEnergy.energy c F z
        (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) st ξ) ∂ν) +
        κ * activeLoss proj c z st ≤ GapNoiseStageEnergy.energy c F z st + β := by
    have hh := tuned_step_drift μ hproj hX t h0 h1 hR hG hε hv j anchor center p s hF ho hp hs hroot hsolution
      hcp hps hFp hres st hst
    simpa only [β, add_assoc] using hh
  have hstart := tuned_initial_energy_bound μ t h0 h1 hR hG hε hv j anchor center p s hF ho hc hp hs
    hroot hsolution hcp hps hFs hFp hres
  have hm := GapNoiseIteration.initialized_accumulatedEnergy_integral hmstep hmenergy hmloss hminit
    ν ν hinv hκ henergy hloss hstep hinit hstart (stageSteps t j)
  have hsum : (stageSteps t j : ℝ) * β ≤ c.radius ^ 2 / 4 :=
    GapNoiseTuning.tuned_drift_sum t h0 h1 hR hG hε hv j p anchor s hres hps
  refine ⟨hi, ?_⟩
  change (∫ w, GapNoiseIteration.accumulatedEnergy
    (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j))
    (GapNoiseStageEnergy.energy c F z) (activeLoss proj c z) κ (stageSteps t j)
    (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1) w.2
    ∂ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)) ≤ 2 * c.radius ^ 2
  nlinarith [sq_nonneg c.radius]

set_option maxHeartbeats 800000 in
omit [CompleteSpace E] in
lemma ideal_trial_confidence [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    let c := stageConfig t j anchor center
    let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
      (Measure.pi fun _ : Fin (stageBatch t j) => μ)
    (ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)) {w |
      c.radius / 12 < ‖trialOutput c (stageSteps t j)
        (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
          (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j)) (stageSteps t j)
          (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1) w.2) - p‖} ≤
      ENNReal.ofReal (1 / 512 : ℝ) := by
  let c := stageConfig t j anchor center
  let τ := stageShift t j
  let z := p + τ • (s - p)
  let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
    (Measure.pi fun _ : Fin (stageBatch t j) => μ)
  let κ := c.regularization / (2 ^ 25 * c.scale)
  have hb : 0 < c.curvature := (GapNoiseTuning.effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < c.radius := GapNoiseTuning.stageRadius_pos t hR j
  have hr : 0 < c.regularization := GapNoiseTuning.stageRegularization_pos t hR hε j
  have hS : 0 < c.scale := GapNoiseTuning.stageScale_pos t h0 h1 hR hG hε j
  have hN := GapNoiseTuning.stageSteps_pos t h0 h1 hR hG hε j
  have hweight : (2 : ℝ) ^ 23 ≤ κ * stageSteps t j :=
    GapNoiseTuning.stage_accumulated_weight hr hS (GapNoiseTuning.stageSteps_lower t j)
  have hdR : c.radius ≤ t.R := OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le j
  have hJ : 1 ≤ (stages t : ℝ) := Nat.one_le_cast.mpr (GapNoiseTuning.stages_pos t)
  have hτ : τ = c.radius / (2 ^ 100 * (stages t : ℝ) * t.R * (1 + c.curvature * t.R)) := rfl
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hshift := (GapNoiseTuning.shift_geometry hd hR hdR hJ hb.le hτ).2.1
  have hzp : ‖z - p‖ ≤ c.radius / 24 := by
    have he : z - p = τ • (s - p) := by dsimp [z]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, norm_sub_rev s p]
    have hh := mul_le_mul_of_nonneg_left hps hτ0
    linarith
  change ‖center - p‖ ≤ c.radius at hcp
  change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
  have ha : c.regularization * ‖center - anchor‖ ≤ t.ε + 3 * c.regularization * c.radius := by
    have ht := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub center p anchor) hr.le
    have hc' := mul_le_mul_of_nonneg_left hcp hr.le
    nlinarith [mul_pos hr hd]
  have hquery (x : E) (hx : ‖x - c.center‖ ≤ 64 * c.radius) :
      t.L0 + c.regularization + c.curvature * c.regularization * ‖x - c.anchor‖ ≤ c.scale :=
    GapNoiseTuning.stageScale_query t h0 h1 hR hG hε j anchor center x ha hx
  have hrootScale : t.L0 + c.regularization + c.curvature * c.regularization * ‖p - c.anchor‖ ≤ c.scale := by
    have hm := mul_le_mul_of_nonneg_left hres hb.le
    have hs' := GapNoiseTuning.stageScale_smoothness t h0 h1 hR hG hε j
    change t.L0 + c.regularization + c.curvature * t.ε +
      67 * c.curvature * c.regularization * c.radius ≤ c.scale at hs'
    change t.L0 + c.regularization + c.curvature * c.regularization * ‖p - anchor‖ ≤ c.scale
    nlinarith [mul_nonneg (mul_nonneg hb.le hr.le) hd.le]
  have hnorm : c.curvature * ‖regularizedReply c p (F p)‖ ≤ c.scale := by
    have ht := norm_add_le (F p) (c.regularization • (p - anchor))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at ht
    have ht' := mul_le_mul_of_nonneg_left ht hb.le
    have hFp' := mul_le_mul_of_nonneg_left hFp hb.le
    have hres' := mul_le_mul_of_nonneg_left hres hb.le
    have hs' := GapNoiseTuning.stageScale_root_envelope t h0 h1 hR hG hε j
    change c.curvature * (OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t) + t.ε) ≤ c.scale at hs'
    change c.curvature * ‖F p + c.regularization • (p - anchor)‖ ≤ c.scale
    nlinarith
  have he := tuned_accumulated_energy μ hproj hX t h0 h1 hR hG hε hv j anchor center p s hF ho
    hc hp hs hroot hsolution hcp hps hFs hFp hres
  apply trial_failure_probability
    (W := StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ×
      (Fin (stageSteps t j) → StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j)))
    (κ := κ) proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j)
    (stageSteps t j) hN z p (fun w => idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1)
    (fun w => w.2) (fun _ => rfl) hd hweight hzp (ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν))
    _ he.1 he.2
  intro w hfailed
  exact stopped_exit_energy hproj c hc hF g (stageBatch t j) (pilotBatch t j) (pilotGroups t j)
    (stageSteps t j) (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1) z p w.2
    hb hS hr.le hd (idealInitial_stable c F g _ _ _ w.1 hb hS hd.le hc) rfl hp hroot
    (hzp.trans (by linarith)) (by change ‖p - center‖ ≤ c.radius; rw [norm_sub_rev]; exact hcp) hrootScale hnorm hquery hfailed

set_option maxHeartbeats 800000 in
omit [CompleteSpace E] in
lemma sampled_trial_confidence [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    let c := stageConfig t j anchor center
    let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
      (Measure.pi fun _ : Fin (stageBatch t j) => μ)
    (ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)) {w |
      c.radius / 12 < ‖sampledTrialOutput proj c g (stageBatch t j) (pilotBatch t j) (pilotGroups t j)
        (stageSteps t j) w.1 w.2 - p‖} ≤ ENNReal.ofReal (1 / 256 : ℝ) := by
  let c := stageConfig t j anchor center
  let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
    (Measure.pi fun _ : Fin (stageBatch t j) => μ)
  let W := StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j) ×
    (Fin (stageSteps t j) → StepSamples Ω (stageBatch t j) (pilotBatch t j) (pilotGroups t j))
  let P := ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)
  let ideal : W → StageState E := fun w => OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (idealStep proj c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j)) (stageSteps t j)
      (idealInitial c F g (stageBatch t j) (pilotBatch t j) (pilotGroups t j) w.1) w.2
  let actual : W → StageState E := fun w => sampledTrialState proj c g (stageBatch t j) (pilotBatch t j)
    (pilotGroups t j) (stageSteps t j) w.1 w.2
  have hb : 0 < c.curvature := (GapNoiseTuning.effectiveCurvature_bounds t h0 h1 hG hR).1
  have hd : 0 < c.radius := GapNoiseTuning.stageRadius_pos t hR j
  have hr : 0 < c.regularization := GapNoiseTuning.stageRegularization_pos t hR hε j
  have hS : 0 < c.scale := GapNoiseTuning.stageScale_pos t h0 h1 hR hG hε j
  have hdR : c.radius ≤ t.R := OracleTemplate.ProjectedClippedExtragradient.radius_le (geometry t) hR.le j
  change ‖center - p‖ ≤ c.radius at hcp
  change c.regularization * ‖p - anchor‖ ≤ t.ε at hres
  have ha : c.regularization * ‖center - anchor‖ ≤ t.ε + 3 * c.regularization * c.radius := by
    have ht := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub center p anchor) hr.le
    have hc' := mul_le_mul_of_nonneg_left hcp hr.le
    nlinarith [mul_pos hr hd]
  have hcs : ‖c.center - s‖ ≤ 2 * t.R := by
    change ‖center - s‖ ≤ 2 * t.R
    have ht := norm_sub_le_norm_sub_add_norm_sub center p s
    linarith
  have hscale (x : E) (hx : ‖x - c.center‖ ≤ 64 * c.radius) :
      c.curvature * (‖F s‖ + c.regularization * ‖x - c.anchor‖) ≤ c.scale :=
    GapNoiseTuning.stageScale_oracle_shift t h0 h1 hR hG hε j anchor center x (F s) hFs ha hx
  have hbatch := GapNoiseTuning.pilotBatch_relative t h0 h1 hR hG hε hv j
  have hi := initialGood_failure_probability μ c s ho hc hb hS hr.le hv
    (by positivity : 0 ≤ 66 * t.R) (hcs.trans (by linarith))
    (hscale c.center (by simp only [sub_self, norm_zero]; positivity))
    (stageBatch t j) (pilotBatch t j) (pilotGroups t j) (GapNoiseTuning.pilotBatch_pos t j) hbatch
  have hstep := goodPilot_failure_probability μ hproj c s ho hb hS hr.le hv hR hdR hcs hscale
    (stageBatch t j) (pilotBatch t j) (pilotGroups t j) (GapNoiseTuning.pilotBatch_pos t j) hbatch
  have hdisagreement : P {w | ideal w ≠ actual w} ≤
      (stageSteps t j + 1 : ℕ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (pilotGroups t j + 1)) :=
    trial_disagreement_probability hproj.lipschitz.continuous.measurable c hF.cont.measurable ho.measurable
      (stageBatch t j) (pilotBatch t j) (pilotGroups t j) (stageSteps t j) ν hb hS hi hstep
  have hreal : (stageSteps t j + 1 : ℕ) * (1 / 2 : ℝ) ^ (pilotGroups t j + 1) ≤ 1 / 16384 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16384 * ((stageSteps t j : ℝ) + 1))).mp
      (GapNoiseTuning.pilotGroups_confidence t j)
    push_cast
    nlinarith
  have hprob : (stageSteps t j + 1 : ℕ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (pilotGroups t j + 1)) ≤
      ENNReal.ofReal (1 / 16384 : ℝ) := by
    have hh := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg (stageSteps t j + 1)), ENNReal.ofReal_natCast] using hh
  have hideal : P {w | c.radius / 12 < ‖trialOutput c (stageSteps t j) (ideal w) - p‖} ≤
      ENNReal.ofReal (1 / 512 : ℝ) :=
    ideal_trial_confidence μ hproj hX t h0 h1 hR hG hε hv j anchor center p s hF ho
      hc hp hs hroot hsolution hcp hps hFs hFp hres
  have hsub : {w : W | c.radius / 12 < ‖trialOutput c (stageSteps t j) (actual w) - p‖} ⊆
      {w | c.radius / 12 < ‖trialOutput c (stageSteps t j) (ideal w) - p‖} ∪ {w | ideal w ≠ actual w} := by
    intro w hw
    by_cases he : ideal w = actual w
    · apply Or.inl
      change c.radius / 12 < ‖trialOutput c (stageSteps t j) (ideal w) - p‖
      rw [he]
      exact hw
    · exact Or.inr he
  have hh := (measure_mono (μ := P) hsub).trans (measure_union_le _ _)
  have hbound := hh.trans (add_le_add hideal (hdisagreement.trans hprob))
  change P {w : W | c.radius / 12 < ‖trialOutput c (stageSteps t j) (actual w) - p‖} ≤ _
  apply hbound.trans
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 512) (by norm_num : (0 : ℝ) ≤ 1 / 16384)]
  apply ENNReal.ofReal_le_ofReal
  norm_num

omit [CompleteSpace E] in
lemma sampled_stage_confidence [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    let c := stageConfig t j anchor center
    let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
      (Measure.pi fun _ : Fin (stageBatch t j) => μ)
    (Measure.pi fun _ : Fin (outerGroups t + 1) => ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν))
      {w | c.radius / 2 < ‖sampledStageOutput proj c g (stageBatch t j) (pilotBatch t j)
        (pilotGroups t j) (stageSteps t j) (outerGroups t) w - p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (outerGroups t + 1)) := by
  let c := stageConfig t j anchor center
  let ν := (Measure.pi fun _ : Fin (pilotGroups t j + 1) => Measure.pi fun _ : Fin (pilotBatch t j) => μ).prod
    (Measure.pi fun _ : Fin (stageBatch t j) => μ)
  let P := ν.prod (Measure.pi fun _ : Fin (stageSteps t j) => ν)
  have ht := sampled_trial_confidence μ hproj hX t h0 h1 hR hG hε hv j anchor center p s
    hF ho hc hp hs hroot hsolution hcp hps hFs hFp hres
  have ht' : P.real {w | c.radius / 12 < ‖sampledTrialOutput proj c g (stageBatch t j)
      (pilotBatch t j) (pilotGroups t j) (stageSteps t j) w.1 w.2 - p‖} ≤ 1 / 256 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 256)] using hh
  have hh := OracleTemplate.MultiplicativeRobustEstimator.medoid_failure_probability
    (P := P) (GapNoiseSampling.measurable_sampledTrialOutput hproj.lipschitz.continuous.measurable
      c ho.measurable (stageBatch t j) (pilotBatch t j) (pilotGroups t j) (stageSteps t j))
    p (r := c.radius / 12) (by have := GapNoiseTuning.stageRadius_pos t hR j; change 0 ≤ c.radius / 12; positivity)
    ht' (outerGroups t)
  have he : 6 * (c.radius / 12) = c.radius / 2 := by ring
  simpa only [he, Function.uncurry, sampledStageOutput] using hh

omit [CompleteSpace E] in
lemma stageBlockOutput_confidence [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (h0 : 0 < t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R)
    (hG : 0 ≤ t.G) (hε : 0 < t.ε) (hv : 0 ≤ t.v) (j : ℕ) (anchor center p s : E)
    {F : E → E} (hF : OracleTemplate.GeneralizedMonotone.Hyp F t.L0 (effectiveCurvature t))
    {g : E → Ω → E}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s t.σ t.v)
    (hc : center ∈ X) (hp : p ∈ X) (hs : s ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p
      (-(F p + OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j • (p - anchor))))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hcp : ‖center - p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.radius (geometry t) j)
    (hps : ‖p - s‖ ≤ t.R) (hFs : ‖F s‖ ≤ t.G)
    (hFp : ‖F p‖ ≤ OracleTemplate.ProjectedClippedExtragradient.rootBound (geometry t))
    (hres : OracleTemplate.ProjectedClippedExtragradient.regularization (geometry t) j * ‖p - anchor‖ ≤ t.ε) :
    (Measure.pi fun _ : Fin (stageCalls t j) => μ)
      {ξ | (stageConfig t j anchor center).radius / 2 <
        ‖stageBlockOutput proj t j anchor center g ξ - p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (outerGroups t + 1)) := by
  let c := stageConfig t j anchor center
  have hm := GapNoiseSampling.measurable_sampledStageOutput hproj.lipschitz.continuous.measurable
    c ho.measurable (stageBatch t j) (pilotBatch t j) (pilotGroups t j) (stageSteps t j) (outerGroups t)
  have hset := measurableSet_lt (measurable_const (a := c.radius / 2))
    (hm.sub (measurable_const (a := p))).norm
  have he := (GapNoiseSampling.stageSamples_preserving μ t j).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (stageCalls t j) => μ) (stageSamples t j ⁻¹'
    {ξ | c.radius / 2 < ‖sampledStageOutput proj c g (stageBatch t j) (pilotBatch t j)
      (pilotGroups t j) (stageSteps t j) (outerGroups t) ξ - p‖}) ≤ _
  simp only [Pi.sub_apply] at he
  rw [he]
  exact sampled_stage_confidence μ hproj hX t h0 h1 hR hG hε hv j anchor center p s hF ho
    hc hp hs hroot hsolution hcp hps hFs hFp hres

end LongTails.Proofs.GapNoiseStageConfidence
