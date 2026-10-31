import LongTails.Proofs.GapNoiseIteration
import Mathlib.Algebra.Order.Chebyshev
import LongTails.Proofs.GapNoiseSampling
import LongTails.Proofs.GapNoiseStageEnergy

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseStopped

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseStageEnergy

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def trueDenominator (c : StageConfig (E := E)) (F : E → E) (x : E) : ℝ :=
  c.scale + c.curvature * (‖regularizedReply c x (F x)‖ + c.scale / c.curvature)

noncomputable def repairedDenominator (c : StageConfig (E := E)) (F : E → E) (x pilot : E) : ℝ :=
  max (trueDenominator c F x) (min (8 * trueDenominator c F x) (pilotDenominator c pilot))

noncomputable def idealInitial (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups) : StageState E :=
  initialWithDenominator c
    (repairedDenominator c F c.center (pilotFromSamples c g c.center pilotBatch groups ξ.1))
    ((1 / (batch : ℝ)) • ∑ j, g c.center (ξ.2 j))

noncomputable def idealStep (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups) : StageState E := by
  classical
  let x := predictor proj state
  exact if permitted c state x then
    { sampledStep proj c g batch pilotBatch groups state ξ with
      pilotDenominator := repairedDenominator c F x (pilotFromSamples c g x pilotBatch groups ξ.1) }
  else { state with active := false }

lemma trueDenominator_eq (c : StageConfig (E := E)) (F : E → E) (x : E) (hb : c.curvature ≠ 0) :
    trueDenominator c F x = 2 * c.scale + c.curvature * ‖regularizedReply c x (F x)‖ := by
  have he : c.curvature * (c.scale / c.curvature) = c.scale := by field_simp
  rw [trueDenominator, mul_add, he]
  ring

lemma trueDenominator_pos (c : StageConfig (E := E)) (F : E → E) (x : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) : 0 < trueDenominator c F x := by
  unfold trueDenominator
  positivity

lemma repairedDenominator_bounds (c : StageConfig (E := E)) (F : E → E) (x pilot : E)
    (hD : 0 ≤ trueDenominator c F x) :
    trueDenominator c F x ≤ repairedDenominator c F x pilot ∧
      repairedDenominator c F x pilot ≤ 8 * trueDenominator c F x := by
  unfold repairedDenominator
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma repairedDenominator_eq (c : StageConfig (E := E)) (F : E → E) (x pilot : E)
    (hlo : trueDenominator c F x ≤ pilotDenominator c pilot)
    (hhi : pilotDenominator c pilot ≤ 8 * trueDenominator c F x) :
    repairedDenominator c F x pilot = pilotDenominator c pilot := by
  rw [repairedDenominator, min_eq_right hhi, max_eq_right hlo]

lemma idealInitial_eq (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups)
    (hlo : trueDenominator c F c.center ≤
      pilotDenominator c (pilotFromSamples c g c.center pilotBatch groups ξ.1))
    (hhi : pilotDenominator c (pilotFromSamples c g c.center pilotBatch groups ξ.1) ≤
      8 * trueDenominator c F c.center) :
    idealInitial c F g batch pilotBatch groups ξ = sampledInitial c g batch pilotBatch groups ξ := by
  unfold idealInitial sampledInitial initialState
  rw [repairedDenominator_eq c F c.center _ hlo hhi]

lemma idealStep_energy (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups) (z : E) :
    energy c F z (idealStep proj c F g batch pilotBatch groups state ξ) =
      energy c F z (sampledStep proj c g batch pilotBatch groups state ξ) := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · simp only [idealStep, hp, ite_true, energy_pilot_replacement]
  · simp only [idealStep, sampledStep, hp, ite_false]

lemma idealStep_eq (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups)
    (hgood : permitted c state (predictor proj state) →
      trueDenominator c F (predictor proj state) ≤
        pilotDenominator c (pilotFromSamples c g (predictor proj state) pilotBatch groups ξ.1) ∧
      pilotDenominator c (pilotFromSamples c g (predictor proj state) pilotBatch groups ξ.1) ≤
        8 * trueDenominator c F (predictor proj state)) :
    idealStep proj c F g batch pilotBatch groups state ξ =
      sampledStep proj c g batch pilotBatch groups state ξ := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · simp only [idealStep, sampledStep, advance, hp, ite_true, updatedState,
      repairedDenominator_eq c F _ _ (hgood hp).1 (hgood hp).2]
  · simp only [idealStep, sampledStep, hp, ite_false]

lemma accuratePilot_bounds (c : StageConfig (E := E)) (F : E → E) (x estimate : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (herror : ‖estimate - regularizedReply c x (F x)‖ ≤
      (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) / 8) :
    trueDenominator c F x ≤ pilotDenominator c estimate ∧
      pilotDenominator c estimate ≤ 8 * trueDenominator c F x := by
  have hh := GapNoisePastState.pilotDenominator_comparable c estimate (regularizedReply c x (F x)) hb hS.le herror
  change trueDenominator c F x ≤ pilotDenominator c estimate ∧
    pilotDenominator c estimate ≤ 3 * trueDenominator c F x at hh
  exact ⟨hh.1, hh.2.trans (by nlinarith [trueDenominator_pos c F x hb hS])⟩

lemma ideal_trial_eq (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (initial : StepSamples Ω batch pilotBatch groups)
    (ξ : Fin steps → StepSamples Ω batch pilotBatch groups)
    (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hinitial : ‖pilotFromSamples c g c.center pilotBatch groups initial.1 -
        regularizedReply c c.center (F c.center)‖ ≤
      (‖regularizedReply c c.center (F c.center)‖ + c.scale / c.curvature) / 8)
    (hgood : ∀ i,
      let state := GapNoiseIteration.pointTrace
        (idealStep proj c F g batch pilotBatch groups) id steps
        (idealInitial c F g batch pilotBatch groups initial) ξ i
      permitted c state (predictor proj state) →
      ‖pilotFromSamples c g (predictor proj state) pilotBatch groups (ξ i).1 -
          regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
        (‖regularizedReply c (predictor proj state) (F (predictor proj state))‖ +
          c.scale / c.curvature) / 8) :
    OracleTemplate.ContinuizedSimilarQuasar.iterateSamples (idealStep proj c F g batch pilotBatch groups)
      steps (idealInitial c F g batch pilotBatch groups initial) ξ =
    sampledTrialState proj c g batch pilotBatch groups steps initial ξ := by
  have hi := accuratePilot_bounds c F c.center _ hb hS hinitial
  have he := idealInitial_eq c F g batch pilotBatch groups initial hi.1 hi.2
  have hh := GapNoiseIteration.iterate_eq_of_pointTrace
    (advance := sampledStep proj c g batch pilotBatch groups)
    (reference := idealStep proj c F g batch pilotBatch groups)
    (good := fun state samples => permitted c state (predictor proj state) →
      ‖pilotFromSamples c g (predictor proj state) pilotBatch groups samples.1 -
          regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
        (‖regularizedReply c (predictor proj state) (F (predictor proj state))‖ + c.scale / c.curvature) / 8)
    (fun state samples hg => idealStep_eq proj c F g batch pilotBatch groups state samples
      (fun hp => accuratePilot_bounds c F _ _ hb hS (hg hp)))
    steps (idealInitial c F g batch pilotBatch groups initial) ξ hgood
  rw [hh, he]
  rfl

lemma idealStep_energy_raw (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E) (ξ : StepSamples Ω batch pilotBatch groups) (z : E) :
    energy c F z (idealStep proj c F g batch pilotBatch groups state ξ) =
      energy c F z (advance proj c state (predictor proj state) 0
        ((1 / (batch : ℝ)) • ∑ j, g (predictor proj state) (ξ.2 j))) := by
  classical
  rw [idealStep_energy]
  by_cases hp : permitted c state (predictor proj state)
  · simp only [sampledStep, hp, ite_true]
    exact energy_advance_pilot _ _ _ _ _ _ _ _ _
  · simp only [sampledStep, advance, hp, ite_false]

lemma repairedDenominator_lower (c : StageConfig (E := E)) (F : E → E) (x pilot : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) :
    c.scale ≤ repairedDenominator c F x pilot := by
  have hd : c.scale ≤ trueDenominator c F x := by
    unfold trueDenominator
    exact le_add_of_nonneg_right (mul_nonneg hb.le (add_nonneg (norm_nonneg _) (div_nonneg hS.le hb.le)))
  exact hd.trans (repairedDenominator_bounds c F x pilot (trueDenominator_pos c F x hb hS).le).1

noncomputable def StateBounds (c : StageConfig (E := E)) (state : StageState E) : Prop :=
  ‖state.base - c.center‖ ≤ 64 * c.radius + 1 / (1024 * c.curvature) ∧
  ‖state.previousQuery - c.center‖ ≤ 64 * c.radius ∧
  c.scale ≤ state.pilotDenominator ∧
  0 < state.previousStep ∧ state.previousStep ≤ 1 / (16384 * c.scale) ∧
  c.curvature * state.previousStep * ‖state.previousReply‖ ≤ 1 / 1024

lemma initialWithDenominator_bounds (c : StageConfig (E := E)) (denominator : ℝ) (raw : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 ≤ c.radius)
    (hden : c.scale ≤ denominator) : StateBounds c (initialWithDenominator c denominator raw) := by
  have hdenpos : 0 < denominator := hS.trans_le hden
  have hη : 0 < 1 / (16384 * denominator) := by positivity
  have hηmax : 1 / (16384 * denominator) ≤ 1 / (16384 * c.scale) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hcap := GapNoisePastState.clippedReply_cap c (regularizedReply c c.center raw) hb hη
  simp only [StateBounds, initialWithDenominator, sub_self, norm_zero]
  exact ⟨by positivity, by positivity, hden, hη, hηmax, hcap⟩

lemma idealInitial_bounds (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 ≤ c.radius) :
    StateBounds c (idealInitial c F g batch pilotBatch groups ξ) :=
  initialWithDenominator_bounds c _ _ hb hS hd (repairedDenominator_lower c F _ _ hb hS)

lemma projected_update_ball {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    (hc : c.center ∈ X) (w raw : E) {η : ℝ} (hb : 0 < c.curvature) (hη : 0 < η)
    (hw : ‖w - c.center‖ ≤ 64 * c.radius) :
    ‖proj (w - η • clippedReply c η raw) - c.center‖ ≤
      64 * c.radius + 1 / (1024 * c.curvature) := by
  have hp := hproj.dist_le (w - η • clippedReply c η raw) hc
  have he : w - η • clippedReply c η raw - c.center =
      (w - c.center) - η • clippedReply c η raw := by abel
  rw [he] at hp
  have ht := norm_sub_le (w - c.center) (η • clippedReply c η raw)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη] at ht
  have hcap := GapNoisePastState.clippedReply_cap c raw hb hη
  have hc' : η * ‖clippedReply c η raw‖ ≤ 1 / (1024 * c.curvature) := by
    apply (le_div_iff₀ (by positivity : 0 < 1024 * c.curvature)).mpr
    nlinarith
  linarith

lemma idealStep_bounds {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    (hc : c.center ∈ X) (F : E → E) (g : E → Ω → E) (batch pilotBatch groups : ℕ)
    (state : StageState E) (ξ : StepSamples Ω batch pilotBatch groups)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hs : StateBounds c state) :
    StateBounds c (idealStep proj c F g batch pilotBatch groups state ξ) := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · have hη := GapNoisePastState.nextStep_pos state hs.2.2.2.1 (hS.trans_le hs.2.2.1)
    have hηmax : nextStep state ≤ 1 / (16384 * c.scale) :=
      (min_le_right _ _).trans
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hs.2.2.1]))
    simp only [idealStep, sampledStep, advance, hp, ite_true, updatedState, StateBounds]
    exact ⟨projected_update_ball hproj c hc _ _ hb hη hp.2.1, hp.2.2,
      repairedDenominator_lower c F _ _ hb hS, hη, hηmax,
      GapNoisePastState.clippedReply_cap c _ hb hη⟩
  · simpa only [idealStep, hp, ite_false, StateBounds] using hs

lemma state_energy_bound (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E)
    {M : ℝ} (hb : 0 < c.curvature) (hs : StateBounds c state)
    (hH : ∀ x, ‖x - c.center‖ ≤ 64 * c.radius → ‖regularizedReply c x (F x)‖ ≤ M) :
    energy c F z state ≤
      (64 * c.radius + 1 / (1024 * c.curvature) + ‖z - c.center‖) ^ 2 +
      (128 * c.radius + 1 / (1024 * c.curvature)) ^ 2 / 4 +
      24 * (1 / (1024 * c.curvature) + (1 / (16384 * c.scale)) * M) ^ 2 := by
  have hcap : |state.previousStep| * ‖state.previousReply‖ ≤ 1 / (1024 * c.curvature) := by
    rw [abs_of_pos hs.2.2.2.1]
    apply (le_div_iff₀ (by positivity : 0 < 1024 * c.curvature)).mpr
    nlinarith [hs.2.2.2.2.2]
  have h := energy_le_of_bounds c F z c.center state hs.1 hs.2.1 le_rfl
    (by simpa only [abs_of_pos hs.2.2.2.1] using hs.2.2.2.2.1) hcap
    (hH state.previousQuery hs.2.1)
  convert h using 1; ring

lemma local_trueReply_bounded [FiniteDimensional ℝ E] (c : StageConfig (E := E))
    {F : E → E} (hF : Continuous F) :
    ∃ M : ℝ, ∀ x, ‖x - c.center‖ ≤ 64 * c.radius → ‖regularizedReply c x (F x)‖ ≤ M := by
  have hc : Continuous (fun x => regularizedReply c x (F x)) := by
    unfold regularizedReply
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall c.center (64 * c.radius)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨M, fun x hx => hM x (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)⟩

lemma regularized_pair_local (c : StageConfig (E := E)) {F : E → E} {L0 : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature) (x y : E)
    (hr : 0 ≤ c.regularization) (hshort : c.curvature * ‖x - y‖ ≤ 1 / 2)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖x - c.anchor‖ ≤ c.scale) :
    ‖regularizedReply c x (F x) - regularizedReply c y (F y)‖ ≤
      2 * (c.scale + c.curvature * ‖regularizedReply c x (F x)‖) * ‖x - y‖ := by
  have hl := OracleTemplate.ConstrainedMonotone.regularized_local_bound hF hr c.anchor x y
    (le_refl ‖x - c.anchor‖) hshort
  rw [norm_sub_rev] at hl
  have hm := mul_le_mul_of_nonneg_right hscale (norm_nonneg (x - y))
  unfold regularizedReply
  nlinarith

lemma scaled_pair_local (c : StageConfig (E := E)) {F : E → E} {L0 η : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature) (x y : E)
    (hb : 0 < c.curvature) (hS : 0 ≤ c.scale) (hr : 0 ≤ c.regularization)
    (hη : 0 ≤ η) (hshort : c.curvature * ‖x - y‖ ≤ 1 / 2)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖x - c.anchor‖ ≤ c.scale)
    (hstep : η * trueDenominator c F x ≤ 1 / 16384) :
    η * ‖regularizedReply c x (F x) - regularizedReply c y (F y)‖ ≤ ‖x - y‖ / 8192 := by
  have hd : c.scale + c.curvature * ‖regularizedReply c x (F x)‖ ≤ trueDenominator c F x := by
    unfold trueDenominator
    nlinarith [mul_nonneg hb.le (div_nonneg hS hb.le)]
  have hc := mul_le_mul_of_nonneg_left hd hη
  have hs := mul_le_mul_of_nonneg_right hstep (norm_nonneg (x - y))
  have hc' := mul_le_mul_of_nonneg_right hc (norm_nonneg (x - y))
  have hl := mul_le_mul_of_nonneg_left (regularized_pair_local c hF x y hr hshort hscale) hη
  nlinarith

lemma adaptive_step_progress {previousStep D denominator : ℝ}
    (hD : 0 < D) (hlo : D ≤ denominator) (hhi : denominator ≤ 8 * D)
    (hprevious : 1 / 131072 - 5 / 4194304 ≤ previousStep * D) :
    1 / 131072 ≤ min (2 * previousStep) (1 / (16384 * denominator)) * D ∧
      min (2 * previousStep) (1 / (16384 * denominator)) * D ≤ 1 / 16384 := by
  have hp : 0 < denominator := hD.trans_le hlo
  have hcaplo : 1 / 131072 ≤ (1 / (16384 * denominator)) * D := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity : 0 < 16384 * denominator)]
    nlinarith
  have hcaphi : (1 / (16384 * denominator)) * D ≤ 1 / 16384 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 16384 * denominator)]
    nlinarith
  rw [min_mul_of_nonneg _ _ hD.le]
  exact ⟨le_min (by nlinarith) hcaplo, (min_le_right _ _).trans hcaphi⟩

lemma adaptive_step_progress_next {η D nextD : ℝ}
    (hstep : 1 / 131072 ≤ η * D)
    (hvariation : η * D - η * nextD ≤ 5 / 4194304) :
    1 / 131072 - 5 / 4194304 ≤ η * nextD := by linarith

lemma next_signal_below_clip (c : StageConfig (E := E)) {F : E → E} (x y : E) {η : ℝ}
    (hb : 0 < c.curvature) (hS : 0 ≤ c.scale) (hη : 0 < η)
    (hstep : η * trueDenominator c F x ≤ 1 / 16384)
    (hpair : c.curvature * ‖x - y‖ ≤ 5 / 1024)
    (hlocal : η * ‖regularizedReply c x (F x) - regularizedReply c y (F y)‖ ≤ ‖x - y‖ / 8192) :
    ‖regularizedReply c y (F y)‖ ≤ (1 / (1024 * c.curvature * η)) / 2 := by
  have hd : c.curvature * ‖regularizedReply c x (F x)‖ ≤ trueDenominator c F x := by
    unfold trueDenominator
    nlinarith [mul_nonneg hb.le (div_nonneg hS hb.le)]
  have hd' := mul_le_mul_of_nonneg_left hd hη.le
  have hl := mul_le_mul_of_nonneg_left hlocal hb.le
  have ht := norm_sub_le_norm_sub_add_norm_sub (regularizedReply c y (F y))
    (regularizedReply c x (F x)) (0 : E)
  simp only [sub_zero, norm_sub_rev (regularizedReply c y (F y))] at ht
  have ht' := mul_le_mul_of_nonneg_left ht (mul_nonneg hb.le hη.le)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (le_div_iff₀ (by positivity : 0 < 1024 * c.curvature * η)).mpr
  nlinarith

lemma initial_denominator_signal (c : StageConfig (E := E)) (F : E → E) (x : E)
    {denominator : ℝ} (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hden : trueDenominator c F x ≤ denominator) :
    ‖regularizedReply c x (F x)‖ ≤ (1 / (1024 * c.curvature * (1 / (16384 * denominator)))) / 2 := by
  have hdenpos := (trueDenominator_pos c F x hb hS).trans_le hden
  have hη : 0 < 1 / (16384 * denominator) := by positivity
  have hstep : (1 / (16384 * denominator)) * trueDenominator c F x ≤ 1 / 16384 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 16384 * denominator)]
    nlinarith
  exact next_signal_below_clip c x x hb hS.le hη hstep (by norm_num) (by simp)

structure StableState (X : Set E) (c : StageConfig (E := E)) (F : E → E) (state : StageState E) : Prop where
  bounds : StateBounds c state
  mem : state.base ∈ X
  query_mem : state.previousQuery ∈ X
  pair : c.curvature * ‖state.base - state.previousQuery‖ ≤ 3 / 1024
  denominator_lower : trueDenominator c F state.previousQuery ≤ state.pilotDenominator
  denominator_upper : state.pilotDenominator ≤ 8 * trueDenominator c F state.previousQuery
  progress : 1 / 131072 - 5 / 4194304 ≤ state.previousStep * trueDenominator c F state.previousQuery

lemma idealInitial_stable {X : Set E} (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (ξ : StepSamples Ω batch pilotBatch groups)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 ≤ c.radius) (hc : c.center ∈ X) :
    StableState X c F (idealInitial c F g batch pilotBatch groups ξ) := by
  let pilot := pilotFromSamples c g c.center pilotBatch groups ξ.1
  let denominator := repairedDenominator c F c.center pilot
  have hD := trueDenominator_pos c F c.center hb hS
  have hbounds := repairedDenominator_bounds c F c.center pilot hD.le
  have hdenpos : 0 < denominator := hD.trans_le hbounds.1
  have hprogress : 1 / 131072 ≤ (1 / (16384 * denominator)) * trueDenominator c F c.center := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity : 0 < 16384 * denominator)]
    nlinarith [hbounds.2]
  refine ⟨idealInitial_bounds c F g batch pilotBatch groups ξ hb hS hd, hc, hc, ?_, hbounds.1, hbounds.2, ?_⟩
  · simp only [idealInitial, initialWithDenominator, sub_self, norm_zero, mul_zero]
    norm_num
  · change 1 / 131072 - 5 / 4194304 ≤ (1 / (16384 * denominator)) * trueDenominator c F c.center
    linarith

lemma stable_step_scale {X : Set E} (c : StageConfig (E := E)) (F : E → E) (state : StageState E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hs : StableState X c F state) :
    1 / 131072 ≤ nextStep state * trueDenominator c F state.previousQuery ∧
      nextStep state * trueDenominator c F state.previousQuery ≤ 1 / 16384 :=
  adaptive_step_progress (trueDenominator_pos c F _ hb hS)
    hs.denominator_lower hs.denominator_upper hs.progress

lemma stable_predictor_distance {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E)) (F : E → E)
    (state : StageState E) (hb : 0 < c.curvature) (hS : 0 < c.scale) (hs : StableState X c F state) :
    c.curvature * ‖state.previousQuery - predictor proj state‖ ≤ 5 / 1024 := by
  have hη := GapNoisePastState.nextStep_pos state hs.bounds.2.2.2.1 (hS.trans_le hs.bounds.2.2.1)
  have hp := hproj.dist_le (state.base - nextStep state • state.previousReply) hs.mem
  have he : state.base - nextStep state • state.previousReply - state.base =
      -(nextStep state • state.previousReply) := by abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hp
  change ‖predictor proj state - state.base‖ ≤ _ at hp
  have hgrowth : nextStep state ≤ 2 * state.previousStep := min_le_left _ _
  have hg := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg state.previousReply)
  have hg' := mul_le_mul_of_nonneg_left hg hb.le
  have hp' := mul_le_mul_of_nonneg_left hp hb.le
  have ht := norm_sub_le_norm_sub_add_norm_sub state.previousQuery state.base (predictor proj state)
  rw [norm_sub_rev state.previousQuery state.base, norm_sub_rev state.base (predictor proj state)] at ht
  have ht' := mul_le_mul_of_nonneg_left ht hb.le
  nlinarith [hs.pair, hs.bounds.2.2.2.2.2]

lemma stable_step_conditions {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (state : StageState E) (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hr : 0 ≤ c.regularization) (hs : StableState X c F state)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖state.previousQuery - c.anchor‖ ≤ c.scale) :
    0 < nextStep state ∧
    nextStep state * ‖regularizedReply c state.previousQuery (F state.previousQuery) -
      regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (‖state.base - predictor proj state‖ + ‖state.base - state.previousQuery‖) / 16 ∧
    ‖regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (1 / (1024 * c.curvature * nextStep state)) / 2 := by
  have hη := GapNoisePastState.nextStep_pos state hs.bounds.2.2.2.1 (hS.trans_le hs.bounds.2.2.1)
  have hp := stable_predictor_distance hproj c F state hb hS hs
  have hstep := stable_step_scale c F state hb hS hs
  have hl := scaled_pair_local c hF state.previousQuery (predictor proj state) hb hS.le hr hη.le
    (by linarith) hscale hstep.2
  refine ⟨hη, ?_, next_signal_below_clip c _ _ hb hS.le hη hstep.2 hp hl⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub state.previousQuery state.base (predictor proj state)
  rw [norm_sub_rev state.previousQuery state.base] at ht
  nlinarith [norm_nonneg (state.base - predictor proj state), norm_nonneg (state.base - state.previousQuery)]

lemma stable_predictor_progress {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (state : StageState E) (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hr : 0 ≤ c.regularization) (hs : StableState X c F state)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖state.previousQuery - c.anchor‖ ≤ c.scale) :
    1 / 262144 ≤ nextStep state * (2 * c.scale +
      c.curvature * ‖regularizedReply c (predictor proj state) (F (predictor proj state))‖) := by
  have hη := GapNoisePastState.nextStep_pos state hs.bounds.2.2.2.1 (hS.trans_le hs.bounds.2.2.1)
  have hd := stable_predictor_distance hproj c F state hb hS hs
  have hstep := stable_step_scale c F state hb hS hs
  have hlocal := scaled_pair_local c hF state.previousQuery (predictor proj state) hb hS.le hr hη.le
    (by linarith) hscale hstep.2
  have hn := norm_sub_norm_le (regularizedReply c state.previousQuery (F state.previousQuery))
    (regularizedReply c (predictor proj state) (F (predictor proj state)))
  have hn' := mul_le_mul_of_nonneg_left hn (mul_nonneg hη.le hb.le)
  have hl' := mul_le_mul_of_nonneg_left hlocal hb.le
  have hvariation : nextStep state * trueDenominator c F state.previousQuery -
      nextStep state * trueDenominator c F (predictor proj state) ≤ 5 / 4194304 := by
    unfold trueDenominator
    nlinarith
  have hnext : 1 / 262144 ≤ nextStep state * trueDenominator c F (predictor proj state) := by
    linarith [hstep.1]
  rwa [trueDenominator_eq c F _ hb.ne'] at hnext

lemma idealStep_stable {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E)) (hc : c.center ∈ X)
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (g : E → Ω → E) (batch pilotBatch groups : ℕ) (state : StageState E)
    (ξ : StepSamples Ω batch pilotBatch groups) (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hr : 0 ≤ c.regularization) (hs : StableState X c F state)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖state.previousQuery - c.anchor‖ ≤ c.scale) :
    StableState X c F (idealStep proj c F g batch pilotBatch groups state ξ) := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · let x := predictor proj state
    let η := nextStep state
    let raw := (1 / (batch : ℝ)) • ∑ j, g x (ξ.2 j)
    let reply := clippedReply c η (regularizedReply c x raw)
    have hη : 0 < η := GapNoisePastState.nextStep_pos state hs.bounds.2.2.2.1
      (hS.trans_le hs.bounds.2.2.1)
    have hd := stable_predictor_distance hproj c F state hb hS hs
    have hstep := stable_step_scale c F state hb hS hs
    have hlocal := scaled_pair_local c hF state.previousQuery x hb hS.le hr hη.le
      (by dsimp [x]; linarith) hscale hstep.2
    have hn := norm_sub_norm_le (regularizedReply c state.previousQuery (F state.previousQuery))
      (regularizedReply c x (F x))
    have hn' := mul_le_mul_of_nonneg_left hn (mul_nonneg hη.le hb.le)
    have hl' := mul_le_mul_of_nonneg_left hlocal hb.le
    have hvariation : η * trueDenominator c F state.previousQuery - η * trueDenominator c F x ≤ 5 / 4194304 := by
      unfold trueDenominator
      nlinarith
    have hprogress := adaptive_step_progress_next hstep.1 hvariation
    have hnewcap := GapNoisePastState.clippedReply_cap c (regularizedReply c x raw) hb hη
    have hgrowth : η ≤ 2 * state.previousStep := min_le_left _ _
    have hg := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg state.previousReply)
    have hg' := mul_le_mul_of_nonneg_left hg hb.le
    have hpairs := LongTails.Proofs.GapNoiseTwoCenter.projected_pair_distance hproj state.base reply
      state.previousReply hη.le
    have hpairs' := mul_le_mul_of_nonneg_left hpairs hb.le
    have hpair : c.curvature * ‖proj (state.base - η • reply) - x‖ ≤ 3 / 1024 := by
      change c.curvature * ‖proj (state.base - η • reply) - predictor proj state‖ ≤ _
      dsimp only [predictor, reply, η] at *
      nlinarith [hs.bounds.2.2.2.2.2]
    have hden := repairedDenominator_bounds c F x
      (pilotFromSamples c g x pilotBatch groups ξ.1) (trueDenominator_pos c F x hb hS).le
    refine ⟨idealStep_bounds hproj c hc F g batch pilotBatch groups state ξ hb hS hs.bounds,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [idealStep, sampledStep, advance, hp, ite_true, updatedState] using
        hproj.mem (state.base - η • reply)
    · simp only [idealStep, sampledStep, advance, hp, ite_true, updatedState]
      exact hproj.mem _
    · simpa only [idealStep, sampledStep, advance, hp, ite_true, updatedState] using hpair
    · simpa only [idealStep, sampledStep, advance, hp, ite_true, updatedState] using hden.1
    · simpa only [idealStep, sampledStep, advance, hp, ite_true, updatedState] using hden.2
    · simpa only [idealStep, sampledStep, advance, hp, ite_true, updatedState] using hprogress
  · simp only [idealStep, hp, ite_false]
    exact ⟨hs.bounds, hs.mem, hs.query_mem, hs.pair, hs.denominator_lower, hs.denominator_upper, hs.progress⟩

lemma low_energy_permitted {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (state : StageState E) (z p : E) (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hr : 0 ≤ c.regularization) (hd : 0 < c.radius) (hs : StableState X c F state)
    (ha : state.active = true) (hp : p ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p (-regularizedReply c p (F p)))
    (hzp : ‖z - p‖ ≤ c.radius) (hpc : ‖p - c.center‖ ≤ c.radius)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖p - c.anchor‖ ≤ c.scale)
    (hnorm : c.curvature * ‖regularizedReply c p (F p)‖ ≤ c.scale)
    (he : energy c F z state ≤ 1024 * c.radius ^ 2) :
    permitted c state (predictor proj state) := by
  have hbds := low_energy_bounds c F z state hd hs.bounds.2.2.2.1.le he
  have hη := GapNoisePastState.nextStep_pos state hs.bounds.2.2.2.1 (hS.trans_le hs.bounds.2.2.1)
  have hwp : ‖state.base - p‖ ≤ 33 * c.radius := by
    have ht := norm_sub_le_norm_sub_add_norm_sub state.base z p
    linarith [hbds.1]
  have hwc : ‖state.base - c.center‖ ≤ 34 * c.radius := by
    have ht := norm_sub_le_norm_sub_add_norm_sub state.base p c.center
    linarith
  have hxprev : ‖state.previousQuery - p‖ ≤ 97 * c.radius := by
    have ht := norm_sub_le_norm_sub_add_norm_sub state.previousQuery state.base p
    rw [norm_sub_rev state.previousQuery state.base] at ht
    linarith [hbds.2.1]
  have hgrowth : nextStep state ≤ 2 * state.previousStep := min_le_left _ _
  have herr : nextStep state *
      ‖state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)‖ ≤ 14 * c.radius := by
    have hm := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg
      (state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)))
    linarith [hbds.2.2]
  refine ⟨ha, by linarith, ?_⟩
  by_cases hsmall : c.curvature * c.radius ≤ 1 / 256
  · have hshort : c.curvature * ‖p - state.previousQuery‖ ≤ 1 / 2 := by
      rw [norm_sub_rev]
      have hm := mul_le_mul_of_nonneg_left hxprev hb.le
      nlinarith
    have hlocal := regularized_pair_local c hF p state.previousQuery hr hshort hscale
    rw [norm_sub_rev p state.previousQuery, norm_sub_rev (regularizedReply c p (F p))] at hlocal
    have hlocal' : ‖regularizedReply c state.previousQuery (F state.previousQuery) -
        regularizedReply c p (F p)‖ ≤ 4 * c.scale * (97 * c.radius) := by
      have hh := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (state.previousQuery - p))
      have hd' := mul_le_mul_of_nonneg_left hxprev (by positivity : 0 ≤ 4 * c.scale)
      nlinarith
    have hηmax : nextStep state ≤ 1 / (16384 * c.scale) :=
      (min_le_right _ _).trans
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hs.bounds.2.2.1]))
    have hprod : nextStep state * c.scale ≤ 1 / 16384 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 16384 * c.scale)).mp hηmax
      nlinarith
    have hlocscaled : nextStep state *
        ‖regularizedReply c state.previousQuery (F state.previousQuery) - regularizedReply c p (F p)‖ ≤ c.radius := by
      have hm := mul_le_mul_of_nonneg_left hlocal' hη.le
      have hh := mul_le_mul_of_nonneg_right hprod hd.le
      nlinarith
    have hpredict := LongTails.Proofs.GapNoiseTwoCenter.past_predictor_root_distance
      (H := fun x => regularizedReply c x (F x)) hproj hp hroot state.base state.previousQuery
      (state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)) hη.le
    have hcancel : regularizedReply c state.previousQuery (F state.previousQuery) +
      (state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)) = state.previousReply := by abel
    rw [hcancel] at hpredict
    change ‖predictor proj state - p‖ ≤ _ at hpredict
    have ht := norm_sub_le_norm_sub_add_norm_sub (predictor proj state) p c.center
    linarith
  · have hpredict := hproj.dist_le (state.base - nextStep state • state.previousReply) hs.mem
    have hcancel : state.base - nextStep state • state.previousReply - state.base =
        -(nextStep state • state.previousReply) := by abel
    rw [hcancel, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hpredict
    change ‖predictor proj state - state.base‖ ≤ _ at hpredict
    have hg := mul_le_mul_of_nonneg_right hgrowth (norm_nonneg state.previousReply)
    have hg' := mul_le_mul_of_nonneg_left hg hb.le
    have hdisp : nextStep state * ‖state.previousReply‖ ≤ c.radius := by
      nlinarith [hs.bounds.2.2.2.2.2]
    have ht := norm_sub_le_norm_sub_add_norm_sub (predictor proj state) state.base c.center
    linarith

noncomputable def activeLoss (proj : E → E) (c : StageConfig (E := E)) (z : E) (state : StageState E) : ℝ := by
  classical
  exact if permitted c state (predictor proj state) then ‖predictor proj state - z‖ ^ 2 else 0

lemma activeLoss_nonneg (proj : E → E) (c : StageConfig (E := E)) (z : E) (state : StageState E) :
    0 ≤ activeLoss proj c z state := by unfold activeLoss; split <;> positivity

lemma activeLoss_bound (proj : E → E) (c : StageConfig (E := E)) (z : E) (state : StageState E) :
    activeLoss proj c z state ≤ (64 * c.radius + ‖c.center - z‖) ^ 2 := by
  classical
  by_cases hp : permitted c state (predictor proj state)
  · have ht := norm_sub_le_norm_sub_add_norm_sub (predictor proj state) c.center z
    have hn : ‖predictor proj state - z‖ ≤ 64 * c.radius + ‖c.center - z‖ := by linarith [hp.2.2]
    simpa only [activeLoss, hp, ite_true] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  · simp only [activeLoss, hp, ite_false]
    positivity

lemma idealStep_active_iff (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E) (ξ : StepSamples Ω batch pilotBatch groups) :
    (idealStep proj c F g batch pilotBatch groups state ξ).active = true ↔
      permitted c state (predictor proj state) := by
  classical
  by_cases hp : permitted c state (predictor proj state) <;>
    simp [idealStep, sampledStep, advance, hp, updatedState]

lemma idealStep_total (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E) (ξ : StepSamples Ω batch pilotBatch groups)
    (ha : (idealStep proj c F g batch pilotBatch groups state ξ).active = true) :
    (idealStep proj c F g batch pilotBatch groups state ξ).total = state.total + predictor proj state := by
  have hp := (idealStep_active_iff proj c F g batch pilotBatch groups state ξ).mp ha
  simp only [idealStep, sampledStep, advance, hp, ite_true, updatedState]

lemma stopped_exit_energy {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E)) (hc : c.center ∈ X)
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (g : E → Ω → E) (batch pilotBatch groups steps : ℕ) (state : StageState E) (z p : E)
    (ξ : Fin steps → StepSamples Ω batch pilotBatch groups)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization) (hd : 0 < c.radius)
    (hs : StableState X c F state) (ha : state.active = true) (hp : p ∈ X)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p (-regularizedReply c p (F p)))
    (hzp : ‖z - p‖ ≤ c.radius) (hpc : ‖p - c.center‖ ≤ c.radius)
    (hrootScale : L0 + c.regularization + c.curvature * c.regularization * ‖p - c.anchor‖ ≤ c.scale)
    (hnorm : c.curvature * ‖regularizedReply c p (F p)‖ ≤ c.scale)
    (hscale : ∀ x, ‖x - c.center‖ ≤ 64 * c.radius →
      L0 + c.regularization + c.curvature * c.regularization * ‖x - c.anchor‖ ≤ c.scale)
    (hfailed : (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ).active ≠ true) :
    1024 * c.radius ^ 2 < energy c F z (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ) := by
  let Inv := fun st : StageState E => StableState X c F st ∧
    (st.active = true ∨ 1024 * c.radius ^ 2 < energy c F z st)
  have hinv (st : StageState E) (hst : Inv st) (samples : StepSamples Ω batch pilotBatch groups) :
      Inv (idealStep proj c F g batch pilotBatch groups st samples) := by
    refine ⟨idealStep_stable hproj c hc hF g batch pilotBatch groups st samples hb hS hr hst.1
      (hscale _ hst.1.bounds.2.1), ?_⟩
    by_cases hguard : permitted c st (predictor proj st)
    · exact Or.inl ((idealStep_active_iff proj c F g batch pilotBatch groups st samples).mpr hguard)
    · apply Or.inr
      have hhigh : 1024 * c.radius ^ 2 < energy c F z st := by
        rcases hst.2 with hactive | hhigh
        · apply lt_of_not_ge
          intro hlow
          exact hguard (low_energy_permitted hproj c hF st z p hb hS hr hd hst.1 hactive hp hroot
            hzp hpc hrootScale hnorm hlow)
        · exact hhigh
      simpa only [idealStep, hguard, ite_false, energy_inactive] using hhigh
  have hfinal := OracleTemplate.ClippedExtragradient.iterateSamples_invariant hinv steps state
    (show Inv state from ⟨hs, Or.inl ha⟩) ξ
  exact hfinal.2.resolve_left hfailed

lemma mean_squared_distance {N : ℕ} (hN : 0 < N) (points : Fin N → E) (z : E) :
    ‖(1 / (N : ℝ)) • ∑ i, points i - z‖ ^ 2 ≤
      (∑ i, ‖points i - z‖ ^ 2) / N := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have he : (1 / (N : ℝ)) • ∑ i, points i - z =
      (1 / (N : ℝ)) • ∑ i, (points i - z) := by
    rw [Finset.sum_sub_distrib, smul_sub]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hn.ne']
  have hnorm := norm_sum_le (Finset.univ : Finset (Fin N)) (fun i => points i - z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin N => ‖points i - z‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn), mul_pow]
  calc
    _ ≤ (1 / (N : ℝ)) ^ 2 * ((N : ℝ) * ∑ i, ‖points i - z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hs.trans hc) (sq_nonneg _)
    _ = _ := by field_simp

lemma active_trial_mean_bound (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (hN : 0 < steps) (z : E)
    (state : StageState E) (hzero : state.total = 0) (ξ : Fin steps → StepSamples Ω batch pilotBatch groups)
    (ha : (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ).active = true) :
    ‖trialOutput c steps (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ) - z‖ ^ 2 ≤
      GapNoiseIteration.accumulatedEnergy (idealStep proj c F g batch pilotBatch groups)
        (fun _ => 0) (activeLoss proj c z) 1 steps state ξ / steps := by
  have hactive (st : StageState E) (samples : StepSamples Ω batch pilotBatch groups)
      (h : (idealStep proj c F g batch pilotBatch groups st samples).active = true) : st.active = true :=
    ((idealStep_active_iff proj c F g batch pilotBatch groups st samples).mp h).1
  have htotal := GapNoiseIteration.active_total_trace (active := fun st : StageState E => st.active = true)
    (point := predictor proj) (total := StageState.total) hactive
    (fun st samples h => idealStep_total proj c F g batch pilotBatch groups st samples h) steps state ξ ha
  have hmatch (st : StageState E) (samples : StepSamples Ω batch pilotBatch groups)
      (h : (idealStep proj c F g batch pilotBatch groups st samples).active = true) :
      activeLoss proj c z st = ‖predictor proj st - z‖ ^ 2 := by
    have hp := (idealStep_active_iff proj c F g batch pilotBatch groups st samples).mp h
    simp only [activeLoss, hp, ite_true]
  have hloss := GapNoiseIteration.active_loss_trace (active := fun st : StageState E => st.active = true)
    (point := predictor proj) (value := fun x => ‖x - z‖ ^ 2) hactive hmatch steps state ξ ha
  rw [hzero, zero_add] at htotal
  simp only [trialOutput, ha, ite_true]
  rw [htotal, hloss]
  exact mean_squared_distance hN _ z

lemma bad_trial_accumulated_energy (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups steps : ℕ) (hN : 0 < steps) (z p : E)
    (state : StageState E) (hzero : state.total = 0) (ξ : Fin steps → StepSamples Ω batch pilotBatch groups)
    {κ : ℝ} (hd : 0 < c.radius) (hbudget : (2 : ℝ) ^ 23 ≤ κ * steps)
    (hzp : ‖z - p‖ ≤ c.radius / 24)
    (hexit : (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ).active ≠ true →
      1024 * c.radius ^ 2 < energy c F z (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
        (idealStep proj c F g batch pilotBatch groups) steps state ξ))
    (hbad : c.radius / 12 < ‖trialOutput c steps (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps state ξ) - p‖) :
    1024 * c.radius ^ 2 < GapNoiseIteration.accumulatedEnergy
      (idealStep proj c F g batch pilotBatch groups) (energy c F z) (activeLoss proj c z) κ steps state ξ := by
  have hNr : 0 < (steps : ℝ) := Nat.cast_pos.mpr hN
  have hκ : 0 < κ := by nlinarith
  let final := OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (idealStep proj c F g batch pilotBatch groups) steps state ξ
  by_cases ha : final.active = true
  · have hmean := active_trial_mean_bound proj c F g batch pilotBatch groups steps hN z state hzero ξ ha
    have hfar : c.radius / 24 < ‖trialOutput c steps final - z‖ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (trialOutput c steps final) z p
      change c.radius / 12 < ‖trialOutput c steps final - p‖ at hbad
      linarith
    have hsquare : (c.radius / 24) ^ 2 < ‖trialOutput c steps final - z‖ ^ 2 := by
      nlinarith [norm_nonneg (trialOutput c steps final - z)]
    have hloss := (lt_div_iff₀ hNr).mp (hsquare.trans_le hmean)
    have hmul := mul_lt_mul_of_pos_left hloss hκ
    have hbudget' := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (c.radius / 24))
    rw [GapNoiseIteration.accumulatedEnergy_decomposition]
    have henergy := energy_nonneg c F z final
    dsimp only [final] at henergy
    nlinarith [sq_pos_of_pos hd]
  · exact (hexit ha).trans_le (GapNoiseIteration.terminal_energy_le_accumulatedEnergy hκ.le
      (activeLoss_nonneg proj c z) steps state ξ)

lemma trial_failure_probability {W : Type*} [MeasurableSpace W] (proj : E → E) (c : StageConfig (E := E))
    (F : E → E) (g : E → Ω → E) (batch pilotBatch groups steps : ℕ) (hN : 0 < steps) (z p : E)
    (initial : W → StageState E) (samples : W → Fin steps → StepSamples Ω batch pilotBatch groups)
    (hzero : ∀ ω, (initial ω).total = 0) {κ : ℝ} (hd : 0 < c.radius)
    (hbudget : (2 : ℝ) ^ 23 ≤ κ * steps) (hzp : ‖z - p‖ ≤ c.radius / 24) (P : Measure W)
    (hexit : ∀ ω, (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps (initial ω) (samples ω)).active ≠ true →
      1024 * c.radius ^ 2 < energy c F z (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
        (idealStep proj c F g batch pilotBatch groups) steps (initial ω) (samples ω)))
    (hi : Integrable (fun ω => GapNoiseIteration.accumulatedEnergy
      (idealStep proj c F g batch pilotBatch groups) (energy c F z) (activeLoss proj c z) κ steps (initial ω) (samples ω)) P)
    (hmean : (∫ ω, GapNoiseIteration.accumulatedEnergy
      (idealStep proj c F g batch pilotBatch groups) (energy c F z) (activeLoss proj c z) κ steps (initial ω) (samples ω) ∂P) ≤
        2 * c.radius ^ 2) :
    P {ω | c.radius / 12 < ‖trialOutput c steps (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps (initial ω) (samples ω)) - p‖} ≤ ENNReal.ofReal (1 / 512 : ℝ) := by
  have hNr : 0 < (steps : ℝ) := Nat.cast_pos.mpr hN
  have hκ : 0 ≤ κ := by nlinarith
  have hn (ω : W) : 0 ≤ GapNoiseIteration.accumulatedEnergy
      (idealStep proj c F g batch pilotBatch groups) (energy c F z) (activeLoss proj c z) κ steps (initial ω) (samples ω) :=
    (energy_nonneg c F z _).trans (GapNoiseIteration.terminal_energy_le_accumulatedEnergy hκ
      (activeLoss_nonneg proj c z) steps (initial ω) (samples ω))
  have hprob := GapNoiseMoments.nonnegative_energy_event
    (bad := {ω | c.radius / 12 < ‖trialOutput c steps (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
      (idealStep proj c F g batch pilotBatch groups) steps (initial ω) (samples ω)) - p‖}) hi hn
    (by positivity : 0 < 1024 * c.radius ^ 2)
    (fun ω hbad => (bad_trial_accumulated_energy proj c F g batch pilotBatch groups steps hN z p
      (initial ω) (hzero ω) (samples ω) hd hbudget hzp (hexit ω) hbad).le) hmean
  have hratio : 2 * c.radius ^ 2 / (1024 * c.radius ^ 2) = (1 / 512 : ℝ) := by field_simp; norm_num
  simpa only [hratio] using hprob

section Measurability

open MeasureTheory
open LongTails.Proofs.GapNoisePastState
open LongTails.Proofs.GapNoiseSampling

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

@[fun_prop] lemma measurable_trueDenominator (c : StageConfig (E := E)) {F : E → E}
    (hF : Measurable F) : Measurable (trueDenominator c F) := by
  unfold trueDenominator regularizedReply
  fun_prop

@[fun_prop] lemma measurable_repairedDenominator (c : StageConfig (E := E)) {F : E → E}
    (hF : Measurable F) : Measurable (Function.uncurry (repairedDenominator c F)) := by
  unfold repairedDenominator Function.uncurry
  fun_prop

lemma measurable_idealInitial (c : StageConfig (E := E)) {F : E → E} (hF : Measurable F)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ) :
    Measurable (idealInitial c F g batch pilotBatch groups) := by
  have hp : Measurable (fun ξ : StepSamples Ω batch pilotBatch groups =>
      pilotFromSamples c g c.center pilotBatch groups ξ.1) :=
    measurable_pilotFromSamples c hg measurable_const pilotBatch groups measurable_fst
  have hd := (measurable_repairedDenominator c hF).comp ((measurable_const (a := c.center)).prodMk hp)
  have hm : Measurable (fun ξ : StepSamples Ω batch pilotBatch groups =>
      (1 / (batch : ℝ)) • ∑ j, g c.center (ξ.2 j)) :=
    measurable_batch_reply hg measurable_const measurable_snd
  have hi : Measurable (Function.uncurry (initialWithDenominator c)) := by
    unfold initialWithDenominator Function.uncurry
    apply measurable_state_mk <;> fun_prop
  exact hi.comp (hd.prodMk hm)

lemma measurable_idealStep {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) {F : E → E} (hF : Measurable F)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ) :
    Measurable (Function.uncurry (idealStep proj c F g batch pilotBatch groups)) := by
  classical
  have hx : Measurable (fun w : StageState E × StepSamples Ω batch pilotBatch groups =>
      predictor proj w.1) := (measurable_predictor hproj).comp measurable_fst
  have hp := measurable_pilotFromSamples c hg hx pilotBatch groups (measurable_fst.comp measurable_snd)
  have hd := (measurable_repairedDenominator c hF).comp (hx.prodMk hp)
  have hs := measurable_sampledStep hproj c hg batch pilotBatch groups
  unfold idealStep Function.uncurry
  apply Measurable.ite (measurableSet_permitted c measurable_fst hx)
  · apply measurable_state_mk
    · exact measurable_base.comp hs
    · exact measurable_previousQuery.comp hs
    · exact measurable_previousReply.comp hs
    · exact hd
    · exact measurable_previousStep.comp hs
    · exact measurable_total.comp hs
    · exact measurable_active.comp hs
  · apply measurable_state_mk <;> fun_prop

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma idealStep_integral_reduce (p : Measure Ω) [IsProbabilityMeasure p]
    (proj : E → E) (c : StageConfig (E := E)) (F : E → E) (g : E → Ω → E)
    (batch pilotBatch groups : ℕ) (state : StageState E) (z : E) :
    (∫ ξ : StepSamples Ω batch pilotBatch groups,
      energy c F z (idealStep proj c F g batch pilotBatch groups state ξ)
      ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => p))).prod
        (Measure.pi (fun _ : Fin batch => p))) =
    ∫ ξ : Fin batch → Ω, energy c F z (advance proj c state (predictor proj state) 0
      ((1 / (batch : ℝ)) • ∑ j, g (predictor proj state) (ξ j)))
      ∂Measure.pi (fun _ : Fin batch => p) := by
  simp_rw [idealStep_energy_raw]
  rw [integral_fun_snd (fun ξ : Fin batch → Ω => energy c F z
    (advance proj c state (predictor proj state) 0
      ((1 / (batch : ℝ)) • ∑ j, g (predictor proj state) (ξ j))))]
  simp only [probReal_univ, one_smul]

lemma idealStep_energy_integral [CompleteSpace E] (p : Measure Ω) [IsProbabilityMeasure p]
    {X : Set E} {proj : E → E} (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj)
    (c : StageConfig (E := E)) {F : E → E} {L0 : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (batch pilotBatch groups : ℕ) (hbatch : 0 < batch) (state : StageState E) (z : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hs : StableState X c F state) (hz : z ∈ X)
    (hscale : L0 + c.regularization + c.curvature * c.regularization * ‖state.previousQuery - c.anchor‖ ≤ c.scale)
    (hguard : permitted c state (predictor proj state))
    (hi : Integrable (g (predictor proj state)) p)
    (hmean : (∫ ω, g (predictor proj state) ω ∂p) = F (predictor proj state))
    (hvi : Integrable (fun ω => ‖g (predictor proj state) ω - F (predictor proj state)‖ ^ 2) p)
    {V D : ℝ} (hv : (∫ ω, ‖g (predictor proj state) ω - F (predictor proj state)‖ ^ 2 ∂p) ≤ V)
    (hD : ‖predictor proj state - z‖ ≤ D) :
    (∫ ξ : StepSamples Ω batch pilotBatch groups,
      energy c F z (idealStep proj c F g batch pilotBatch groups state ξ)
      ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => p))).prod
        (Measure.pi (fun _ : Fin batch => p))) ≤
      energy c F z state - 7 / 8 * ‖state.base - predictor proj state‖ ^ 2 -
        ‖state.base - state.previousQuery‖ ^ 2 / 8 -
        2 * nextStep state * ⟪regularizedReply c (predictor proj state) (F (predictor proj state)),
          predictor proj state - z⟫ + (30 + 4096 * c.curvature * D) * nextStep state ^ 2 * (V / batch) := by
  rw [idealStep_integral_reduce]
  have hc := stable_step_conditions hproj c hF state hb hS hr hs hscale
  have hm := OracleTemplate.LightTail.finite_mean_integral hi batch hbatch
  have hgm : Measurable (g (predictor proj state)) := hg.comp measurable_prodMk_left
  have hmom := OracleTemplate.RobustGradient.finite_mean_variance
    hgm hi _ hvi hmean batch hbatch
  have hraw : Measurable (fun ξ : Fin batch → Ω =>
      (1 / (batch : ℝ)) • ∑ j, g (predictor proj state) (ξ j)) :=
    GapNoiseSampling.measurable_batch_reply hg measurable_const measurable_id
  apply active_step_integral hproj c hF.cont.measurable z state 0 hraw hm.1
    (hm.2.trans hmean) hmom.1 _ hz hb hc.1 hguard hc.2.1 hc.2.2 hD
  rw [hmom.2]
  exact div_le_div_of_nonneg_right hv (Nat.cast_nonneg batch)

lemma measurable_activeLoss {proj : E → E} (hproj : Measurable proj)
    (c : StageConfig (E := E)) (z : E) : Measurable (activeLoss proj c z) := by
  classical
  unfold activeLoss
  apply Measurable.ite (measurableSet_permitted c measurable_id (measurable_predictor hproj))
  · fun_prop
  · exact measurable_const

lemma ideal_initial_energy_integrable [FiniteDimensional ℝ E] {batch pilotBatch groups : ℕ}
    {P : Measure (StepSamples Ω batch pilotBatch groups)} [IsProbabilityMeasure P]
    (c : StageConfig (E := E)) {F : E → E} (hF : Continuous F) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (z : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 ≤ c.radius) :
    Integrable (fun ξ => energy c F z (idealInitial c F g batch pilotBatch groups ξ)) P := by
  obtain ⟨M, hM⟩ := local_trueReply_bounded c hF
  have hm := (measurable_energy c hF.measurable z).comp
    (measurable_idealInitial c hF.measurable hg batch pilotBatch groups)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((64 * c.radius + 1 / (1024 * c.curvature) + ‖z - c.center‖) ^ 2 +
      (128 * c.radius + 1 / (1024 * c.curvature)) ^ 2 / 4 +
      24 * (1 / (1024 * c.curvature) + (1 / (16384 * c.scale)) * M) ^ 2)
  apply Filter.Eventually.of_forall
  intro ξ
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _ _ _ _)]
  exact state_energy_bound c F z _ hb (idealInitial_bounds c F g batch pilotBatch groups ξ hb hS hd) hM

lemma ideal_initial_energy_bound [FiniteDimensional ℝ E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : StageConfig (E := E)) {F : E → E} (hF : Continuous F) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (batch pilotBatch groups : ℕ) (hbatch : 0 < batch) (z : E)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 ≤ c.radius)
    (hi : Integrable (g c.center) μ) (hmean : (∫ ω, g c.center ω ∂μ) = F c.center)
    (hvi : Integrable (fun ω => ‖g c.center ω - F c.center‖ ^ 2) μ)
    {V : ℝ} (hv : (∫ ω, ‖g c.center ω - F c.center‖ ^ 2 ∂μ) ≤ V) :
    (∫ ξ : StepSamples Ω batch pilotBatch groups, energy c F z (idealInitial c F g batch pilotBatch groups ξ)
      ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => μ))).prod
        (Measure.pi (fun _ : Fin batch => μ))) ≤
      ‖c.center - z‖ ^ 2 + 24 * (1 / (16384 * trueDenominator c F c.center)) ^ 2 * (V / batch) := by
  have hD := trueDenominator_pos c F c.center hb hS
  have hV : 0 ≤ V := (integral_nonneg (fun ω => sq_nonneg ‖g c.center ω - F c.center‖)).trans hv
  have hgm : Measurable (g c.center) := hg.comp measurable_prodMk_left
  have hm := OracleTemplate.LightTail.finite_mean_integral hi batch hbatch
  have hmom := OracleTemplate.RobustGradient.finite_mean_variance hgm hi _ hvi hmean batch hbatch
  have hraw : Measurable (fun ξ : Fin batch → Ω => (1 / (batch : ℝ)) • ∑ j, g c.center (ξ j)) :=
    GapNoiseSampling.measurable_batch_reply hg measurable_const measurable_id
  have hvbatch : (∫ ξ : Fin batch → Ω, ‖(1 / (batch : ℝ)) • ∑ j, g c.center (ξ j) - F c.center‖ ^ 2
      ∂Measure.pi (fun _ : Fin batch => μ)) ≤ V / batch := by
    rw [hmom.2]
    exact div_le_div_of_nonneg_right hv (Nat.cast_nonneg batch)
  have hper (pilots : Fin (groups + 1) → Fin pilotBatch → Ω) :
      (∫ ξ : Fin batch → Ω, energy c F z (idealInitial c F g batch pilotBatch groups (pilots, ξ))
        ∂Measure.pi (fun _ : Fin batch => μ)) ≤
      ‖c.center - z‖ ^ 2 + 24 * (1 / (16384 * trueDenominator c F c.center)) ^ 2 * (V / batch) := by
    let denominator := repairedDenominator c F c.center (pilotFromSamples c g c.center pilotBatch groups pilots)
    have hlo := (repairedDenominator_bounds c F c.center
      (pilotFromSamples c g c.center pilotBatch groups pilots) hD.le).1
    have hdenpos : 0 < denominator := hD.trans_le hlo
    have hs := initial_denominator_signal c F c.center hb hS hlo
    have hh := initial_energy_integral c F z hdenpos hb hraw hm.1 (hm.2.trans hmean) hmom.1 hvbatch hs
    have hη : 1 / (16384 * denominator) ≤ 1 / (16384 * trueDenominator c F c.center) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have hη2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (16384 * denominator)) hη 2
    have hmul := mul_le_mul_of_nonneg_right hη2 (by positivity : 0 ≤ 24 * (V / batch))
    change (∫ ξ : Fin batch → Ω, energy c F z (initialWithDenominator c denominator
      ((1 / (batch : ℝ)) • ∑ j, g c.center (ξ j))) ∂Measure.pi (fun _ : Fin batch => μ)) ≤ _
    nlinarith
  have hjoint := ideal_initial_energy_integrable
    (P := (Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => μ))).prod
      (Measure.pi (fun _ : Fin batch => μ))) c hF hg z hb hS hd
  rw [integral_prod _ hjoint]
  have hh := integral_mono hjoint.integral_prod_left (integrable_const _) hper
  simpa only [integral_const, probReal_univ, one_smul] using hh

lemma ideal_iterate_energy_integrable {batch pilotBatch groups : ℕ} {P : Measure (StepSamples Ω batch pilotBatch groups)}
    [IsProbabilityMeasure P] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    (hc : c.center ∈ X) {F : E → E} (hF : Measurable F)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (state : StageState E) (z : E) (hb : 0 < c.curvature) (hS : 0 < c.scale)
    (hs : StateBounds c state) {M : ℝ}
    (hH : ∀ x, ‖x - c.center‖ ≤ 64 * c.radius → ‖regularizedReply c x (F x)‖ ≤ M) (steps : ℕ) :
    Integrable (fun ξ : Fin steps → StepSamples Ω batch pilotBatch groups =>
      energy c F z (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
        (idealStep proj c F g batch pilotBatch groups) steps state ξ))
      (Measure.pi fun _ : Fin steps => P) := by
  have hm := (measurable_energy c hF z).comp
    ((OracleTemplate.ClippedExtragradient.measurable_iterateSamples
      (measurable_idealStep hproj.lipschitz.continuous.measurable c hF hg batch pilotBatch groups) steps).comp
        ((measurable_const (a := state)).prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((64 * c.radius + 1 / (1024 * c.curvature) + ‖z - c.center‖) ^ 2 +
      (128 * c.radius + 1 / (1024 * c.curvature)) ^ 2 / 4 +
      24 * (1 / (1024 * c.curvature) + (1 / (16384 * c.scale)) * M) ^ 2)
  apply Filter.Eventually.of_forall
  intro ξ
  simp only [Function.comp_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _ _ _ _)]
  exact state_energy_bound c F z _ hb
    (OracleTemplate.ClippedExtragradient.iterateSamples_invariant
      (fun st hst samples => idealStep_bounds hproj c hc F g batch pilotBatch groups st samples hb hS hst)
      steps state hs ξ) hH

end Measurability

end LongTails.Proofs.GapNoiseStopped
