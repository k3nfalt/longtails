import LongTails.Proofs.GapNoiseStopped
import LongTails.Proofs.GapNoiseTuning
import LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseStageDrift

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseStopped
open LongTails.Proofs.GapNoiseTwoCenter

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regularized_root_gap {X : Set E} (c : StageConfig (E := E)) (F : E → E) (p s : E)
    (hp : p ∈ X) (hs : s ∈ X) (hr : 0 ≤ c.regularization)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p (-regularizedReply c p (F p)))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s)) :
    ⟪F p - F s, p - s⟫ ≤ c.regularization * ‖p - c.anchor‖ * ‖p - s‖ := by
  have hn := OracleTemplate.ConstrainedMonotone.normal_monotone hp hs hroot hsolution
  have he : -regularizedReply c p (F p) - -F s =
      -(F p - F s) - c.regularization • (p - c.anchor) := by unfold regularizedReply; module
  rw [he, inner_sub_left, inner_neg_left, real_inner_smul_left] at hn
  have hi := real_inner_le_norm (-(p - c.anchor)) (p - s)
  rw [inner_neg_left, norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_left hi hr
  nlinarith

lemma root_operator_difference {F : E → E} {L0 b R G ε : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 b) (p s : E) (hR : 0 < R)
    (hG : ‖F s‖ ≤ G) (hgap : ⟪F p - F s, p - s⟫ ≤ ε * R) (hps : ‖p - s‖ ≤ R) :
    ‖F p - F s‖ ≤ ε * (1 + 2 * b * R) + 4 * (L0 + b * G) * R := by
  let h := R / (1 + 2 * b * R)
  have hb := hF.L1_nonneg
  have hh : 0 < h := by dsimp [h]; positivity
  have hhR : h ≤ R := by
    dsimp [h]
    rw [div_le_iff₀ (by positivity : 0 < 1 + 2 * b * R)]
    nlinarith [mul_nonneg hb (sq_nonneg R)]
  have hcap : b * h ≤ 1 / 2 := by
    dsimp [h]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 1 + 2 * b * R)]
    nlinarith [mul_nonneg hb hR.le]
  have ho := OracleTemplate.ConstrainedMonotone.one_point hF p s hh hcap
  have hL : 0 ≤ L0 + b * G := by
    have hG0 := (norm_nonneg _).trans hG
    have h0 := hF.L0_pos
    positivity
  have hnorm : 2 * (L0 + b * ‖F s‖) * h * (‖p - s‖ + h) ≤ 4 * (L0 + b * G) * h * R := by
    have hcoef := mul_le_mul_of_nonneg_left hG hb
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hh.le (by positivity : 0 ≤ ‖p - s‖ + h))
    have hdist := mul_le_mul_of_nonneg_left (show ‖p - s‖ + h ≤ 2 * R by linarith)
      (mul_nonneg hL hh.le)
    nlinarith
  have he : h * (1 + 2 * b * R) = R := by dsimp [h]; field_simp
  have heε := congrArg (fun u : ℝ => ε * u) he
  apply (mul_le_mul_iff_left₀ hh).mp
  nlinarith

lemma query_gap_bound (c : StageConfig (E := E)) (F : E → E) (x s : E) {D : ℝ}
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hxs : ‖x - s‖ ≤ D)
    (hscale : c.curvature * (‖F s‖ + c.regularization * ‖x - c.anchor‖) ≤ c.scale) :
    ⟪F x - F s, x - s⟫ ≤ D * (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) := by
  have hshift : ‖F s‖ + c.regularization * ‖x - c.anchor‖ ≤ c.scale / c.curvature := by
    rw [le_div_iff₀ hb]
    nlinarith
  have hFbound : ‖F x‖ ≤ ‖regularizedReply c x (F x)‖ + c.regularization * ‖x - c.anchor‖ := by
    have ht := norm_sub_le (regularizedReply c x (F x)) (c.regularization • (x - c.anchor))
    simpa only [regularizedReply, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] using ht
  have hn := norm_sub_le (F x) (F s)
  have hdiff : ‖F x - F s‖ ≤ ‖regularizedReply c x (F x)‖ + c.scale / c.curvature := by linarith
  calc
    _ ≤ ‖F x - F s‖ * ‖x - s‖ := real_inner_le_norm _ _
    _ ≤ (‖regularizedReply c x (F x)‖ + c.scale / c.curvature) * D :=
      mul_le_mul hdiff hxs (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma initial_gap_scaled (c : StageConfig (E := E)) (F : E → E) (s : E) {R : ℝ}
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hcs : ‖c.center - s‖ ≤ 2 * R)
    (hsolution : c.curvature * ‖F s‖ ≤ c.scale)
    (hanchor : c.curvature * c.regularization * ‖c.center - c.anchor‖ ≤ c.scale) :
    c.curvature * ⟪F c.center - F s, c.center - s⟫ ≤
      2 * R * trueDenominator c F c.center := by
  have hFbound : ‖F c.center‖ ≤ ‖regularizedReply c c.center (F c.center)‖ +
      c.regularization * ‖c.center - c.anchor‖ := by
    have ht := norm_sub_le (regularizedReply c c.center (F c.center))
      (c.regularization • (c.center - c.anchor))
    simpa only [regularizedReply, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] using ht
  have hnorm := norm_sub_le (F c.center) (F s)
  have hnorm' := mul_le_mul_of_nonneg_left hnorm hb.le
  have hFbound' := mul_le_mul_of_nonneg_left hFbound hb.le
  have hD : c.curvature * ‖F c.center - F s‖ ≤ trueDenominator c F c.center := by
    rw [trueDenominator_eq c F _ hb.ne']
    nlinarith
  have hinner := mul_le_mul_of_nonneg_left (real_inner_le_norm (F c.center - F s) (c.center - s)) hb.le
  have hprod := mul_le_mul_of_nonneg_right hD (norm_nonneg (c.center - s))
  have hdist := mul_le_mul_of_nonneg_left hcs (trueDenominator_pos c F c.center hb hS).le
  nlinarith

lemma initial_gap_local (c : StageConfig (E := E)) {F : E → E} {L0 R G ε : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature) (p s : E)
    (hS : 0 < c.scale) (hR : 0 < R) (hε : 0 ≤ ε) (hdR : c.radius ≤ R)
    (hcp : ‖c.center - p‖ ≤ c.radius) (hps : ‖p - s‖ ≤ R) (hG : ‖F s‖ ≤ G)
    (hgap : ⟪F p - F s, p - s⟫ ≤ ε * R)
    (hsmall : c.curvature * c.radius ≤ 1 / 2)
    (hrootSlope : 2 * (L0 + c.curvature * ‖F p‖) ≤ c.scale)
    (hsolutionSlope : 4 * (L0 + c.curvature * G) ≤ c.scale) :
    ⟪F c.center - F s, c.center - s⟫ ≤ ε * R + 3 * c.scale * R * c.radius +
      ε * (1 + 2 * c.curvature * R) * c.radius := by
  have hb := hF.L1_nonneg
  have hd : 0 ≤ c.radius := (norm_nonneg _).trans hcp
  have hshort : c.curvature * ‖p - c.center‖ ≤ 1 / 2 := by
    rw [norm_sub_rev]
    have hh := mul_le_mul_of_nonneg_left hcp hb
    linarith
  have hl := hF.local p c.center (by linarith)
  have hlocal : ‖F c.center - F p‖ ≤ c.scale * ‖c.center - p‖ := by
    rw [norm_sub_rev c.center p, norm_sub_rev (F c.center) (F p)]
    have hh := mul_nonneg (norm_nonneg (F p - F c.center)) (by linarith : 0 ≤ 1 / 2 - c.curvature * ‖p - c.center‖)
    have hslope := mul_le_mul_of_nonneg_right hrootSlope (norm_nonneg (p - c.center))
    nlinarith
  have href := root_operator_difference hF p s hR hG hgap hps
  have hG0 := (norm_nonneg _).trans hG
  have hN : 0 ≤ ε * (1 + 2 * c.curvature * R) + 4 * (L0 + c.curvature * G) * R := by
    have h0 := hF.L0_pos
    positivity
  have hnear := gap_near_reference F c.center p s hS.le hN hcp hps hlocal href
  have hterm := mul_le_mul_of_nonneg_right hsolutionSlope (mul_nonneg hR.le hd)
  have hdist := mul_le_mul_of_nonneg_left hdR (mul_nonneg hS.le hd)
  nlinarith

lemma initial_gap_normalized (c : StageConfig (E := E)) {F : E → E} {L0 R G ε J τ : ℝ}
    (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature) (p s : E)
    (hb : 0 < c.curvature) (hd : 0 < c.radius) (hR : 0 < R) (hJ : 1 ≤ J)
    (hr : 0 < c.regularization) (hrS : c.regularization ≤ c.scale)
    (hdR : c.radius ≤ R) (hcp : ‖c.center - p‖ ≤ c.radius) (hps : ‖p - s‖ ≤ R)
    (hG : ‖F s‖ ≤ G) (hgap : ⟪F p - F s, p - s⟫ ≤ ε * R)
    (hrootSlope : 2 * (L0 + c.curvature * ‖F p‖) ≤ c.scale)
    (hsolutionSlope : 4 * (L0 + c.curvature * G) ≤ c.scale)
    (hsolution : c.curvature * ‖F s‖ ≤ c.scale)
    (hanchor : c.curvature * c.regularization * ‖c.center - c.anchor‖ ≤ c.scale)
    (hε : ε = 2 ^ 20 * J * c.regularization * c.radius)
    (hτ : τ = c.radius / (2 ^ 100 * J * R * (1 + c.curvature * R))) :
    τ * c.scale * ⟪F c.center - F s, c.center - s⟫ ≤
      (trueDenominator c F c.center) ^ 2 * c.radius ^ 2 := by
  have hS := hr.trans_le hrS
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hSD : c.scale ≤ trueDenominator c F c.center := by
    rw [trueDenominator_eq c F _ hb.ne']
    nlinarith [mul_nonneg hb.le (norm_nonneg (regularizedReply c c.center (F c.center)))]
  by_cases hsmall : c.curvature * c.radius ≤ 1 / 256
  · have hg := initial_gap_local c hF p s hS hR hε0 hdR hcp hps hG hgap
      (by linarith) hrootSlope hsolutionSlope
    have hextra := mul_nonneg (mul_nonneg hε0 hd.le) (mul_nonneg hb.le hR.le)
    have hg' : ⟪F c.center - F s, c.center - s⟫ ≤ ε * R + 3 * c.scale * R * c.radius +
        ε * (1 + 8 * (c.curvature * R)) * c.radius := by nlinarith
    have hh := GapNoiseTuning.small_initial_gap_bound hd hR hdR hJ hr hrS
      (mul_nonneg hb.le hR.le) hε hτ hg'
    have hm := mul_le_mul_of_nonneg_left hh hS.le
    have hs := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS.le hSD 2) (sq_nonneg c.radius)
    nlinarith
  · have hcs : ‖c.center - s‖ ≤ 2 * R := by
      have ht := norm_sub_le_norm_sub_add_norm_sub c.center p s
      linarith
    have hg := initial_gap_scaled c F s hb hS hr.le hcs hsolution hanchor
    have hshift := (GapNoiseTuning.shift_geometry hd hR hdR hJ hb.le hτ).2.1
    exact GapNoiseTuning.large_initial_gap_bound hb hd hS hSD hτ0 hg hshift (by linarith)

lemma initial_energy_small {Ω : Type} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E} (c : StageConfig (E := E))
    {F : E → E} (hF : Continuous F) {g : E → Ω → E} (p s : E) {σ v τ : ℝ}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s σ v)
    (batch pilotBatch groups : ℕ) (hbatch : 0 < batch) (hc : c.center ∈ X)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hd : 0 < c.radius)
    (hrS : c.regularization ≤ c.scale) (hv : 0 ≤ v)
    (hgap : 0 ≤ ⟪F c.center - F s, c.center - s⟫)
    (hcp : ‖c.center - p‖ ≤ c.radius) (hτ : 0 ≤ τ)
    (hshift : τ * ‖p - s‖ ≤ c.radius / 24)
    (hnoise : 2 ^ 120 * (1 + c.curvature * c.radius) * σ ^ 2 ≤
      (batch : ℝ) * c.regularization * c.scale * c.radius ^ 2)
    (hbatchGap : 2 ^ 120 * (1 + c.curvature * c.radius) * v ≤ (batch : ℝ) * c.scale * τ)
    (hnormalized : τ * c.scale * ⟪F c.center - F s, c.center - s⟫ ≤
      (trueDenominator c F c.center) ^ 2 * c.radius ^ 2) :
    (∫ ξ : StepSamples Ω batch pilotBatch groups,
      GapNoiseStageEnergy.energy c F (p + τ • (s - p)) (idealInitial c F g batch pilotBatch groups ξ)
      ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => μ))).prod
        (Measure.pi (fun _ : Fin batch => μ))) ≤ 3 * c.radius ^ 2 / 2 := by
  have hSD : c.scale ≤ trueDenominator c F c.center := by
    rw [trueDenominator_eq c F _ hb.ne']
    nlinarith [mul_nonneg hb.le (norm_nonneg (regularizedReply c c.center (F c.center)))]
  have hreserve := GapNoiseTuning.initial_batch_reserve hS hSD hrS (Nat.cast_pos.mpr hbatch)
    (show 1 ≤ 1 + c.curvature * c.radius by nlinarith [mul_pos hb hd]) hv hgap hnoise hbatchGap hnormalized
  have hinitial := ideal_initial_energy_bound μ c hF ho.measurable batch pilotBatch groups hbatch
    (p + τ • (s - p)) hb hS hd.le (ho.integrable _ hc) (ho.unbiased _ hc)
    (ho.variance_integrable _ hc) (ho.variance _ hc)
  have hdist : ‖c.center - (p + τ • (s - p))‖ ≤ 25 * c.radius / 24 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub c.center p (p + τ • (s - p))
    have he : p - (p + τ • (s - p)) = -(τ • (s - p)) := by module
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ, norm_sub_rev s p] at ht
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  nlinarith [sq_nonneg c.radius]

lemma shifted_predictor_drift {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    (state : StageState E) (p s : E) {τ h B D Qmax : ℝ}
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization)
    (hst : StableState X c F state)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p (-regularizedReply c p (F p)))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hh : 0 < h) (hcap : c.curvature * h ≤ 1 / 2)
    (hshift : τ * ‖p - s‖ ≤ h / 2)
    (hxp : ‖predictor proj state - p‖ ≤ D)
    (hxz : ‖predictor proj state - (p + τ • (s - p))‖ ^ 2 ≤ Qmax)
    (hB : ‖F p‖ + c.regularization * (‖p - c.anchor‖ + D) +
      2 * (L0 + c.curvature * ‖F p‖) * (D + h) ≤ B)
    (hoffset : 2 * c.curvature * B ≤ c.scale)
    (hscale : c.regularization * c.curvature * Qmax ≤ 4 * c.scale * h)
    (hlocalScale : L0 + c.regularization + c.curvature * c.regularization *
      ‖state.previousQuery - c.anchor‖ ≤ c.scale) :
    let z := p + τ • (s - p)
    let floor := c.regularization * (τ ^ 2 * ‖p - c.anchor + (p - s)‖ ^ 2 +
      2 * τ * (‖p - c.anchor‖ * ‖p - s‖))
    c.regularization / (2 ^ 25 * c.scale) * ‖predictor proj state - z‖ ^ 2 ≤
      nextStep state * (⟪regularizedReply c (predictor proj state) (F (predictor proj state)),
        predictor proj state - z⟫ + floor) := by
  dsimp only
  let x := predictor proj state
  let z := p + τ • (s - p)
  let floor := c.regularization * (τ ^ 2 * ‖p - c.anchor + (p - s)‖ ^ 2 +
    2 * τ * (‖p - c.anchor‖ * ‖p - s‖))
  have hx : x ∈ X := hproj.mem _
  have hη := GapNoisePastState.nextStep_pos state hst.bounds.2.2.2.1 (hS.trans_le hst.bounds.2.2.1)
  have hstrong := OracleTemplate.ConstrainedMonotone.regularized_strong_vi hF.mono hroot hx
  have hsolution' : 0 ≤ ⟪F s, x - s⟫ := by
    have hn := hsolution x hx
    rw [inner_neg_left] at hn
    linarith
  have hcentered := centered_drift F x p c.anchor s hr hτ hτhalf hstrong hsolution'
  have hgap := mul_nonneg hτ (hF.mono x s)
  have hJ : c.regularization / 4 * ‖x - z‖ ^ 2 ≤
      ⟪regularizedReply c x (F x), x - z⟫ + floor := by
    dsimp [z, floor, regularizedReply]
    nlinarith
  have hfloor : 0 ≤ floor := by dsimp [floor]; positivity
  have hco := OracleTemplate.ConstrainedMonotone.regularized_coercivity hF c.anchor hx hroot hr hh hcap hxp
  have hB' := mul_le_mul_of_nonneg_left hB hh.le
  have hbase : h * ‖regularizedReply c x (F x)‖ ≤ h * B +
      ⟪regularizedReply c x (F x), x - p⟫ := by
    change h * ‖F x + c.regularization • (x - c.anchor)‖ ≤ _
    dsimp only [regularizedReply]
    linarith
  have hshifted := shifted_coercivity (fun y => regularizedReply c y (F y)) x p s hτ hshift hbase
  have hcoercive : h / 2 * ‖regularizedReply c x (F x)‖ - h * B ≤
      ⟪regularizedReply c x (F x), x - z⟫ + floor := by
    dsimp only [z]
    linarith
  have hprogress := stable_predictor_progress hproj c hF state hb hS hr hst hlocalScale
  exact uniform_norm_scaled_drift hη.le hS hb hh hr (sq_nonneg _) hxz hprogress
    hoffset hscale hJ hcoercive

lemma ideal_step_drift {Ω : Type} [MeasurableSpace Ω] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (c : StageConfig (E := E))
    {F : E → E} {L0 : ℝ} (hF : OracleTemplate.GeneralizedMonotone.Hyp F L0 c.curvature)
    {g : E → Ω → E} (state : StageState E) (p s : E) {σ v τ h B D Dsafe : ℝ}
    (ho : LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.IsGapStochasticOperator μ X F g s σ v)
    (batch pilotBatch groups : ℕ) (hbatch : 0 < batch)
    (hb : 0 < c.curvature) (hS : 0 < c.scale) (hr : 0 ≤ c.regularization) (hv : 0 ≤ v)
    (hst : StableState X c F state)
    (hroot : OracleTemplate.ConstrainedMonotone.Normal X p (-regularizedReply c p (F p)))
    (hsolution : OracleTemplate.ConstrainedMonotone.Normal X s (-F s))
    (hz : p + τ • (s - p) ∈ X) (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2)
    (hh : 0 < h) (hcap : c.curvature * h ≤ 1 / 2) (hshift : τ * ‖p - s‖ ≤ h / 2)
    (hDsafe : 0 ≤ Dsafe)
    (hgeometry : permitted c state (predictor proj state) →
      ‖predictor proj state - p‖ ≤ D ∧ ‖predictor proj state - (p + τ • (s - p))‖ ≤ Dsafe)
    (hB : ‖F p‖ + c.regularization * (‖p - c.anchor‖ + D) +
      2 * (L0 + c.curvature * ‖F p‖) * (D + h) ≤ B)
    (hoffset : 2 * c.curvature * B ≤ c.scale)
    (hscale : c.regularization * c.curvature * Dsafe ^ 2 ≤ 4 * c.scale * h)
    (hlocalScale : L0 + c.regularization + c.curvature * c.regularization *
      ‖state.previousQuery - c.anchor‖ ≤ c.scale)
    (hsize : (30 + 4096 * c.curvature * Dsafe) * (1 / (16384 * c.scale)) * v ≤ (batch : ℝ) * τ) :
    let z := p + τ • (s - p)
    let floor := c.regularization * (τ ^ 2 * ‖p - c.anchor + (p - s)‖ ^ 2 +
      2 * τ * (‖p - c.anchor‖ * ‖p - s‖))
    (∫ ξ : StepSamples Ω batch pilotBatch groups,
      GapNoiseStageEnergy.energy c F z (idealStep proj c F g batch pilotBatch groups state ξ)
      ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => μ))).prod
        (Measure.pi (fun _ : Fin batch => μ))) +
      (c.regularization / (2 ^ 25 * c.scale)) * activeLoss proj c z state ≤
    GapNoiseStageEnergy.energy c F z state + 2 * (1 / (16384 * c.scale)) * floor +
      (30 + 4096 * c.curvature * Dsafe) * (1 / (16384 * c.scale)) ^ 2 * σ ^ 2 / batch := by
  classical
  dsimp only
  let z := p + τ • (s - p)
  let floor := c.regularization * (τ ^ 2 * ‖p - c.anchor + (p - s)‖ ^ 2 +
    2 * τ * (‖p - c.anchor‖ * ‖p - s‖))
  have hfloor : 0 ≤ floor := by dsimp [floor]; positivity
  have hK : 0 ≤ 30 + 4096 * c.curvature * Dsafe := by positivity
  by_cases hguard : permitted c state (predictor proj state)
  · let x := predictor proj state
    let η := nextStep state
    let ηmax := 1 / (16384 * c.scale)
    let J := ⟪regularizedReply c x (F x), x - z⟫
    let gap := ⟪F x - F s, x - s⟫
    have hx : x ∈ X := hproj.mem _
    have hη := GapNoisePastState.nextStep_pos state hst.bounds.2.2.2.1 (hS.trans_le hst.bounds.2.2.1)
    have hηmax : η ≤ ηmax := (min_le_right _ _).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [hst.bounds.2.2.1]))
    have hgap : 0 ≤ gap := hF.mono x s
    have hbound := idealStep_energy_integral μ hproj c hF ho.measurable batch pilotBatch groups hbatch state z
      hb hS hr hst hz hlocalScale hguard (ho.integrable x hx) (ho.unbiased x hx)
      (ho.variance_integrable x hx) (ho.variance x hx) (hgeometry hguard).2
    have habsorb := GapNoiseMoments.batch_gap_absorption (σ := σ) hK hη.le hηmax hv hgap
      (Nat.cast_pos.mpr hbatch) hsize
    have hstrong := OracleTemplate.ConstrainedMonotone.regularized_strong_vi hF.mono hroot hx
    have hsinner : 0 ≤ ⟪F s, x - s⟫ := by
      have hn := hsolution x hx
      rw [inner_neg_left] at hn
      linarith
    have hcentered := centered_drift F x p c.anchor s hr hτ hτhalf hstrong hsinner
    have hstrong' : c.regularization / 4 * ‖x - z‖ ^ 2 + τ * gap ≤ J + floor := by
      dsimp [z, J, gap, floor, regularizedReply]
      nlinarith
    have hprogress := shifted_predictor_drift hproj c hF state p s hb hS hr hst hroot hsolution
      hτ hτhalf hh hcap hshift (hgeometry hguard).1
      (pow_le_pow_left₀ (norm_nonneg _) (hgeometry hguard).2 2) hB hoffset hscale hlocalScale
    have hstep : (∫ ξ : StepSamples Ω batch pilotBatch groups,
        GapNoiseStageEnergy.energy c F z (idealStep proj c F g batch pilotBatch groups state ξ)
        ∂(Measure.pi (fun _ : Fin (groups + 1) => Measure.pi (fun _ : Fin pilotBatch => μ))).prod
          (Measure.pi (fun _ : Fin batch => μ))) ≤
        GapNoiseStageEnergy.energy c F z state - 2 * η * J + η * τ * gap +
          (30 + 4096 * c.curvature * Dsafe) * ηmax ^ 2 * σ ^ 2 / batch := by
      dsimp only [x, η, ηmax, J, gap, z] at *
      nlinarith [sq_nonneg ‖state.base - predictor proj state‖, sq_nonneg ‖state.base - state.previousQuery‖]
    have hh := GapNoiseMoments.drift_after_gap_absorption hη.le hηmax hfloor
      (by positivity : 0 ≤ c.regularization / 4 * ‖x - z‖ ^ 2) hstep hstrong' hprogress
    simpa only [activeLoss, hguard, ite_true, x, ηmax, z, floor] using hh
  · simp only [idealStep, hguard, ite_false, GapNoiseStageEnergy.energy_inactive, activeLoss,
      integral_const, probReal_univ, one_smul, mul_zero, add_zero]
    change GapNoiseStageEnergy.energy c F z state ≤ GapNoiseStageEnergy.energy c F z state +
      2 * (1 / (16384 * c.scale)) * floor +
      (30 + 4096 * c.curvature * Dsafe) * (1 / (16384 * c.scale)) ^ 2 * σ ^ 2 / batch
    have hn1 : 0 ≤ 2 * (1 / (16384 * c.scale)) * floor := by positivity
    have hn2 : 0 ≤ (30 + 4096 * c.curvature * Dsafe) * (1 / (16384 * c.scale)) ^ 2 * σ ^ 2 / batch := by positivity
    linarith

end LongTails.Proofs.GapNoiseStageDrift
