import LongTails.Proofs.GapNoiseTwoCenter
import LongTails.Proofs.GapNoiseMoments
import LongTails.Proofs.GapNoisePastState

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapNoiseStageEnergy

open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseTwoCenter

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def energy (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E) : ℝ :=
  ‖state.base - z‖ ^ 2 + ‖state.base - state.previousQuery‖ ^ 2 / 4 +
    24 * state.previousStep ^ 2 *
      ‖state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)‖ ^ 2

lemma energy_nonneg (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E) :
    0 ≤ energy c F z state := by unfold energy; positivity

lemma energy_le_of_bounds (c : StageConfig (E := E)) (F : E → E) (z center : E)
    (state : StageState E) {B D Z U T M : ℝ}
    (hw : ‖state.base - center‖ ≤ B) (hx : ‖state.previousQuery - center‖ ≤ D)
    (hz : ‖z - center‖ ≤ Z) (hη : |state.previousStep| ≤ U)
    (hg : |state.previousStep| * ‖state.previousReply‖ ≤ T)
    (hH : ‖regularizedReply c state.previousQuery (F state.previousQuery)‖ ≤ M) :
    energy c F z state ≤ (B + Z) ^ 2 + (B + D) ^ 2 / 4 + 24 * (T + U * M) ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hH
  have hwz : ‖state.base - z‖ ≤ B + Z := by
    have ht := norm_sub_le_norm_sub_add_norm_sub state.base center z
    rw [norm_sub_rev center z] at ht
    linarith
  have hwx : ‖state.base - state.previousQuery‖ ≤ B + D := by
    have ht := norm_sub_le_norm_sub_add_norm_sub state.base center state.previousQuery
    rw [norm_sub_rev center state.previousQuery] at ht
    linarith
  have herr : |state.previousStep| *
      ‖state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)‖ ≤ T + U * M := by
    have ht := mul_le_mul_of_nonneg_left
      (norm_sub_le state.previousReply (regularizedReply c state.previousQuery (F state.previousQuery)))
      (abs_nonneg state.previousStep)
    have hm := mul_le_mul hη hH (norm_nonneg _) ((abs_nonneg _).trans hη)
    nlinarith
  have he2 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) herr 2
  rw [mul_pow, sq_abs] at he2
  have hw2 := pow_le_pow_left₀ (norm_nonneg _) hwz 2
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hwx 2
  unfold energy
  linarith

lemma low_energy_bounds (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E)
    {d : ℝ} (hd : 0 < d) (hη : 0 ≤ state.previousStep)
    (he : energy c F z state ≤ 1024 * d ^ 2) :
    ‖state.base - z‖ ≤ 32 * d ∧ ‖state.base - state.previousQuery‖ ≤ 64 * d ∧
      state.previousStep * ‖state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)‖ ≤ 7 * d := by
  have h1 : 0 ≤ ‖state.base - z‖ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ‖state.base - state.previousQuery‖ ^ 2 := sq_nonneg _
  have h3 : 0 ≤ state.previousStep ^ 2 *
      ‖state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)‖ ^ 2 := by positivity
  unfold energy at he
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [norm_nonneg (state.base - z)]
  · nlinarith [norm_nonneg (state.base - state.previousQuery)]
  · have hn := mul_nonneg hη (norm_nonneg
      (state.previousReply - regularizedReply c state.previousQuery (F state.previousQuery)))
    nlinarith

lemma active_step_energy {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj)
    (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E) (pilot raw : E)
    (hz : z ∈ X) (hη : 0 ≤ nextStep state)
    (hguard : permitted c state (predictor proj state))
    (hlocal : nextStep state *
      ‖regularizedReply c state.previousQuery (F state.previousQuery) -
        regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (‖state.base - predictor proj state‖ + ‖state.base - state.previousQuery‖) / 16) :
    let x := predictor proj state
    let η := nextStep state
    let H := regularizedReply c x (F x)
    let e := clippedReply c η (regularizedReply c x raw) - H
    energy c F z (advance proj c state x pilot raw) ≤ energy c F z state -
      7 / 8 * ‖state.base - x‖ ^ 2 - ‖state.base - state.previousQuery‖ ^ 2 / 8 -
      2 * η * ⟪H, x - z⟫ - 2 * η * ⟪e, x - z⟫ + 30 * η ^ 2 * ‖e‖ ^ 2 := by
  let x := predictor proj state
  let η := nextStep state
  let H := regularizedReply c x (F x)
  let oldH := regularizedReply c state.previousQuery (F state.previousQuery)
  let e := clippedReply c η (regularizedReply c x raw) - H
  let oldError := state.previousReply - oldH
  have hgrowth : η ≤ 2 * state.previousStep := min_le_left _ _
  have hsum : oldH + oldError = state.previousReply := by dsimp [oldError]; abel
  have he : H + e = clippedReply c η (regularizedReply c x raw) := by dsimp [e]; abel
  have hdiff := local_oracle_difference oldH H oldError e hη hlocal
  rw [hsum] at hdiff
  have hp := past_augmented_energy hproj state.base z state.previousReply state.previousQuery
    H e oldError hz hη hgrowth hdiff
  dsimp only at hp
  rw [he] at hp
  dsimp only
  rw [advance, ite_eq_left hguard]
  simpa only [energy, updatedState, x, η, H, oldError, oldH, e, predictor] using hp

lemma energy_pilot_replacement (c : StageConfig (E := E)) (F : E → E) (z : E)
    (state : StageState E) (denominator : ℝ) :
    energy c F z { state with pilotDenominator := denominator } = energy c F z state := rfl

lemma energy_advance_pilot (proj : E → E) (c : StageConfig (E := E)) (F : E → E)
    (z : E) (state : StageState E) (x pilot otherPilot raw : E) :
    energy c F z (advance proj c state x pilot raw) =
      energy c F z (advance proj c state x otherPilot raw) := by
  classical
  unfold advance
  split <;> rfl

lemma energy_inactive (c : StageConfig (E := E)) (F : E → E) (z : E) (state : StageState E) :
    energy c F z { state with active := false } = energy c F z state := rfl

@[fun_prop] lemma measurable_energy [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (c : StageConfig (E := E)) {F : E → E} (hF : Measurable F) (z : E) :
    Measurable (energy c F z) := by
  unfold energy regularizedReply
  fun_prop

lemma projected_bounded_energy {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj) (w x z q H : E)
    (hx : x ∈ X) (hz : z ∈ X) {η T : ℝ} (hη : 0 ≤ η) (hq : ‖q‖ ≤ T) :
    let y := proj (w - η • q)
    ‖y - z‖ ^ 2 + ‖y - x‖ ^ 2 / 4 + 24 * η ^ 2 * ‖q - H‖ ^ 2 ≤
      (‖w - z‖ + η * T) ^ 2 + (‖w - x‖ + η * T) ^ 2 / 4 +
        24 * η ^ 2 * (T + ‖H‖) ^ 2 := by
  have bound (a : E) (ha : a ∈ X) : ‖proj (w - η • q) - a‖ ≤ ‖w - a‖ + η * T := by
    have hp := hproj.dist_le (w - η • q) ha
    have he : w - η • q - a = (w - a) - η • q := by abel
    rw [he] at hp
    have hn := norm_sub_le (w - a) (η • q)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hn
    have hq' := mul_le_mul_of_nonneg_left hq hη
    linarith
  have hz2 := pow_le_pow_left₀ (norm_nonneg _) (bound z hz) 2
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) (bound x hx) 2
  have he : ‖q - H‖ ≤ T + ‖H‖ := by linarith [norm_sub_le q H]
  have he2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he 2)
    (by positivity : 0 ≤ 24 * η ^ 2)
  dsimp only
  linarith

lemma active_energy_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj)
    (c : StageConfig (E := E)) {F : E → E} (hF : Measurable F) (z : E) (state : StageState E)
    (pilot : E) {raw : Ω → E} (hg : Measurable raw) (hz : z ∈ X)
    (hb : 0 < c.curvature) (hη : 0 < nextStep state)
    (hguard : permitted c state (predictor proj state)) :
    Integrable (fun ω => energy c F z (advance proj c state (predictor proj state) pilot (raw ω))) P := by
  let x := predictor proj state
  let η := nextStep state
  let T := 1 / (1024 * c.curvature * η)
  let H := regularizedReply c x (F x)
  have hT : 0 ≤ T := by dsimp [T, η]; positivity
  have hx : x ∈ X := hproj.mem _
  have hm : Measurable (fun ω => energy c F z (advance proj c state (predictor proj state) pilot (raw ω))) :=
    (measurable_energy c hF z).comp
    (GapNoisePastState.measurable_advance proj hproj.lipschitz.continuous.measurable c
      measurable_const measurable_const measurable_const hg)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((‖state.base - z‖ + η * T) ^ 2 + (‖state.base - x‖ + η * T) ^ 2 / 4 +
      24 * η ^ 2 * (T + ‖H‖) ^ 2)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _ _ _ _)]
  have hq := OracleTemplate.norm_clip_le hT (regularizedReply c x (raw ω))
  have hh := projected_bounded_energy hproj state.base x z
    (clippedReply c η (regularizedReply c x (raw ω))) H hx hz hη.le hq
  rw [advance, ite_eq_left hguard]
  simpa only [energy, updatedState, x, η, T, H, predictor] using hh

lemma initial_energy_integral {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] (c : StageConfig (E := E)) (F : E → E) (z : E)
    {denominator : ℝ} (hden : 0 < denominator) (hb : 0 < c.curvature)
    {raw : Ω → E} (hg : Measurable raw) (hi : Integrable raw P)
    (hmean : (∫ ω, raw ω ∂P) = F c.center)
    (hvi : Integrable (fun ω => ‖raw ω - F c.center‖ ^ 2) P)
    {V : ℝ} (hv : (∫ ω, ‖raw ω - F c.center‖ ^ 2 ∂P) ≤ V)
    (hsignal : ‖regularizedReply c c.center (F c.center)‖ ≤
      (1 / (1024 * c.curvature * (1 / (16384 * denominator)))) / 2) :
    (∫ ω, energy c F z (initialWithDenominator c denominator (raw ω)) ∂P) ≤
      ‖c.center - z‖ ^ 2 + 24 * (1 / (16384 * denominator)) ^ 2 * V := by
  let η := 1 / (16384 * denominator)
  let T := 1 / (1024 * c.curvature * η)
  let H := regularizedReply c c.center (F c.center)
  let G : Ω → E := fun ω => regularizedReply c c.center (raw ω)
  have hT : 0 < T := by dsimp [T, η]; positivity
  have hV : 0 ≤ V := (integral_nonneg (fun ω => sq_nonneg ‖raw ω - F c.center‖)).trans hv
  have hG : Measurable G := hg.add_const _
  have hGi : Integrable G P := hi.add (integrable_const _)
  have hGmean : (∫ ω, G ω ∂P) = H := by
    dsimp [G, H, regularizedReply]
    rw [integral_add hi (integrable_const _), hmean]
    simp only [integral_const, probReal_univ, one_smul]
  have hdiff (ω : Ω) : G ω - H = raw ω - F c.center := by
    dsimp [G, H, regularizedReply]
    abel
  have hGvi : Integrable (fun ω => ‖G ω - H‖ ^ 2) P := by simpa only [hdiff] using hvi
  have hGv : (∫ ω, ‖G ω - H‖ ^ 2 ∂P) ≤ V := by simpa only [hdiff] using hv
  have hbound := (GapNoiseMoments.clipped_variance_bias hG hGi hGmean hT hV hsignal hGvi hGv).2
  have he2 : Integrable (fun ω => ‖OracleTemplate.clip T (G ω) - H‖ ^ 2) P := by
    have hri : Integrable (fun ω => ‖G ω - H‖ ^ (2 : ℝ)) P := by
      simpa only [Real.rpow_two] using hGvi
    simpa only [Real.rpow_two] using OracleTemplate.clipped_moment_integrable hG hT.le
      (by norm_num : (0 : ℝ) ≤ 2) (by dsimp [H, T, η]; linarith : ‖H‖ ≤ T) hri
  have heq (ω : Ω) : energy c F z (initialWithDenominator c denominator (raw ω)) =
      ‖c.center - z‖ ^ 2 + 24 * η ^ 2 * ‖OracleTemplate.clip T (G ω) - H‖ ^ 2 := by
    simp only [energy, initialWithDenominator, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, add_zero, clippedReply, η, T, G, H]
  simp_rw [heq]
  rw [integral_add (integrable_const _) (he2.const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 24 * η ^ 2)
  dsimp [η] at hm
  linarith

lemma active_step_integral {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Set E} {proj : E → E}
    (hproj : OracleTemplate.ConstrainedMonotone.Proj X proj)
    (c : StageConfig (E := E)) {F : E → E} (hF : Measurable F) (z : E) (state : StageState E)
    (pilot : E) {raw : Ω → E} (hg : Measurable raw) (hi : Integrable raw P)
    (hmean : (∫ ω, raw ω ∂P) = F (predictor proj state))
    (hvi : Integrable (fun ω => ‖raw ω - F (predictor proj state)‖ ^ 2) P)
    {V D : ℝ} (hv : (∫ ω, ‖raw ω - F (predictor proj state)‖ ^ 2 ∂P) ≤ V)
    (hz : z ∈ X) (hb : 0 < c.curvature) (hη : 0 < nextStep state)
    (hguard : permitted c state (predictor proj state))
    (hlocal : nextStep state *
      ‖regularizedReply c state.previousQuery (F state.previousQuery) -
        regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (‖state.base - predictor proj state‖ + ‖state.base - state.previousQuery‖) / 16)
    (hsignal : ‖regularizedReply c (predictor proj state) (F (predictor proj state))‖ ≤
      (1 / (1024 * c.curvature * nextStep state)) / 2)
    (hD : ‖predictor proj state - z‖ ≤ D) :
    (∫ ω, energy c F z (advance proj c state (predictor proj state) pilot (raw ω)) ∂P) ≤
      energy c F z state - 7 / 8 * ‖state.base - predictor proj state‖ ^ 2 -
        ‖state.base - state.previousQuery‖ ^ 2 / 8 -
        2 * nextStep state * ⟪regularizedReply c (predictor proj state) (F (predictor proj state)),
          predictor proj state - z⟫ + (30 + 4096 * c.curvature * D) * nextStep state ^ 2 * V := by
  let x := predictor proj state
  let η := nextStep state
  let H := regularizedReply c x (F x)
  let G : Ω → E := fun ω => regularizedReply c x (raw ω)
  let T := 1 / (1024 * c.curvature * η)
  let C := energy c F z state - 7 / 8 * ‖state.base - x‖ ^ 2 -
    ‖state.base - state.previousQuery‖ ^ 2 / 8 - 2 * η * ⟪H, x - z⟫
  have hT : 0 < T := by dsimp [T, η]; positivity
  have hV : 0 ≤ V := (integral_nonneg (fun ω => sq_nonneg ‖raw ω - F (predictor proj state)‖)).trans hv
  have hG : Measurable G := hg.add_const _
  have hGi : Integrable G P := hi.add (integrable_const _)
  have hGmean : (∫ ω, G ω ∂P) = H := by
    dsimp [G, H, regularizedReply]
    rw [integral_add hi (integrable_const _), hmean]
    simp only [integral_const, probReal_univ, one_smul, x]
  have hdiff (ω : Ω) : G ω - H = raw ω - F x := by
    dsimp [G, H, regularizedReply]
    abel
  have hGvi : Integrable (fun ω => ‖G ω - H‖ ^ 2) P := by simpa only [hdiff] using hvi
  have hGv : (∫ ω, ‖G ω - H‖ ^ 2 ∂P) ≤ V := by simpa only [hdiff] using hv
  have hei := active_energy_integrable (P := P) hproj c hF z state pilot hg hz hb hη hguard
  have hpoint (ω : Ω) : energy c F z (advance proj c state x pilot (raw ω)) ≤
      C - 2 * η * ⟪OracleTemplate.clip T (G ω) - H, x - z⟫ +
        30 * η ^ 2 * ‖OracleTemplate.clip T (G ω) - H‖ ^ 2 := by
    have hh := active_step_energy hproj c F z state pilot (raw ω) hz hη.le hguard hlocal
    simpa only [C, T, G, H, x, η, clippedReply] using hh
  have hh := GapNoiseMoments.integrate_clipped_energy hG hGi hGmean hT hV hsignal hη.le hD hGvi hGv hei hpoint
  change (∫ ω, energy c F z (advance proj c state x pilot (raw ω)) ∂P) ≤
    C + (30 + 4096 * c.curvature * D) * η ^ 2 * V
  calc
    _ ≤ C + 30 * η ^ 2 * V + 4 * η * D * V / T := hh
    _ = _ := by
      dsimp [T]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring

end LongTails.Proofs.GapNoiseStageEnergy
