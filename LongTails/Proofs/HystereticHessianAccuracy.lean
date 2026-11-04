import LongTails.Proofs.HystereticHessianParameters
import LongTails.Proofs.HystereticHessianSampling

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianAccuracy

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianParameters HystereticHessianMoments HystereticHessianBlocks
open HystereticHessianAnchorBlocks HystereticHessianCertificates HystereticHessianSampling
open HystereticHessianTransport HystereticHessianTracking HystereticHessianCompletion
open OracleTemplate.StochasticGeneralized
open LongTails.Algorithms.GuardedHessianTransport (uniformLaw)

lemma configured_proposal_growth (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    (g : Space p → Space p) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖) :
    (∀ x v, ‖g (x + coarseDisplacement p (tunedConfig p) v)‖ ≤ 2 * max ‖g x‖ (guardRadius p)) ∧
    (∀ s : State p (tunedConfig p), ‖g (s.point + fineDisplacement p (tunedConfig p) s)‖ ≤
      2 * max ‖g s.point‖ (guardRadius p)) := by
  have hc := tuned_coarse_conditions p hv hcurv
  have hf := tuned_fine_conditions p hv hcurv
  have he := targetAccuracy_pos p hv
  have heM := (noise_scales p hv).2.2.1.trans (guardRadius_bounds p hv).2.1
  rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨?_, ?_⟩
  · exact coarse_proposal_growth p (tunedConfig p) g hL0 hL1 hc.1 hg hH hc.2.1 hc.2.2
  · exact fine_proposal_growth p (tunedConfig p) g hL0 hL1 hf.1.le hg hH hf.2.1
      (by linarith [hf.2.2.1])

lemma configured_initial_gradient (p : Params) (hv : spec.valid p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ) :
    ‖g p.x0‖ ≤ guardRadius p := by
  have hM := guardRadius_bounds p hv
  rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, _, _⟩
  apply HystereticHessianDescent.sublevel_gradient_bound p f g hL0 hL1 hf hg hH hm hM.1.le
    _ _ p.x0 le_rfl
  · have hh := mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hL1)
    exact hh.trans hM.2.2.1
  · have hh := mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hL0)
    exact hh.trans hM.2.2.2

lemma expected_of_two_failures {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (A B : Set Ω) {e M δA δB : ℝ} (he : 0 < e) (hM : 0 < M)
    (hsecond : (∫ ω, X ω ^ 2 ∂P) ≤ M)
    (hgood : ∀ ω, ω ∉ A → ω ∉ B → X ω ≤ e)
    (hA : P.real A ≤ δA) (hB : P.real B ≤ δB) (hδ : δA + δB ≤ e ^ 2 / M) :
    Integrable X P ∧ (∫ ω, X ω ∂P) ≤ 2 * e := by
  have hsub : {ω | e < X ω} ⊆ A ∪ B := by
    intro ω hω
    by_contra hh
    have ha : ω ∉ A := fun h => hh (Or.inl h)
    have hb : ω ∉ B := fun h => hh (Or.inr h)
    exact (not_lt_of_ge (hgood ω ha hb)) hω
  have hfailure : P.real {ω | e < X ω} ≤ e ^ 2 / M :=
    (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ((add_le_add hA hB).trans hδ))
  have hh := AffineTransportConcentration.expected_from_failure_and_second hX hX0 hX2 he.le
    (by positivity : 0 < e / (2 * M)) hsecond hfailure
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  field_simp
  ring

noncomputable def gradientBadEvent (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {Ω : Type} [Nonempty Ω] (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖) : Set (ℕ → ℝ × Ω) :=
  let c := tunedConfig p
  let M := guardRadius p
  let growth := configured_proposal_growth p hv hcurv g hg hH
  let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
  let next := blockNext p c answer g M growth.1 growth.2
  let bad := fun n (t : BlockState p c g M) w =>
    gradientBlockBad p c answer g (targetAccuracy p / 256) n t.val w
  let start : BlockState p c g M := ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
  {ξ | ∃ k < blockCap c, blockBad cost next bad start ξ k = true}

lemma gradient_bad_probability (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hi : ∀ x, Integrable (answer (x, none)) P)
    (hm : ∀ x, (∫ ω, answer (x, none) ω ∂P) = g x)
    (hpi : ∀ x, Integrable (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ ω, ‖answer (x, none) ω - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) :
    let Q := (uniformLaw : Measure ℝ).prod P
    (Measure.infinitePi fun _ : ℕ => Q).real (gradientBadEvent p hv hcurv answer g hg hH) ≤
      (logicalBlocks p : ℝ) * (1 / 2 : ℝ) ^ groupCount p := by
  intro Q
  let c := tunedConfig p
  let M := guardRadius p
  let growth := configured_proposal_growth p hv hcurv g hg hH
  have hi' (x : Space p) : Integrable (fun z : ℝ × Ω => answer (x, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hi x)
  have hm' (x : Space p) : (∫ z : ℝ × Ω, answer (x, none) z.2 ∂Q) = g x := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hm x
  have hpi' (x : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hpi x)
  have hb' (x : Space p) : (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p := by
    have heq := integral_fun_snd (μ := (uniformLaw : Measure ℝ)) (ν := P)
      (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p)
    simp only [probReal_univ, one_smul] at heq
    exact heq.trans_le (hb x)
  have hp : 1 < p.p := hv.2.2.2.2.2.2.1
  have hp2 : p.p ≤ 2 := hv.2.2.2.2.2.2.2.1
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hh := adaptive_gradient_block_probability p c Q answer ha g hg.continuous.measurable
    hp.le hp2 hU (by positivity : 0 < targetAccuracy p / 256) hi' hm' hpi' hb'
    (fun x => by simpa only [c, tuned_pilotBatch, show (tunedConfig p).radius = localRadius p from rfl] using pilot_moment p hv ‖g x‖ (norm_nonneg _))
    (fun x hx => by simpa only [c, tuned_resetBatch] using refresh_moment p hv ‖g x‖ (norm_nonneg _) hx)
    M growth.1 growth.2 ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩ (blockCap c)
  simpa only [gradientBadEvent, c, M, growth, tuned_blockCap p hv, tuned_groups] using hh

def noiseBadEvent (p : Params) {Ω : Type} [MeasurableSpace Ω] (Q : Measure (ℝ × Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p) : Set (ℕ → ℝ × Ω) :=
  let c := tunedConfig p
  {ξ | ∃ j < c.macros + 1, (path p c answer (initial p c) ξ (j * macroCalls c),
    fun k => ξ (j * macroCalls c + k)) ∈
      HystereticHessianConcentration.macroBad p c Q answer g (targetAccuracy p / 256)}

lemma noise_bad_probability (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hi : ∀ y v, Integrable (answer (y, some v)) P)
    (hm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q) :
    let Q := (uniformLaw : Measure ℝ).prod P
    (Measure.infinitePi fun _ : ℕ => Q).real (noiseBadEvent p Q answer g) ≤
      (macroCount p : ℝ) * Real.exp (-confidence p) := by
  intro Q
  let c := tunedConfig p
  let a := targetAccuracy p / 256
  let b : ℝ := transportBatchCount p
  let τ := c.clipThreshold
  let K := p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p)
  let R := 512 * K * c.fineStep
  let C := 2 * τ / b
  let V := (2 * τ) ^ (2 - p.q) * R ^ p.q / b ^ 2
  let θ := 2 * confidence p / a ^ 2
  have he := targetAccuracy_pos p hv
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hU := localRadius_pos p hv
  have hf := tuned_fine_conditions p hv hcurv
  have ht := tuned_transport_bounds p hv hcurv
  have henergy := tuned_transport_energy p hv hcurv
  change 0 ≤ C ∧ 0 ≤ V ∧ 0 ≤ θ ∧ θ * (2 * a * C + C ^ 2) ≤ 1 ∧
    ((epochCount p : ℝ) * b) * ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2 ≤
      -confidence p at henergy
  have hmom (s : State p c) : Integrable (transportNoise p c Q answer g s) Q ∧
      Integrable (fun z => ‖transportNoise p c Q answer g s z‖ ^ 2) Q ∧
      (∫ z, transportNoise p c Q answer g s z ∂Q) = 0 ∧
      (∀ z, ‖transportNoise p c Q answer g s z‖ ≤ C) ∧
      (∫ z, ‖transportNoise p c Q answer g s z‖ ^ 2 ∂Q) ≤ V := by
    rcases hv with ⟨hL0, hL1, _, _, hσ, hα, _, _, hq, hq2, _, _⟩
    have hh := transportNoise_moments p c P answer ha g hL0 hL1 hq.le hq2 hσ hα hU hf.1.le
      ht.1 (le_refl K) hg hD hH hi hm hpi hb hf.2.1 hf.2.2.2.1 s
    simpa only [c, tuned_transportBatch] using hh
  have hh := HystereticHessianConcentration.trial_noise_tail p c Q answer ha g hg.continuous.measurable
    ha0 henergy.1 henergy.2.1 henergy.2.2.1 hmom henergy.2.2.2.1
  simp only [c, tuned_macros, tuned_epoch p hv, tuned_transportBatch, Nat.cast_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr henergy.2.2.2.2)
    (Nat.cast_nonneg (macroCount p)))

lemma good_events_accuracy (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (hi : ∀ y v, Integrable (answer (y, some v)) P)
    (hmean : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (ξ : ℕ → ℝ × Ω)
    (hgrad : ξ ∉ gradientBadEvent p hv hcurv answer g hg hH)
    (hnoise : ξ ∉ noiseBadEvent p ((uniformLaw : Measure ℝ).prod P) answer g) :
    ‖g (output p (tunedConfig p)
      (path p (tunedConfig p) answer (initial p (tunedConfig p)) ξ (trialCalls (tunedConfig p))))‖ ≤ targetAccuracy p := by
  let c := tunedConfig p
  let Q := (uniformLaw : Measure ℝ).prod P
  let a := targetAccuracy p / 256
  let K := p.L0 + p.L1 * (4 * localRadius p) + p.σh + p.αh * (4 * localRadius p)
  let d := ((512 * K * c.fineStep) ^ p.q / (c.clipThreshold / 2) ^ (p.q - 1)) / (transportBatchCount p : ℝ)
  have he := targetAccuracy_pos p hv
  have hU := localRadius_pos p hv
  have hM := guardRadius_bounds p hv
  have hFine := tuned_fine_conditions p hv hcurv
  have hCoarse := tuned_coarse_conditions p hv hcurv
  have hScale := localScale_bounds p hv hcurv
  have ht := tuned_transport_bounds p hv hcurv
  have growth := configured_proposal_growth p hv hcurv g hg hH
  have hδ : 0 ≤ f p.x0 - m := sub_nonneg.mpr (hm p.x0)
  have hbudget := tuned_macro_budget p hv hcurv hδ hgap
  have hv0 := hv
  rcases hv with ⟨hL0, hL1, _, _, hσ, hα, _, _, hq, hq2, _, _⟩
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by
    have hR := ht.2.1
    have hτ := ht.1
    dsimp [d]
    positivity
  have hbias (s : State p c) : ‖transportBias p c Q answer g s‖ ≤ d := by
    have hh := transportBias_bound p c P answer ha g hL0 hL1 hq.le hq2 hσ hα hU hFine.1.le
      ht.1 (le_refl K) hg hD hH hi hmean hpi hb hFine.2.1 hFine.2.2.2.1 s
    simpa only [c, tuned_transportBatch] using hh
  have hlinear : 16 * p.L1 * (f p.x0 - m) ≤ guardRadius p := by
    have hh := mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hL1)
    exact hh.trans hM.2.2.1
  have hconstant : 16 * p.L0 * (f p.x0 - m) ≤ (guardRadius p) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hL0)
    exact hh.trans hM.2.2.2
  have htrack : 3 * a + (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d ≤ c.accuracy / 64 := by
    have hbiasSum := ht.2.2.2.1
    simp only [c, tuned_epoch p hv0, tuned_transportBatch, Nat.cast_mul]
    change 3 * a + (epochCount p : ℝ) * (transportBatchCount p : ℝ) * d ≤ targetAccuracy p / 64
    change (epochCount p : ℝ) * (transportBatchCount p : ℝ) * d ≤ a at hbiasSum
    dsimp [a] at hbiasSum ⊢
    linarith
  apply good_trial_accuracy p c Q answer f g ξ hL0 hL1 hFine.1 he hCoarse.1 hU hf hg hH
    hFine.2.1 hFine.2.2.1 hm hM.1.le hM.2.1 le_rfl hlinear hconstant
    ha0 hd (by dsimp [a, c, tunedConfig]; linarith) htrack hbias growth.1 growth.2
    hScale.1 le_rfl hFine.2.2.2.2.1 ?_ ?_ ?_
  · simpa only [c, tuned_epoch p hv0, tuned_macros,
      show (tunedConfig p).accuracy = targetAccuracy p from rfl,
      show (tunedConfig p).radius = localRadius p from rfl] using hbudget
  · intro k hk
    apply Bool.eq_false_iff.mpr
    intro hh
    exact hgrad ⟨k, hk, hh⟩
  · intro j hj hh
    exact hnoise ⟨j, hj, hh⟩

lemma configured_second_moment (p : Params) (hv : spec.valid p) (hcurv : 0 < p.L0 + p.L1)
    {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (hi : ∀ x, Integrable (answer (x, none)) P)
    (hmean : ∀ x, (∫ ω, answer (x, none) ω ∂P) = g x)
    (hpi : ∀ x, Integrable (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ ω, ‖answer (x, none) ω - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) :
    let c := tunedConfig p
    let Q := (uniformLaw : Measure ℝ).prod P
    let X := fun ξ => ‖g (output p c (path p c answer (initial p c) ξ (trialCalls c)))‖
    Integrable (fun ξ => X ξ ^ 2) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, X ξ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ momentBound p := by
  intro c Q X
  have hi' (x : Space p) : Integrable (fun z : ℝ × Ω => answer (x, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hi x)
  have hm' (x : Space p) : (∫ z : ℝ × Ω, answer (x, none) z.2 ∂Q) = g x := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hmean x
  have hpi' (x : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hpi x)
  have hb' (x : Space p) : (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p := by
    have heq := integral_fun_snd (μ := (uniformLaw : Measure ℝ)) (ν := P)
      (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p)
    simp only [probReal_univ, one_smul] at heq
    exact heq.trans_le (hb x)
  have hM := guardRadius_bounds p hv
  have hg0 := configured_initial_gradient p hv f g hf hg hH hm hgap
  have growth := configured_proposal_growth p hv hcurv g hg hH
  have hguard := guard_pilot_moment p hv
  have hgroups := group_failure_small p hv
  have hv0 := hv
  rcases hv with ⟨_, _, hσ, hα, _, _, hp, hp2, _, _, _, _⟩
  have hh := HystereticHessianExpectation.trial_output_second_moment p c Q answer ha g hg.continuous.measurable
    hp.le hp2 hσ hα hM.1 rfl hi' hm' hpi' hb'
    (by simpa only [c, tuned_pilotBatch] using hguard)
    (by simpa only [c, tuned_groups] using hgroups) growth.1 growth.2
  refine ⟨hh.1, hh.2.trans ?_⟩
  rw [show blockCap c = logicalBlocks p from tuned_blockCap p hv0]
  have hsq : ‖g p.x0‖ ^ 2 ≤ (guardRadius p) ^ 2 := by nlinarith [norm_nonneg (g p.x0)]
  unfold momentBound
  nlinarith

lemma stream_expected_accuracy (p : Params) (hv : spec.valid p)
    {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (hgi : ∀ x, Integrable (answer (x, none)) P)
    (hgm : ∀ x, (∫ ω, answer (x, none) ω ∂P) = g x)
    (hgpi : ∀ x, Integrable (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p) P)
    (hgb : ∀ x, (∫ ω, ‖answer (x, none) ω - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hhi : ∀ y v, Integrable (answer (y, some v)) P)
    (hhm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hhpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hhb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q) :
    let c := tunedConfig p
    let Q := (uniformLaw : Measure ℝ).prod P
    let F := fun ξ => output p c (path p c answer (initial p c) ξ (trialCalls c))
    Measurable F ∧ Integrable (fun ξ => ‖g (F ξ)‖) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖g (F ξ)‖ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ p.ε := by
  intro c Q F
  have hF : Measurable F := measurable_trial_output p c answer ha (trialCalls c)
  by_cases hcurv : 0 < p.L0 + p.L1
  ·
    let X := fun ξ => ‖g (F ξ)‖
    let R := Measure.infinitePi fun _ : ℕ => Q
    let A := gradientBadEvent p hv hcurv answer g hg hH
    let B := noiseBadEvent p Q answer g
    have hX : Measurable X := (hg.continuous.measurable.comp hF).norm
    have hsecond := configured_second_moment p hv hcurv P answer ha f g hf hg hH hm hgap hgi hgm hgpi hgb
    have hA := gradient_bad_probability p hv hcurv P answer ha g hg hH hgi hgm hgpi hgb
    have hB := noise_bad_probability p hv hcurv P answer ha g hg hD hH hhi hhm hhpi hhb
    have hgood : ∀ ξ, ξ ∉ A → ξ ∉ B → X ξ ≤ targetAccuracy p := by
      intro ξ hξA hξB
      exact good_events_accuracy p hv hcurv P answer ha f g hf hg hD hH hm hgap hhi hhm hhpi hhb ξ hξA hξB
    have hδ : (logicalBlocks p : ℝ) * (1 / 2 : ℝ) ^ groupCount p +
        (macroCount p : ℝ) * Real.exp (-confidence p) ≤ (targetAccuracy p) ^ 2 / momentBound p := by
      have hh := mul_le_mul_of_nonneg_left (group_failure_bound p) (Nat.cast_nonneg (logicalBlocks p) : (0 : ℝ) ≤ logicalBlocks p)
      have hconf := confidence_failure_bound p hv
      push_cast at hconf
      nlinarith
    have hh := expected_of_two_failures R X hX (fun ξ => norm_nonneg _) hsecond.1 A B
      (targetAccuracy_pos p hv) (momentBound_pos p hv) hsecond.2 hgood hA hB hδ
    refine ⟨hF, hh.1, hh.2.trans_eq ?_⟩
    unfold targetAccuracy
    ring
  · rcases hv with ⟨hL0, hL1, _, _, _, _, _, _, _, _, _, hε⟩
    have h0 : p.L0 = 0 := by linarith
    have h1 : p.L1 = 0 := by linarith
    have hz (x : Space p) : g x = 0 :=
      HystereticHessianDescent.zero_curvature_gradient p f g hf hg
        (fun y => by simpa only [h0, h1, zero_mul, add_zero] using hH y) hm x
    have hzero : (fun ξ => ‖g (F ξ)‖) = fun _ => (0 : ℝ) := by
      funext ξ
      simp only [hz, norm_zero]
    rw [hzero]
    exact ⟨hF, integrable_const 0, by simpa only [integral_zero] using hε.le⟩

lemma execution_expected_accuracy (p : Params) (hv : spec.valid p)
    {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P0 (P : Measure _))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (f : Space p → ℝ) (g : Space p → Space p)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (hgi : ∀ x, Integrable (answer (x, none)) P0)
    (hgm : ∀ x, (∫ ω, answer (x, none) ω ∂P0) = g x)
    (hgpi : ∀ x, Integrable (fun ω => ‖answer (x, none) ω - g x‖ ^ p.p) P0)
    (hgb : ∀ x, (∫ ω, ‖answer (x, none) ω - g x‖ ^ p.p ∂P0) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hhi : ∀ y v, Integrable (answer (y, some v)) P0)
    (hhm : ∀ y v, (∫ ω, answer (y, some v) ω ∂P0) = fderiv ℝ g y v)
    (hhpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P0)
    (hhb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P0) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    (B : ℕ) (hB : trialCalls (tunedConfig p) ≤ B) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
    let A := tunedAlgorithm p
    let F := fun w : A.Seed × (ℕ → Ω) => OracleTemplate.execute O A (fun _ => B) w.1 w.2
    let J := (A.law : Measure _).prod (P : Measure _)
    Measurable F ∧ Integrable (fun w => ‖g (F w)‖) J ∧ (∫ w, ‖g (F w)‖ ∂J) ≤ p.ε := by
  intro O A F J
  let c := tunedConfig p
  let F0 := fun w : (Unit × (ℕ → ℝ)) × (ℕ → Ω) =>
    OracleTemplate.execute O (trial p c) (fun _ => trialCalls c) w.1 w.2
  have heq : F = F0 := by
    funext w
    exact (execute_bounded_trial_eq p c P answer B hB w.1 w.2).trans
      (execute_eq_path p c P answer w.1 w.2 (trialCalls c)).symm
  have hs := stream_expected_accuracy p hv P0 answer ha f g hf hg hD hH hm hgap
    hgi hgm hgpi hgb hhi hhm hhpi hhb
  have ht := execution_transfer p c P0 P h_samples answer ha (trialCalls c)
    (fun x => ‖g x‖) hg.continuous.measurable.norm
  rw [heq]
  exact ⟨ht.1, ht.2.1.mpr hs.2.1, ht.2.2.trans_le hs.2.2⟩

lemma specification_successful (p : Params) (hv : spec.valid p) (f : Space p → ℝ)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (hadm : spec.admissible p f O) (N : ℕ) (hN : trialCalls (tunedConfig p) ≤ N) :
    let A := tunedAlgorithm p
    spec.successful p f (fun w : A.Seed × ((k : ℕ) → O.Seed k) =>
      OracleTemplate.execute O A (fun _ => N) w.1 w.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hadm with ⟨a, h, P0, P, hsamples, rfl, hf, hcd, hH,
    ⟨m, hm, hgap⟩, ham, hhm, hai, hamean, hapi, hab, hhi, hhmean, hhpi, hhb⟩
  let : Nonempty p.Ω := nonempty_of_isProbabilityMeasure (P0 : Measure _)
  have hspace : WithLp.measurableSpace 2 (Fin p.d → ℝ) =
      LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector p.d := by
    let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
    exact BorelSpace.measurable_eq
  rw [hspace] at ham hhm
  let answer := fun q : Space p × Option (Space p) => fun ω : p.Ω =>
    match q.2 with
    | none => a q.1 ω
    | some v => h (q.1, v) ω
  have hanswer : Measurable (Function.uncurry answer) :=
    HystereticHessianMeasurable.measurable_oracle_answer p a h ham hhm
  have hg : Differentiable ℝ (gradient f) := hcd.differentiable (by norm_num)
  have hD : Continuous (fderiv ℝ (gradient f)) := hcd.continuous_fderiv (by norm_num)
  have hh := execution_expected_accuracy p hv (P0 : Measure _) P hsamples answer hanswer f (gradient f)
    hf hg hD hH hm hgap hai hamean hapi hab hhi hhmean hhpi hhb N hN
  dsimp only [spec]
  rw [hspace]
  exact hh

end LongTails.Proofs.HystereticHessianAccuracy
