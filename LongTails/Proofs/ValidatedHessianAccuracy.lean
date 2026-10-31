import LongTails.Proofs.ValidatedHessianSampling
import LongTails.Proofs.ValidatedHessianTuning

open MeasureTheory
open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.GuardedHessianTransport
open LongTails.Proofs.ValidatedHessianExecution
open LongTails.Proofs.ValidatedHessianSampling

namespace LongTails.Proofs.ValidatedHessianAccuracy

set_option maxHeartbeats 800000 in
lemma wrapper_accuracy (p : Params) (c : Config) (K B : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (R : Measure (Fin (c.steps + 1))) [IsProbabilityMeasure R]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (g : Space p → Space p) (hg : Measurable g)
    (ha : Measurable (fun w : Space p × (ℝ × Ω) => answer (w.1, none) w.2.2))
    (hp : 1 < p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hε : 0 < p.ε) (hB : 0 < B) (h0 : ‖g p.x0‖ ≤ M)
    (hai : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (ham : ∀ x, (∫ z : ℝ × Ω, answer (x, none) z.2 ∂P) = g x)
    (hapi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hab : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hi : Integrable (fun w => ‖g (finiteTrialPoint p c answer w)‖ ^ 2)
      (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)))
    (hb : (∫ w, ‖g (finiteTrialPoint p c answer w)‖ ^ 2
      ∂R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)) ≤ 9 * M ^ 2)
    (hbad : (R.prod (Measure.pi fun _ : Fin (trialCalls c) => P)).real
      {w | p.ε / 4 < ‖g (finiteTrialPoint p c answer w)‖} ≤ 1 / 3) :
    let Q := (Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => P)
    let X := fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) =>
      LongTails.Algorithms.ValidatedHessianTransport.output p c K B
        (HeavyTailedProductProcess.trajectory (step p c K B answer)
          (LongTails.Algorithms.ValidatedHessianTransport.calls c K B)
          (LongTails.Algorithms.ValidatedHessianTransport.initial p c K w.1) w.2)
    Measurable X ∧ Integrable (fun w => ‖g (X w)‖) Q ∧
      (∫ w, ‖g (X w)‖ ∂Q) ≤ p.ε / 4 + M * (1 / 3 : ℝ) ^ K +
        120 * (K + 1 : ℕ) * (p.σg + p.αg * M) * ((B : ℝ) ^ (p.p - 1))⁻¹ ^ p.p⁻¹ := by
  intro Q X
  let μ := (Measure.pi fun _ : Fin K => R).prod
    (Measure.pi fun _ : Fin (K * trialCalls c) => P)
  let V := finiteBlockCandidates p c K answer
  have hV : Measurable V := measurable_finiteBlockCandidates p c K answer hstep
  have hfinite := finite_candidates_guarantees p c K P R answer hstep g hg hM.le h0 hi hb hbad
  let estimates := fun w : ((Fin K → Fin (c.steps + 1)) ×
      (Fin (K * trialCalls c) → ℝ × Ω)) × (ℕ → ℝ × Ω) => fun j : Fin (K + 1) =>
    (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B, answer (V w.1 j, none) (w.2 (j.val * B + i)).2
  let Y := fun w => V w.1 (bestEstimate (estimates w))
  have he : Measurable estimates := by
    apply Measurable.of_eval
    intro j
    have hj (i : ℕ) : Measurable (fun w : ((Fin K → Fin (c.steps + 1)) ×
        (Fin (K * trialCalls c) → ℝ × Ω)) × (ℕ → ℝ × Ω) =>
      answer (V w.1 j, none) (w.2 (j.val * B + i)).2) :=
      ha.comp (f := fun w : ((Fin K → Fin (c.steps + 1)) ×
        (Fin (K * trialCalls c) → ℝ × Ω)) × (ℕ → ℝ × Ω) =>
        (V w.1 j, w.2 (j.val * B + i))) (by fun_prop)
    exact (Finset.measurable_sum (Finset.range B) (fun i _ => hj i)).const_smul (B : ℝ)⁻¹
  have heval : Measurable (fun w : (Fin (K + 1) → Space p) × Fin (K + 1) => w.1 w.2) :=
    measurable_from_prod_countable_left (fun j => measurable_pi_apply j)
  have hY : Measurable Y := heval.comp
    ((hV.comp measurable_fst).prodMk (GuardedHessianValidation.measurable_bestEstimate.comp he))
  have hbound := GuardedHessianValidation.fresh_validated_selection
    (r := p.ε / 4) (δ := (1 / 3 : ℝ) ^ K) μ P K V g
    (fun x z => answer (x, none) z.2) hV hg ha hp.le hp2 hσ hα hM (by positivity) B hB
    hai ham hapi hab (fun j => (hfinite.1 j).1) (fun j => (hfinite.1 j).2)
    (fun _ => h0) hfinite.2
  have hpres := OracleTemplate.ScalarHeavyTailEstimator.seed_prefix_tail_preserving
    (P := P) (Measure.pi fun _ : Fin K => R) (K * trialCalls c)
  have heq : Y ∘ (fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) =>
      ((w.1, fun i : Fin (K * trialCalls c) => w.2 i.val),
        fun j => w.2 (K * trialCalls c + j))) = X := by
    funext w
    dsimp only [X]
    rw [output_representation p c K B answer w.1 w.2 hB]
    simp only [Y, estimates, V, Function.comp_def, finiteBlockCandidates_eq]
  have hF : Measurable (fun w => ‖g (Y w)‖) := (hg.comp hY).norm
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]
    exact hY.comp hpres.measurable
  · have hh := (hpres.integrable_comp hF.aestronglyMeasurable).mpr hbound.1
    simpa only [Function.comp_def, ← heq] using hh
  · have hh : (∫ w, ‖g (Y w)‖ ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) =
        ∫ w, ‖g (X w)‖ ∂Q := by
      dsimp only [μ]
      rw [← hpres.map_eq, integral_map hpres.measurable.aemeasurable hF.aestronglyMeasurable]
      simp only [← heq, Function.comp_def]
      rfl
    rw [← hh]
    exact hbound.2

lemma oracle_tuned_wrapper (p : Params) (hv : spec.valid p) (c : Config) (hc : c = tunedConfig p) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (f : Space p → ℝ) (g : Space p → Space p)
    (hgm : Measurable (fun w : Space p × Ω => answer (w.1, none) w.2))
    (hhm : Measurable (fun w : (Space p × Space p) × Ω => answer (w.1.1, some w.1.2) w.2))
    (hstep : Measurable (fun w : State p c × (ℝ × Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)))
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    (hgi : ∀ y, Integrable (answer (y, none)) P)
    (hgmean : ∀ y, (∫ ω, answer (y, none) ω ∂P) = g y)
    (hgpi : ∀ y, Integrable (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p) P)
    (hgb : ∀ y, (∫ ω, ‖answer (y, none) ω - g y‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p)
    (hhi : ∀ y v, Integrable (answer (y, some v)) P)
    (hhmean : ∀ y v, (∫ ω, answer (y, some v) ω ∂P) = fderiv ℝ g y v)
    (hhpi : ∀ y v, Integrable (fun ω => ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q) P)
    (hhb : ∀ y v, (∫ ω, ‖answer (y, some v) ω - fderiv ℝ g y v‖ ^ p.q ∂P) ≤
      (p.σh ^ p.q + p.αh ^ p.q * ‖g y‖ ^ p.q) * ‖v‖ ^ p.q)
    {m : ℝ} (hf : ∀ x, HasGradientAt f (g x) x)
    (hm : ∀ x, m ≤ f x) (hgap : f p.x0 - m ≤ p.Δ)
    (reference : Fin (c.steps + 1)) :
    let K := LongTails.Algorithms.ValidatedHessianTransport.repeatCount p
    let B := LongTails.Algorithms.ValidatedHessianTransport.validationCount p
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let R := (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure
    let S := (Measure.pi fun _ : Fin K => R).prod (Measure.infinitePi fun _ : ℕ => Q)
    let X := fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) =>
      LongTails.Algorithms.ValidatedHessianTransport.output p c K B
        (HeavyTailedProductProcess.trajectory (step p c K B answer)
          (LongTails.Algorithms.ValidatedHessianTransport.calls c K B)
          (LongTails.Algorithms.ValidatedHessianTransport.initial p c K w.1) w.2)
    Measurable X ∧ Integrable (fun w => ‖g (X w)‖) S ∧ (∫ w, ‖g (X w)‖ ∂S) ≤ p.ε := by
  intro K B Q R S X
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  have : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  have : IsProbabilityMeasure R := inferInstanceAs
    (IsProbabilityMeasure (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure)
  have ht := GuardedHessianTrial.oracle_tuned_trial p hv c hc P answer f g hgm hhm hstep
    hg hD hH hgi hgmean hgpi hgb hhi hhmean hhpi hhb hf hm hgap reference
  have hfinite := finite_trial_guarantees p c Q R answer hstep g hg.continuous.measurable
    ht.1 ht.2.1 ht.2.2
  have h0 := GuardedHessianTuning.initial_gradient_bound p hv f g hf hg hH hm hgap
  have hnumeric := ValidatedHessianTuning.tuned_expected_small p hv
  rcases hv with ⟨hL0, hL1, hσg, hαg, hσh, hαh, hp, hp2, hq, hq2, hΔ, hε⟩
  have hM := (GuardedHessianTuning.radius_estimates p hL0 hL1 hΔ hε).1
  have hgm' : Measurable (fun w : Space p × (ℝ × Ω) => answer (w.1, none) w.2.2) :=
    hgm.comp (f := fun w : Space p × (ℝ × Ω) => (w.1, w.2.2)) (by fun_prop)
  have hgi' (y : Space p) : Integrable (fun z : ℝ × Ω => answer (y, none) z.2) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgi y)
  have hgmean' (y : Space p) : (∫ z : ℝ × Ω, answer (y, none) z.2 ∂Q) = g y := by
    simpa only [Q, integral_fun_snd, probReal_univ, one_smul] using hgmean y
  have hgpi' (y : Space p) : Integrable (fun z : ℝ × Ω => ‖answer (y, none) z.2 - g y‖ ^ p.p) Q :=
    measurePreserving_snd.integrable_comp_of_integrable (hgpi y)
  have hgb' (y : Space p) : (∫ z : ℝ × Ω, ‖answer (y, none) z.2 - g y‖ ^ p.p ∂Q) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g y‖ ^ p.p := by
    have heq := integral_fun_snd (μ := U) (ν := P) (fun ω => ‖answer (y, none) ω - g y‖ ^ p.p)
    simp only [probReal_univ, one_smul] at heq
    exact heq.trans_le (hgb y)
  have hh := wrapper_accuracy p c K B Q R answer hstep g hg.continuous.measurable hgm'
    hp hp2 hσg hαg hM hε (ValidatedHessianTuning.validationCount_pos p) h0
    hgi' hgmean' hgpi' hgb' hfinite.1 hfinite.2.1 hfinite.2.2
  exact ⟨hh.1, hh.2.1, hh.2.2.trans hnumeric⟩

lemma execution_transfer (p : Params) (c : Config) (K B : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P0 : Measure Ω) [IsProbabilityMeasure P0] (P : ProbabilityMeasure (ℕ → Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P0 (P : Measure _))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (hg : Measurable g) (hB : 0 < B)
    (N : ℕ) (hN : LongTails.Algorithms.ValidatedHessianTransport.calls c K B ≤ N)
    (X : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × Ω) → Space p)
    (hXeq : ∀ w, X w = LongTails.Algorithms.ValidatedHessianTransport.output p c K B
      (HeavyTailedProductProcess.trajectory (step p c K B answer)
        (LongTails.Algorithms.ValidatedHessianTransport.calls c K B)
        (LongTails.Algorithms.ValidatedHessianTransport.initial p c K w.1) w.2))
    (hX : Measurable X)
    (hi : Integrable (fun w => ‖g (X w)‖)
      ((Measure.pi fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure).prod
        (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ).prod P0)))
    (hb : (∫ w, ‖g (X w)‖
      ∂(Measure.pi fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure).prod
        (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ).prod P0)) ≤ p.ε) :
    let O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
    let A := LongTails.Algorithms.ValidatedHessianTransport.algorithm p c K B
    let F := fun w : ((Fin K → Fin (c.steps + 1)) × (ℕ → ℝ)) × (ℕ → Ω) =>
      OracleTemplate.execute O A (fun _ => N) w.1 w.2
    let J := ((Measure.pi fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ))).prod (P : Measure _)
    Measurable F ∧ Integrable (fun w => ‖g (F w)‖) J ∧ (∫ w, ‖g (F w)‖ ∂J) ≤ p.ε := by
  intro O A F J
  let R := Measure.pi fun _ : Fin K => (PMF.uniformOfFintype (Fin (c.steps + 1))).toMeasure
  let Z := fun w : ((Fin K → Fin (c.steps + 1)) × (ℕ → ℝ)) × (ℕ → Ω) =>
    (w.1.1, fun k => (w.1.2 k, w.2 k))
  have hPlaw : (P : Measure _) = Measure.infinitePi fun _ : ℕ => P0 := by
    have hh := h_samples.stream_law.map_eq
    change (P : Measure (ℕ → Ω)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  have hZ : MeasurePreserving Z J
      (R.prod (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ).prod P0)) := by
    dsimp only [J]
    rw [hPlaw]
    exact HeavyTailedTapeExecution.initial_zip_streams_preserving R (uniformLaw : Measure ℝ) P0
  have heq : F = X ∘ Z := by
    funext w
    change F w = X (Z w)
    rw [hXeq]
    exact (execute_wrapper p c K B P answer w.1 w.2 hB N hN).trans
      (output_representation p c K B answer (Z w).1 (Z w).2 hB).symm
  have hG : Measurable (fun w => ‖g (X w)‖) := (hg.comp hX).norm
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact hX.comp hZ.measurable
  · rw [heq]
    exact (hZ.integrable_comp hG.aestronglyMeasurable).mpr hi
  · have hh : (∫ w, ‖g (X w)‖
        ∂R.prod (Measure.infinitePi fun _ : ℕ => (uniformLaw : Measure ℝ).prod P0)) =
        ∫ w, ‖g (F w)‖ ∂J := by
      rw [← hZ.map_eq, integral_map hZ.measurable.aemeasurable hG.aestronglyMeasurable]
      simp only [heq, Function.comp_def]
    rw [← hh]
    exact hb

lemma specification_successful (p : Params) (hv : spec.valid p) (f : Space p → ℝ)
    (O : OracleTemplate.Oracle (Space p × Option (Space p)) (Space p))
    (hadm : spec.admissible p f O) (N : ℕ)
    (hN : LongTails.Algorithms.ValidatedHessianTransport.calls (tunedConfig p)
      (LongTails.Algorithms.ValidatedHessianTransport.repeatCount p)
      (LongTails.Algorithms.ValidatedHessianTransport.validationCount p) ≤ N) :
    let A := LongTails.Algorithms.ValidatedHessianTransport.tunedAlgorithm p
    spec.successful p f (fun w : A.Seed × ((k : ℕ) → O.Seed k) =>
      OracleTemplate.execute O A (fun _ => N) w.1 w.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hadm with ⟨a, h, P0, P, hsamples, rfl, hf, hcd, hH,
    ⟨m, hm, hgap⟩, ham, hhm, hai, hamean, hapi, hab, hhi, hhmean, hhpi, hhb⟩
  have hspace : WithLp.measurableSpace 2 (Fin p.d → ℝ) =
      LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector p.d := by
    let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
    exact BorelSpace.measurable_eq
  rw [hspace] at ham hhm
  let c := tunedConfig p
  let answer := fun q : Space p × Option (Space p) => fun ω : p.Ω =>
    match q.2 with
    | none => a q.1 ω
    | some v => h (q.1, v) ω
  have hg : Differentiable ℝ (gradient f) := hcd.differentiable (by norm_num)
  have hD : Continuous (fderiv ℝ (gradient f)) := hcd.continuous_fderiv (by norm_num)
  have hstep : Measurable (fun w : State p c × (ℝ × p.Ω) =>
      update p c w.1 w.2.1 (answer (query p c w.1 w.2.1) w.2.2)) :=
    GuardedHessianMeasurable.measurable_step p c a h ham hhm
  have ht := oracle_tuned_wrapper p hv c rfl (P0 : Measure _) answer f (gradient f) ham hhm hstep
    hg hD hH hai hamean hapi hab hhi hhmean hhpi hhb hf hm hgap ⟨0, by omega⟩
  let K := LongTails.Algorithms.ValidatedHessianTransport.repeatCount p
  let B := LongTails.Algorithms.ValidatedHessianTransport.validationCount p
  let X := fun w : (Fin K → Fin (c.steps + 1)) × (ℕ → ℝ × p.Ω) =>
    LongTails.Algorithms.ValidatedHessianTransport.output p c K B
      (HeavyTailedProductProcess.trajectory (step p c K B answer)
        (LongTails.Algorithms.ValidatedHessianTransport.calls c K B)
        (LongTails.Algorithms.ValidatedHessianTransport.initial p c K w.1) w.2)
  have hh := execution_transfer p c K B (P0 : Measure p.Ω) P hsamples answer (gradient f)
    hg.continuous.measurable (ValidatedHessianTuning.validationCount_pos p) N hN X (fun _ => rfl)
    ht.1 (by simpa only [uniformLaw, ProbabilityMeasure.coe_mk, X, K, B] using ht.2.1) (by simpa only [uniformLaw, ProbabilityMeasure.coe_mk, X, K, B] using ht.2.2)
  dsimp only [spec]
  rw [hspace]
  exact hh

end LongTails.Proofs.ValidatedHessianAccuracy
