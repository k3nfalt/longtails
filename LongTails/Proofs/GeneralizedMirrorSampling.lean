import LongTails.Proofs.GeneralizedMirrorStopped
import LongTails.Proofs.RobustSampleBlocks

open MeasureTheory

namespace LongTails.Proofs.GeneralizedMirrorSampling

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def splitBlock (m : ℕ) (b : Fin (m + 2) → Ω) : (Fin m → Ω) × Ω :=
  ((fun i => b ⟨i.val, by omega⟩), b ⟨m, by omega⟩)

noncomputable def joinBlock (m : ℕ) (b : (Fin m → Ω) × Ω) : Fin (m + 2) → Ω :=
  fun i => if h : i.val < m then b.1 ⟨i.val, h⟩ else b.2

lemma measurable_joinBlock (m : ℕ) : Measurable (joinBlock (Ω := Ω) m) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.val < m
  · simp only [joinBlock, dite_eq_left hi]
    exact (measurable_pi_apply (⟨i.val, hi⟩ : Fin m)).comp measurable_fst
  · simp only [joinBlock, dite_eq_right hi]
    exact measurable_snd

omit [MeasurableSpace Ω] in
lemma joinBlock_pilot (m : ℕ) (b : (Fin m → Ω) × Ω) (i : Fin m) :
    joinBlock m b ⟨i.val, by omega⟩ = b.1 i := by
  simp only [joinBlock, dite_eq_left i.isLt, Fin.eta]

omit [MeasurableSpace Ω] in
lemma joinBlock_fresh (m : ℕ) (b : (Fin m → Ω) × Ω) :
    joinBlock m b ⟨m, by omega⟩ = b.2 := by
  simp [joinBlock]

omit [MeasurableSpace Ω] in
lemma splitBlock_joinBlock (m : ℕ) (b : (Fin m → Ω) × Ω) : splitBlock m (joinBlock m b) = b := by
  apply Prod.ext
  · funext i
    simp [splitBlock, joinBlock]
  · simp [splitBlock, joinBlock]

lemma splitBlock_preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (splitBlock (Ω := Ω) m) (Measure.pi fun _ : Fin (m + 2) => μ)
      ((Measure.pi fun _ : Fin m => μ).prod μ) := by
  have h := ((MeasurePreserving.id (Measure.pi fun _ : Fin m => μ)).prod
    (measurePreserving_eval (μ := fun _ : Fin 2 => μ) (0 : Fin 2))).comp
      (OracleTemplate.RobustGradient.finite_split_preserving μ m 2)
  convert h using 1
  funext b
  rfl


lemma splitBlock_integral (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ)
    {F : (Fin m → Ω) × Ω → ℝ} (hi : Integrable F ((Measure.pi fun _ : Fin m => μ).prod μ)) :
    (∫ b, F (splitBlock m b) ∂Measure.pi (fun _ : Fin (m + 2) => μ)) =
      ∫ p, ∫ ω, F (p, ω) ∂μ ∂Measure.pi (fun _ : Fin m => μ) := by
  have hp := splitBlock_preserving μ m
  have hm : AEStronglyMeasurable F ((Measure.pi fun _ : Fin (m + 2) => μ).map (splitBlock m)) := by
    rw [hp.map_eq]
    exact hi.aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq, integral_prod F hi]

lemma splitBlock_exp_control (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ)
    {F : (Fin m → Ω) × Ω → ℝ} {C : ℝ}
    (hi : Integrable (fun z => Real.exp (F z)) ((Measure.pi fun _ : Fin m => μ).prod μ))
    (hb : (∫ z, Real.exp (F z) ∂(Measure.pi fun _ : Fin m => μ).prod μ) ≤ C) :
    Integrable (fun b => Real.exp (F (splitBlock m b))) (Measure.pi fun _ : Fin (m + 2) => μ) ∧
      (∫ b, Real.exp (F (splitBlock m b)) ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤ C := by
  have hp := splitBlock_preserving μ m
  refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
  have hm : AEStronglyMeasurable (fun z => Real.exp (F z))
      ((Measure.pi fun _ : Fin (m + 2) => μ).map (splitBlock m)) := by
    rw [hp.map_eq]
    exact hi.aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq]
  exact hb

lemma pilot_projection_preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (fun b : Fin (m + 2) → Ω => (splitBlock m b).1)
      (Measure.pi fun _ : Fin (m + 2) => μ) (Measure.pi fun _ : Fin m => μ) :=
  (measurePreserving_fst (μ := Measure.pi fun _ : Fin m => μ) (ν := μ)).comp
    (splitBlock_preserving μ m)

open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror

lemma block_pilot_failure (q : Public) (hq : spec.valid q) (μ : Measure q.Ω)
    [IsProbabilityMeasure μ] (m : ℕ) {W : q.Ω → Dual q} (hW : Measurable W) (u : Dual q)
    (hmi : Integrable (fun ω => ‖W ω - u‖ ^ q.α) μ)
    (hm : (∫ ω, ‖W ω - u‖ ^ q.α ∂μ) ≤ q.σ ^ q.α) :
    (Measure.pi fun _ : Fin (m + 2) => μ)
      {b | clipRadius q / 2 < ‖OracleTemplate.RobustGradient.pilotCenter (clipRadius q)
        (fun i : Fin m => W ((splitBlock m b).1 i)) - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  rcases hq with ⟨_, _, hR, _, _, hσ, hα, _, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  have hscale := GeneralizedMirrorNoise.pilot_scale hσ hα.le
    (GeneralizedMirrorTuning.clipRadius_pilot q hR hσ hε)
  have hconf := GeneralizedMirrorNoise.pilot_moment_confidence hW hB (by linarith : 0 ≤ q.α)
    u hmi (hm.trans hscale) m
  have hv : Measurable (fun b : Fin m → q.Ω => fun i => W (b i)) := by
    apply Measurable.of_eval
    intro i
    exact hW.comp (measurable_pi_apply i)
  have hc := (OracleTemplate.RobustGradient.measurable_pilotCenter m).comp
    ((measurable_const (a := clipRadius q)).prodMk hv)
  have hs := measurableSet_lt (measurable_const (a := clipRadius q / 2)) (hc.sub_const u).norm
  have hp := (pilot_projection_preserving μ m).measure_preimage hs.nullMeasurableSet
  change (Measure.pi fun _ : Fin (m + 2) => μ)
    ((fun b => (splitBlock m b).1) ⁻¹' {b | clipRadius q / 2 <
      ‖OracleTemplate.RobustGradient.pilotCenter (clipRadius q) (fun i => W (b i)) - u‖}) ≤ _
  simp only [Function.comp_def] at hp
  rw [hp]
  exact hconf

lemma stoppedError_join_split (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) :
    GeneralizedMirrorStopped.stoppedError q ell m I g u s (joinBlock m (splitBlock m b)) =
      GeneralizedMirrorStopped.stoppedError q ell m I g u s b := by
  have hc : GeneralizedMirrorProcess.blockCenter q ell m g s (joinBlock m (splitBlock m b)) =
      GeneralizedMirrorProcess.blockCenter q ell m g s b := by
    unfold GeneralizedMirrorProcess.blockCenter
    congr 1
    funext i
    rw [joinBlock_pilot]
    rfl
  unfold GeneralizedMirrorStopped.stoppedError GeneralizedMirrorStopped.GoodPilot
  rw [hc]
  simp only [GeneralizedMirrorProcess.blockDirection, hc, joinBlock_fresh]
  rfl

lemma stopped_signed_mgf (q : Public) (hq : spec.valid q) (ell : ℝ) (m : ℕ)
    (I : Instance q) (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m)
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hg : Measurable (g (GeneralizedMirrorProcess.queryPoint q ell s)))
    (hi : Integrable (g (GeneralizedMirrorProcess.queryPoint q ell s)) μ)
    (hmean : ∫ ω, g (GeneralizedMirrorProcess.queryPoint q ell s) ω ∂μ =
      I.df (GeneralizedMirrorProcess.queryPoint q ell s))
    (hmi : Integrable (fun ω => ‖g (GeneralizedMirrorProcess.queryPoint q ell s) ω -
      I.df (GeneralizedMirrorProcess.queryPoint q ell s)‖ ^ q.α) μ)
    (hm : (∫ ω, ‖g (GeneralizedMirrorProcess.queryPoint q ell s) ω -
      I.df (GeneralizedMirrorProcess.queryPoint q ell s)‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (l : Dual q →L[ℝ] ℝ) {θ a D : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hl : ‖l‖ ≤ D)
    (hsmall : θ * a * D * (3 * clipRadius q / 2) ≤ 1) :
    Integrable (fun b => Real.exp (θ * a * l
      (GeneralizedMirrorStopped.stoppedError q ell m I g u s b)))
      (Measure.pi fun _ : Fin (m + 2) => μ) ∧
      (∫ b, Real.exp (θ * a * l (GeneralizedMirrorStopped.stoppedError q ell m I g u s b))
        ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤
      Real.exp (θ * a * D * (q.σ ^ q.α / (clipRadius q / 2) ^ (q.α - 1)) +
        θ ^ 2 * a ^ 2 * D ^ 2 * noiseMoment q) := by
  classical
  rcases hq with ⟨_, _, hR, _, _, hσ, hα, hα2, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  by_cases hr : GeneralizedMirrorStopped.Ready I u s
  · let c := fun p : Fin m → q.Ω => OracleTemplate.RobustGradient.pilotCenter (clipRadius q)
      (fun i => g (GeneralizedMirrorProcess.queryPoint q ell s) (p i))
    have hv : Measurable (fun p : Fin m → q.Ω => fun i =>
        g (GeneralizedMirrorProcess.queryPoint q ell s) (p i)) := by
      apply Measurable.of_eval
      intro i
      exact hg.comp (measurable_pi_apply i)
    have hc : Measurable c := (OracleTemplate.RobustGradient.measurable_pilotCenter m).comp
      ((measurable_const (a := clipRadius q)).prodMk hv)
    have h := GeneralizedMirrorNoise.centered_pilot_mgf (Measure.pi fun _ : Fin m => μ)
      hg hi hB hα.le hα2 hσ c hc (I.df (GeneralizedMirrorProcess.queryPoint q ell s))
      hmean hmi hm l hθ ha hD hl hsmall
    have hb := splitBlock_exp_control μ m h.1 h.2
    simp only [GeneralizedMirrorStopped.stoppedError, GeneralizedMirrorStopped.GoodPilot,
      hr, true_and, GeneralizedMirrorProcess.blockDirection, GeneralizedMirrorProcess.blockCenter,
      splitBlock, c, noiseMoment] at hb ⊢
    convert hb using 1 <;> congr! 8
  · simp only [GeneralizedMirrorStopped.stoppedError, hr, false_and, ↓reduceIte,
      map_zero, mul_zero, Real.exp_zero]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    apply Real.one_le_exp_iff.mpr
    unfold noiseMoment
    positivity

lemma stopped_second_moment (q : Public) (hq : spec.valid q) (ell : ℝ) (m : ℕ)
    (I : Instance q) (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m)
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hg : Measurable (g (GeneralizedMirrorProcess.queryPoint q ell s)))
    (hmi : Integrable (fun ω => ‖g (GeneralizedMirrorProcess.queryPoint q ell s) ω -
      I.df (GeneralizedMirrorProcess.queryPoint q ell s)‖ ^ q.α) μ)
    (hm : (∫ ω, ‖g (GeneralizedMirrorProcess.queryPoint q ell s) ω -
      I.df (GeneralizedMirrorProcess.queryPoint q ell s)‖ ^ q.α ∂μ) ≤ q.σ ^ q.α) :
    Integrable (fun b => ‖GeneralizedMirrorStopped.stoppedError q ell m I g u s b‖ ^ 2)
      (Measure.pi fun _ : Fin (m + 2) => μ) ∧
      (∫ b, ‖GeneralizedMirrorStopped.stoppedError q ell m I g u s b‖ ^ 2
        ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤ noiseMoment q := by
  classical
  rcases hq with ⟨_, _, hR, _, _, hσ, hα, hα2, hε, _⟩
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hσ hε
  by_cases hr : GeneralizedMirrorStopped.Ready I u s
  · let c := fun p : Fin m → q.Ω => OracleTemplate.RobustGradient.pilotCenter (clipRadius q)
      (fun i => g (GeneralizedMirrorProcess.queryPoint q ell s) (p i))
    have hv : Measurable (fun p : Fin m → q.Ω => fun i =>
        g (GeneralizedMirrorProcess.queryPoint q ell s) (p i)) := by
      apply Measurable.of_eval
      intro i
      exact hg.comp (measurable_pi_apply i)
    have hc : Measurable c := (OracleTemplate.RobustGradient.measurable_pilotCenter m).comp
      ((measurable_const (a := clipRadius q)).prodMk hv)
    have h := GeneralizedMirrorNoise.centered_pilot_second_moment
      (Measure.pi fun _ : Fin m => μ) hg hB (by linarith : 0 ≤ q.α) hα2 hσ c hc
      (I.df (GeneralizedMirrorProcess.queryPoint q ell s)) hmi hm
    let F := fun z : (Fin m → q.Ω) × q.Ω => ‖if
      ‖c z.1 - I.df (GeneralizedMirrorProcess.queryPoint q ell s)‖ ≤ clipRadius q / 2 then
        OracleTemplate.RobustGradient.centeredClip (clipRadius q) (c z.1)
          (g (GeneralizedMirrorProcess.queryPoint q ell s) z.2) -
            I.df (GeneralizedMirrorProcess.queryPoint q ell s) else 0‖ ^ 2
    have hp := splitBlock_preserving μ m
    have hi : Integrable F ((Measure.pi fun _ : Fin m => μ).prod μ) := h.1
    have hb : Integrable (fun b => F (splitBlock m b)) (Measure.pi fun _ : Fin (m + 2) => μ) ∧
        (∫ b, F (splitBlock m b) ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤ noiseMoment q := by
      refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
      have hmeas : AEStronglyMeasurable F
          ((Measure.pi fun _ : Fin (m + 2) => μ).map (splitBlock m)) := by
        rw [hp.map_eq]
        exact hi.aestronglyMeasurable
      rw [← integral_map hp.measurable.aemeasurable hmeas, hp.map_eq]
      exact h.2
    simp only [GeneralizedMirrorStopped.stoppedError, GeneralizedMirrorStopped.GoodPilot,
      hr, true_and, GeneralizedMirrorProcess.blockDirection, GeneralizedMirrorProcess.blockCenter,
      splitBlock, c, F] at hb ⊢
    convert hb using 1
  · simp only [GeneralizedMirrorStopped.stoppedError, hr, false_and, ↓reduceIte,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    refine ⟨integrable_const _, ?_⟩
    unfold noiseMoment
    positivity

end LongTails.Proofs.GeneralizedMirrorSampling
