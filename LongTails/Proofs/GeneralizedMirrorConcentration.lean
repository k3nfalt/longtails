import LongTails.Proofs.GeneralizedMirrorSampling
import LongTails.Proofs.GeneralizedMirrorWeights

open MeasureTheory
open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror
open LongTails.Proofs.GeneralizedMirrorProcess
open LongTails.Proofs.GeneralizedMirrorStopped
open LongTails.Proofs.GeneralizedMirrorWeights

namespace LongTails.Proofs.GeneralizedMirrorConcentration

noncomputable def liftScalar (q : Public) (m : ℕ)
    (F : State q m → (Fin (m + 2) → q.Ω) → ℝ) (n : ℕ) (s : State q m) (b : Fin n → q.Ω) : ℝ :=
  if h : n = m + 2 then F s (fun i => b ⟨i.val, by omega⟩) else 0

lemma liftScalar_full (q : Public) (m : ℕ) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (s : State q m) (b : Fin (m + 2) → q.Ω) : liftScalar q m F (m + 2) s b = F s b := by
  simp [liftScalar]

lemma measurable_liftScalar (q : Public) (m : ℕ) (F : State q m → (Fin (m + 2) → q.Ω) → ℝ)
    (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (Function.uncurry (liftScalar q m F n)) := by
  by_cases hn : n = m + 2
  · subst n
    simpa only [Function.uncurry_def, liftScalar_full] using hF
  · simpa only [Function.uncurry_def, liftScalar, dite_eq_right hn] using
      (measurable_const (a := (0 : ℝ)) : Measurable (fun _ : State q m × (Fin n → q.Ω) => (0 : ℝ)))

noncomputable def signedBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) : ℝ :=
  activeWeight q ell s * (stoppedError q ell m I g u s b) (u - s.z)

noncomputable def energyBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) : ℝ :=
  activeWeight q ell s ^ 2 * ‖stoppedError q ell m I g u s b‖ ^ 2

noncomputable def failureBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) : ℝ := by
  classical
  exact if Ready I u s ∧ ¬GoodPilot q ell m I g s b then 1 else 0

lemma measurable_signedBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) (hd : Measurable I.df)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s}) :
    Measurable (Function.uncurry (signedBlock q ell m I g u)) := by
  have he := measurable_stoppedError q ell m I hg hd u hr
  have hfst : Measurable (Prod.fst : State q m × (Fin (m + 2) → q.Ω) → State q m) := measurable_fst
  have hz := (GeneralizedMirrorExecution.measurable_state_z q m).comp hfst
  have hc : Continuous (fun z : Dual q × q.E => z.1 z.2) := by fun_prop
  exact ((measurable_activeWeight q ell m).comp hfst).mul
    (hc.measurable.comp (he.prodMk (measurable_const.sub hz)))

lemma measurable_energyBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) (hd : Measurable I.df)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s}) :
    Measurable (Function.uncurry (energyBlock q ell m I g u)) := by
  have he := measurable_stoppedError q ell m I hg hd u hr
  exact (((measurable_activeWeight q ell m).comp measurable_fst).pow_const 2).mul
    (he.norm.pow_const 2)

lemma measurable_failureBlock (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g)) (hd : Measurable I.df)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s}) :
    Measurable (Function.uncurry (failureBlock q ell m I g u)) :=
  measurable_const.ite ((hr.preimage measurable_fst).inter
    (measurableSet_goodPilot q ell m I hg hd).compl) measurable_const

lemma failureBlock_range (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) :
    0 ≤ failureBlock q ell m I g u s b ∧ failureBlock q ell m I g u s b ≤ 1 := by
  unfold failureBlock
  split_ifs <;> norm_num

lemma energyBlock_nonneg (q : Public) (ell : ℝ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (u : q.E) (s : State q m) (b : Fin (m + 2) → q.Ω) :
    0 ≤ energyBlock q ell m I g u s b := by unfold energyBlock; positivity

lemma energyBlock_mean (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (s : State q m) :
    (∫ b, energyBlock q ell m I g u s b ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤
      activeWeight q ell s ^ 2 * noiseMoment q := by
  by_cases hr : Ready I u s
  · have hy := (ready_query_mem hq hell I hQ hU u hr).1
    have hgp : Measurable (g (queryPoint q ell s)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    have he := GeneralizedMirrorSampling.stopped_second_moment q hq ell m I g u s μ
      hgp (hmi _ hy) (hm _ hy)
    unfold energyBlock
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
  · simp only [energyBlock, stoppedError, hr, false_and, ↓reduceIte, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, integral_zero]
    have hσ := hq.2.2.2.2.2.1
    have hB := GeneralizedMirrorTuning.clipRadius_pos q hq.2.2.1 hσ hq.2.2.2.2.2.2.2.2.1
    unfold noiseMoment
    positivity

lemma failureBlock_mean (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (s : State q m) :
    (∫ b, failureBlock q ell m I g u s b ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤
      (1 / 2 : ℝ) ^ m := by
  classical
  by_cases hr : Ready I u s
  · have hy := (ready_query_mem hq hell I hQ hU u hr).1
    have hgp : Measurable (g (queryPoint q ell s)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    let A : Set (Fin (m + 2) → q.Ω) := {b | clipRadius q / 2 <
      ‖blockCenter q ell m g s b - I.df (queryPoint q ell s)‖}
    have hc : Measurable (blockCenter q ell m g s) :=
      (measurable_blockCenter q ell m hg).comp measurable_prodMk_left
    have hA : MeasurableSet A := measurableSet_lt measurable_const (hc.sub_const _).norm
    have he : (fun b => failureBlock q ell m I g u s b) = A.indicator (fun _ => (1 : ℝ)) := by
      funext b
      simp [failureBlock, hr, GoodPilot, A, Set.indicator]
    rw [he]
    change (∫ b, A.indicator 1 b ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤ _
    rw [integral_indicator_one hA]
    have hb := GeneralizedMirrorSampling.block_pilot_failure q hq μ m hgp
      (I.df (queryPoint q ell s)) (hmi _ hy) (hm _ hy)
    have ht := ENNReal.toReal_mono (by finiteness) hb
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ m),
      A, blockCenter, GeneralizedMirrorSampling.splitBlock] using ht
  · simp [failureBlock, hr]

noncomputable def signedCompensator (q : Public) (ell θ : ℝ) {m : ℕ} (s : State q m) : ℝ :=
  θ * activeWeight q ell s * q.ε / 128 +
    4 * θ ^ 2 * q.R ^ 2 * (activeWeight q ell s ^ 2 * noiseMoment q)

lemma measurable_signedCompensator (q : Public) (ell θ : ℝ) (m : ℕ) :
    Measurable (signedCompensator q ell θ (m := m)) := by
  have ha := measurable_activeWeight q ell m
  exact (((ha.const_mul θ).mul_const q.ε).div_const 128).add
    (((ha.pow_const 2).mul_const (noiseMoment q)).const_mul (4 * θ ^ 2 * q.R ^ 2))

lemma signedBlock_mgf (q : Public) (hq : spec.valid q) {ell θ : ℝ} (hell : 0 < ell)
    (hθ : 0 ≤ θ) (hsmall : θ * (2 * q.R) * (q.R / (32768 * ell)) ≤ 1)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hi : ∀ x ∈ I.Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ I.Q, (∫ ω, g x ω ∂μ) = I.df x)
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u) (s : State q m) :
    Integrable (fun b => Real.exp (θ * signedBlock q ell m I g u s b))
      (Measure.pi fun _ : Fin (m + 2) => μ) ∧
      (∫ b, Real.exp (θ * signedBlock q ell m I g u s b)
        ∂Measure.pi (fun _ : Fin (m + 2) => μ)) ≤ Real.exp (signedCompensator q ell θ s) := by
  have ha := activeWeight_nonneg q hq hell s
  have hR := hq.2.2.1
  have hε := hq.2.2.2.2.2.2.2.2.1
  by_cases hr : Ready I u s
  · have hy := (ready_query_mem hq hell I hQ hU u hr).1
    have hz := ready_zradius I u hu hmin hR hd hstrong hr
    let l : Dual q →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (u - s.z)
    have hl : ‖l‖ ≤ 2 * q.R := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      change ‖v (u - s.z)‖ ≤ _
      calc
        _ ≤ ‖v‖ * ‖u - s.z‖ := v.le_opNorm _
        _ ≤ ‖v‖ * (2 * q.R) := mul_le_mul_of_nonneg_left (by rwa [norm_sub_rev]) (norm_nonneg _)
        _ = _ := by ring
    have hs : θ * activeWeight q ell s * (2 * q.R) * (3 * clipRadius q / 2) ≤ 1 := by
      have ht := mul_le_mul_of_nonneg_left (activeWeight_motion q hq hell s)
        (show 0 ≤ θ * (2 * q.R) by positivity)
      nlinarith only [ht, hsmall]
    have hgp : Measurable (g (queryPoint q ell s)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    have hb := GeneralizedMirrorSampling.stopped_signed_mgf q hq ell m I g u s μ hgp
      (hi _ hy) (hmean _ hy) (hmi _ hy) (hm _ hy) l hθ ha (by positivity) hl hs
    have he (b : Fin (m + 2) → q.Ω) : θ * signedBlock q ell m I g u s b =
        θ * activeWeight q ell s * l (stoppedError q ell m I g u s b) := by
      simp only [signedBlock, l, ContinuousLinearMap.apply_apply]
      ring
    simp_rw [he]
    refine ⟨hb.1, hb.2.trans (Real.exp_le_exp.mpr ?_)⟩
    have hβ := GeneralizedMirrorTuning.clipRadius_bias q hR hq.2.2.2.2.2.1
      hq.2.2.2.2.2.2.1 hε
    have ht := mul_le_mul_of_nonneg_left hβ (show 0 ≤ θ * activeWeight q ell s * (2 * q.R) by positivity)
    have heq : θ * activeWeight q ell s * (2 * q.R) * (q.ε / (256 * q.R)) =
        θ * activeWeight q ell s * q.ε / 128 := by field_simp; ring
    rw [heq] at ht
    unfold signedCompensator
    nlinarith only [ht]
  · simp only [signedBlock, stoppedError, hr, false_and, ↓reduceIte, zero_apply,
      mul_zero, Real.exp_zero]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    apply Real.one_le_exp_iff.mpr
    have hB := GeneralizedMirrorTuning.clipRadius_pos q hR hq.2.2.2.2.2.1 hε
    have hσ := hq.2.2.2.2.2.1
    unfold signedCompensator noiseMoment
    positivity

lemma energyBlock_bound (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (g : q.E → q.Ω → Dual q) (u : q.E)
    (s : State q m) (b : Fin (m + 2) → q.Ω) :
    energyBlock q ell m I g u s b ≤ (q.R / (32768 * ell)) ^ 2 := by
  have ha := activeWeight_nonneg q hq hell s
  have hB := GeneralizedMirrorTuning.clipRadius_pos q hq.2.2.1
    hq.2.2.2.2.2.1 hq.2.2.2.2.2.2.2.2.1
  have hb := stoppedError_bound q ell m I g u s b hB.le
  have ht := mul_le_mul_of_nonneg_left hb ha
  have hm := activeWeight_motion q hq hell s
  have hh := pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _)) (ht.trans hm) 2
  simpa only [mul_pow, energyBlock] using hh

lemma accumulated_signedCompensator_bound (q : Public) (hq : spec.valid q) {ell θ : ℝ}
    (hell : 0 < ell) (hθ : 0 ≤ θ) (m : ℕ) (I : Instance q)
    (g : q.E → q.Ω → Dual q) (s : State q m) (hA : 0 ≤ s.A)
    (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (ξ : ℕ → q.Ω) (k : ℕ) :
    OracleTemplate.StochasticGeneralized.accumulated (fun _ => m + 2) (liftedNext q ell m I g)
      (fun _ s _ => signedCompensator q ell θ s) k s ξ ≤
        θ * q.R ^ 2 / 64 + θ ^ 2 * q.R ^ 4 / (8192 * ell) := by
  have hw := accumulated_weights_bound q hq hell m I g s hA hs ξ k
  have hv := accumulated_variance_bound q hq hell m I g s hA hs ξ k
  have he : (fun (n : ℕ) (s : State q m) (_ : Fin n → q.Ω) => signedCompensator q ell θ s) =
      (fun n s b => (θ * q.ε / 128) * (fun _ s _ => activeWeight q ell s) n s b +
        (4 * θ ^ 2 * q.R ^ 2) * (fun _ s _ => activeWeight q ell s ^ 2 * noiseMoment q) n s b) := by
    funext n s b
    unfold signedCompensator
    ring
  rw [he, OracleTemplate.StochasticGeneralized.accumulated_linear]
  have hε := hq.2.2.2.2.2.2.2.2.1
  have hh := add_le_add (mul_le_mul_of_nonneg_left hw (show 0 ≤ θ * q.ε / 128 by positivity))
    (mul_le_mul_of_nonneg_left hv (show 0 ≤ 4 * θ ^ 2 * q.R ^ 2 by positivity))
  apply hh.trans_eq
  field_simp
  ring

lemma signed_tail (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U)
    (hd : ∀ z ∈ I.U, HasFDerivAt I.h (I.dh z) z) (hdf : Measurable I.df)
    (hstrong : ∀ z ∈ I.Q ∩ I.U, ∀ v ∈ I.Q, ‖v - z‖ ^ 2 / 2 ≤ divergence I v z)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hi : ∀ x ∈ I.Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ I.Q, (∫ ω, g x ω ∂μ) = I.df x)
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (hu : u ∈ I.Q) (hmin : IsMinOn (objective I) I.Q u)
    (hr : MeasurableSet {s : State q m | Ready I u s})
    (s : State q m) (hA : 0 ≤ s.A) (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real {ξ | q.R ^ 2 / 8 ≤
      OracleTemplate.StochasticGeneralized.accumulated (fun _ => m + 2) (liftedNext q ell m I g)
        (liftScalar q m (signedBlock q ell m I g u)) k s ξ} ≤ Real.exp (-4 * ell) := by
  have hell0 : 0 < ell := by linarith
  have hR := hq.2.2.1
  let θ := 64 * ell / q.R ^ 2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hsmall : θ * (2 * q.R) * (q.R / (32768 * ell)) ≤ 1 := by
    have he : θ * (2 * q.R) * (q.R / (32768 * ell)) = 1 / 256 := by
      dsimp [θ]
      field_simp
      ring
    rw [he]
    norm_num
  have hstep (t : State q m) := signedBlock_mgf q hq hell0 hθ hsmall m I hQ hU hd hstrong
    hg μ hi hmean hmi hm u hu hmin t
  have hinc (n : ℕ) := measurable_liftScalar q m (signedBlock q ell m I g u)
    (measurable_signedBlock q ell m I hg hdf u hr) n
  have h := OracleTemplate.RobustGradient.adaptive_compensated_tail μ
    (cost := fun _ : State q m => m + 2) (next := liftedNext q ell m I g)
    (increment := liftScalar q m (signedBlock q ell m I g u))
    (compensator := signedCompensator q ell θ)
    measurable_const (measurable_liftedNext q ell m I hg hp) hinc
    (measurable_signedCompensator q ell θ m) hθ
    (fun t => by simpa only [liftScalar_full] using hstep t) k s
    (fun ξ => accumulated_signedCompensator_bound q hq hell0 hθ m I g s hA hs ξ k)
    (t := q.R ^ 2 / 8)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have he : θ * q.R ^ 2 / 64 + θ ^ 2 * q.R ^ 4 / (8192 * ell) - θ * (q.R ^ 2 / 8) =
      -13 * ell / 2 := by
    dsimp [θ]
    field_simp
    ring
  rw [he]
  linarith

lemma energy_tail (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 1 ≤ ell)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U) (hdf : Measurable I.df)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s})
    (s : State q m) (hA : 0 ≤ s.A) (hs : s.A ≤ 2 * q.R ^ 2 / q.ε) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real {ξ | q.R ^ 2 / 16 ≤
      OracleTemplate.StochasticGeneralized.accumulated (fun _ => m + 2) (liftedNext q ell m I g)
        (liftScalar q m (energyBlock q ell m I g u)) k s ξ} ≤ Real.exp (-4 * ell) := by
  have hell0 : 0 < ell := by linarith
  have hR := hq.2.2.1
  let θ := 128 * ell / q.R ^ 2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hsmall : θ * (q.R / (32768 * ell)) ^ 2 ≤ 1 := by
    have he : θ * (q.R / (32768 * ell)) ^ 2 = 1 / (8388608 * ell) := by
      dsimp [θ]
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 8388608 * ell)).mpr
    linarith
  have hinc (n : ℕ) := measurable_liftScalar q m (energyBlock q ell m I g u)
    (measurable_energyBlock q ell m I hg hdf u hr) n
  have hmean : Measurable (fun t : State q m => activeWeight q ell t ^ 2 * noiseMoment q) :=
    ((measurable_activeWeight q ell m).pow_const 2).mul_const _
  have h := OracleTemplate.RobustGradient.adaptive_nonnegative_energy_tail μ
    (cost := fun _ : State q m => m + 2) (next := liftedNext q ell m I g)
    (energy := liftScalar q m (energyBlock q ell m I g u))
    (mean := fun t => activeWeight q ell t ^ 2 * noiseMoment q)
    measurable_const (measurable_liftedNext q ell m I hg hp) hinc hmean hθ hsmall
    (fun t b => by simpa only [liftScalar_full] using energyBlock_nonneg q ell m I g u t b)
    (fun t b => by simpa only [liftScalar_full] using energyBlock_bound q hq hell0 m I g u t b)
    (fun t => by simpa only [liftScalar_full] using energyBlock_mean q hq hell0 m I hQ hU hg μ hmi hm u t)
    k s (fun ξ => accumulated_variance_bound q hq hell0 m I g s hA hs ξ k)
    (t := q.R ^ 2 / 16)
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have he : 2 * θ * (q.R ^ 2 / (32768 * ell)) - θ * (q.R ^ 2 / 16) =
      1 / 128 - 8 * ell := by
    dsimp [θ]
    field_simp
    ring
  rw [he]
  linarith

lemma failure_tail (q : Public) (hq : spec.valid q) {ell : ℝ} (hell : 0 < ell)
    (m : ℕ) (I : Instance q) (hQ : Convex ℝ I.Q) (hU : Convex ℝ I.U) (hdf : Measurable I.df)
    {g : q.E → q.Ω → Dual q} (hg : Measurable (Function.uncurry g))
    (hp : Measurable (fun t : ℝ × q.E × Dual q => guardedProx q I t.1 t.2.1 t.2.2))
    (μ : Measure q.Ω) [IsProbabilityMeasure μ]
    (hmi : ∀ x ∈ I.Q, Integrable (fun ω => ‖g x ω - I.df x‖ ^ q.α) μ)
    (hm : ∀ x ∈ I.Q, (∫ ω, ‖g x ω - I.df x‖ ^ q.α ∂μ) ≤ q.σ ^ q.α)
    (u : q.E) (hr : MeasurableSet {s : State q m | Ready I u s}) (s : State q m) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).real {ξ | 1 ≤
      OracleTemplate.StochasticGeneralized.accumulated (fun _ => m + 2) (liftedNext q ell m I g)
        (liftScalar q m (failureBlock q ell m I g u)) k s ξ} ≤ k * (1 / 2 : ℝ) ^ m := by
  have hinc (n : ℕ) := measurable_liftScalar q m (failureBlock q ell m I g u)
    (measurable_failureBlock q ell m I hg hdf u hr) n
  have hzero (n : ℕ) (t : State q m) (b : Fin n → q.Ω) :
      0 ≤ liftScalar q m (failureBlock q ell m I g u) n t b ∧
        liftScalar q m (failureBlock q ell m I g u) n t b ≤ 1 := by
    unfold liftScalar
    split_ifs
    · exact failureBlock_range q ell m I g u t _
    · norm_num
  apply OracleTemplate.RobustGradient.adaptive_failure_count_bound μ
    (cost := fun _ : State q m => m + 2) (next := liftedNext q ell m I g)
    (failure := liftScalar q m (failureBlock q ell m I g u))
    (allowance := fun _ => (1 / 2 : ℝ) ^ m)
    measurable_const (measurable_liftedNext q ell m I hg hp) hinc measurable_const
    (fun n t b => (hzero n t b).1) (fun n t b => (hzero n t b).2)
    (fun _ => by positivity) (fun _ => pow_le_one₀ (by norm_num) (by norm_num))
    (fun t => by simpa only [liftScalar_full] using failureBlock_mean q hq hell m I hQ hU hg μ hmi hm u t)
    k s
  intro ξ
  rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum]
  simp

end LongTails.Proofs.GeneralizedMirrorConcentration
