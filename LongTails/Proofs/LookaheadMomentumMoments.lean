import LongTails.Proofs.LookaheadMomentumRun
import LongTails.Proofs.CompositeTransportMoments

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.LookaheadMomentum

open OracleTemplate.CompositeTransport (OracleHyp inner_step init_partial_moment)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Defs

variable (cfg : Config) (x0 : E) (g : E → Ω → E) (grad : E → E) (ξ : ℕ → Ω)

noncomputable def nearOf (s : E × E × E) : E := leadNear cfg (stepTo cfg s.1 s.2.2) s.1

noncomputable def farOf (s : E × E × E) : E := leadFar cfg (stepTo cfg s.1 s.2.2) s.1

noncomputable def noise : ℕ → E
  | 0 => (1 / (cfg.n0 : ℝ)) • ∑ i ∈ Finset.range cfg.n0, (g x0 (ξ i) - grad x0)
  | t + 1 => keep cfg • noise t +
      weightNear cfg • (g (nearOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t)) -
        grad (nearOf cfg (traj cfg x0 g ξ t))) +
      weightFar cfg • (g (farOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t + 1)) -
        grad (farOf cfg (traj cfg x0 g ξ t)))

noncomputable def halfNoise (t : ℕ) : E :=
  keep cfg • noise cfg x0 g grad ξ t +
    weightNear cfg • (g (nearOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t)) -
      grad (nearOf cfg (traj cfg x0 g ξ t)))

noncomputable def drift (x x' : E) : E :=
  keep cfg • (grad x - grad x') + weightNear cfg • (grad (leadNear cfg x' x) - grad x') +
    weightFar cfg • (grad (leadFar cfg x' x) - grad x')

noncomputable def bias : ℕ → E
  | 0 => 0
  | t + 1 => keep cfg • bias t +
      drift cfg grad (traj cfg x0 g ξ t).1 (traj cfg x0 g ξ (t + 1)).1

lemma traj_succ_fst (t : ℕ) : (traj cfg x0 g ξ (t + 1)).1 =
    stepTo cfg (traj cfg x0 g ξ t).1 (traj cfg x0 g ξ t).2.2 := rfl

lemma traj_succ_snd (t : ℕ) : (traj cfg x0 g ξ (t + 1)).2.2 =
    keep cfg • (traj cfg x0 g ξ t).2.2 +
      weightNear cfg • g (nearOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t)) +
      weightFar cfg • g (farOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t + 1)) := rfl

lemma weights_sum : keep cfg + weightNear cfg + weightFar cfg = 1 := by
  unfold keep weightNear weightFar
  ring

lemma error_split (hn : 1 ≤ cfg.n0) : ∀ t,
    (traj cfg x0 g ξ t).2.2 - grad (traj cfg x0 g ξ t).1 =
      noise cfg x0 g grad ξ t + bias cfg x0 g grad ξ t := by
  intro t
  induction t with
  | zero =>
      simp only [traj, mInit, noise, bias, add_zero, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, smul_sub]
      have hn0 : (cfg.n0 : ℝ) ≠ 0 := by exact_mod_cast (show cfg.n0 ≠ 0 by omega)
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hn0, one_smul]
  | succ t ih =>
      rw [traj_succ_snd]
      simp only [noise, bias, drift]
      have h := ih
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      have hw := weights_sum cfg
      have hone : grad (traj cfg x0 g ξ (t + 1)).1 =
          (keep cfg + weightNear cfg + weightFar cfg) • grad (traj cfg x0 g ξ (t + 1)).1 := by
        rw [hw, one_smul]
      have hn : nearOf cfg (traj cfg x0 g ξ t) =
          leadNear cfg (traj cfg x0 g ξ (t + 1)).1 (traj cfg x0 g ξ t).1 := rfl
      have hf : farOf cfg (traj cfg x0 g ξ t) =
          leadFar cfg (traj cfg x0 g ξ (t + 1)).1 (traj cfg x0 g ξ t).1 := rfl
      rw [← hn, ← hf]
      nth_rewrite 1 [hone]
      module

end Defs

section Bias

variable {cfg : Config} {x0 : E} {g : E → Ω → E} {grad : E → E}

omit [InnerProductSpace ℝ E] in
lemma stepTo_move [NormedSpace ℝ E] (hη : 0 ≤ cfg.η) (x m : E) : ‖stepTo cfg x m - x‖ ≤ cfg.η := by
  unfold stepTo
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hη,
    abs_norm]
  by_cases hm : ‖m‖ = 0
  · rw [hm]; simpa using hη
  · rw [div_mul_cancel₀ _ hm]

lemma bias_bound {D : ℝ} (hk0 : 0 ≤ keep cfg) (hk1 : keep cfg < 1) (hη : 0 ≤ cfg.η)
    (hD : ∀ x x' : E, ‖x' - x‖ ≤ cfg.η → ‖drift cfg grad x x'‖ ≤ D) (ξ : ℕ → Ω) : ∀ t,
    ‖bias cfg x0 g grad ξ t‖ ≤ D / (1 - keep cfg) := by
  have h1 : 0 < 1 - keep cfg := by linarith
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x0 x0 (by simpa using hη))
  intro t
  induction t with
  | zero => simp only [bias, norm_zero]; positivity
  | succ t ih =>
      simp only [bias]
      have hmove : ‖(traj cfg x0 g ξ (t + 1)).1 - (traj cfg x0 g ξ t).1‖ ≤ cfg.η := by
        rw [traj_succ_fst]
        exact stepTo_move hη _ _
      calc ‖keep cfg • bias cfg x0 g grad ξ t + _‖
          ≤ keep cfg * ‖bias cfg x0 g grad ξ t‖ + D := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
            exact add_le_add le_rfl (hD _ _ hmove)
        _ ≤ keep cfg * (D / (1 - keep cfg)) + D := by gcongr
        _ = D / (1 - keep cfg) := by field_simp; ring

end Bias

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  (cfg : Config) (x0 : E) (g : E → Ω → E) (grad : E → E)

lemma measurable_stepTo : Measurable (fun z : E × E => stepTo cfg z.1 z.2) := by
  unfold stepTo
  fun_prop

lemma measurable_nearOf : Measurable (nearOf (E := E) cfg) := by
  have hs := measurable_stepTo (E := E) cfg
  have hx : Measurable (fun s : E × E × E => stepTo cfg s.1 s.2.2) :=
    hs.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  unfold nearOf leadNear
  exact hx.add ((hx.sub measurable_fst).const_smul _)

lemma measurable_farOf : Measurable (farOf (E := E) cfg) := by
  have hs := measurable_stepTo (E := E) cfg
  have hx : Measurable (fun s : E × E × E => stepTo cfg s.1 s.2.2) :=
    hs.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  unfold farOf leadFar
  exact hx.add ((hx.sub measurable_fst).const_smul _)

lemma measurable_traj (hg : Measurable (Function.uncurry g)) :
    ∀ t, Measurable (fun ξ : ℕ → Ω => traj cfg x0 g ξ t) := by
  have hs := measurable_stepTo (E := E) cfg
  intro t
  induction t with
  | zero =>
      simp only [traj, mInit]
      refine measurable_const.prodMk (measurable_const.prodMk ?_)
      refine Measurable.const_smul ?_ _
      refine Finset.measurable_sum _ fun i _ => ?_
      exact hg.comp (measurable_const.prodMk (measurable_pi_apply i))
  | succ t ih =>
      have hx : Measurable (fun ξ : ℕ → Ω => stepTo cfg (traj cfg x0 g ξ t).1 (traj cfg x0 g ξ t).2.2) :=
        hs.comp ((measurable_fst.comp ih).prodMk (measurable_snd.comp (measurable_snd.comp ih)))
      have hn : Measurable (fun ξ : ℕ → Ω => nearOf cfg (traj cfg x0 g ξ t)) :=
        (measurable_nearOf cfg).comp ih
      have hf : Measurable (fun ξ : ℕ → Ω => farOf cfg (traj cfg x0 g ξ t)) :=
        (measurable_farOf cfg).comp ih
      change Measurable (fun ξ : ℕ → Ω => (stepTo cfg (traj cfg x0 g ξ t).1 (traj cfg x0 g ξ t).2.2,
        (traj cfg x0 g ξ t).1, keep cfg • (traj cfg x0 g ξ t).2.2 +
          weightNear cfg • g (nearOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t)) +
          weightFar cfg • g (farOf cfg (traj cfg x0 g ξ t)) (ξ (cfg.n0 + 2 * t + 1))))
      refine hx.prodMk ((measurable_fst.comp ih).prodMk ?_)
      exact (((measurable_snd.comp (measurable_snd.comp ih)).const_smul _).add
        ((hg.comp (hn.prodMk (measurable_pi_apply _))).const_smul _)).add
        ((hg.comp (hf.prodMk (measurable_pi_apply _))).const_smul _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma traj_congr {ξ ξ' : ℕ → Ω} : ∀ t, (∀ i, i < cfg.n0 + 2 * t → ξ i = ξ' i) →
    traj cfg x0 g ξ t = traj cfg x0 g ξ' t := by
  intro t
  induction t with
  | zero =>
      intro h
      simp only [traj, mInit]
      congr 3
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [h i (by simpa using Finset.mem_range.mp hi)]
  | succ t ih =>
      intro h
      have h' := ih (fun i hi => h i (by omega))
      simp only [traj, h']
      rw [h (cfg.n0 + 2 * t) (by omega), h (cfg.n0 + 2 * t + 1) (by omega)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma noise_congr {ξ ξ' : ℕ → Ω} : ∀ t, (∀ i, i < cfg.n0 + 2 * t → ξ i = ξ' i) →
    noise cfg x0 g grad ξ t = noise cfg x0 g grad ξ' t := by
  intro t
  induction t with
  | zero =>
      intro h
      simp only [noise]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [h i (by simpa using Finset.mem_range.mp hi)]
  | succ t ih =>
      intro h
      simp only [noise]
      rw [ih (fun i hi => h i (by omega)), traj_congr cfg x0 g t (fun i hi => h i (by omega)),
        h (cfg.n0 + 2 * t) (by omega), h (cfg.n0 + 2 * t + 1) (by omega)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma halfNoise_congr {ξ ξ' : ℕ → Ω} (t : ℕ) (h : ∀ i, i < cfg.n0 + 2 * t + 1 → ξ i = ξ' i) :
    halfNoise cfg x0 g grad ξ t = halfNoise cfg x0 g grad ξ' t := by
  simp only [halfNoise]
  rw [noise_congr cfg x0 g grad t (fun i hi => h i (by omega)),
    traj_congr cfg x0 g t (fun i hi => h i (by omega)), h (cfg.n0 + 2 * t) (by omega)]

end Measurable

section NoiseProcess

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω]
variable {g : E → Ω → E} {grad : E → E} {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : ℝ}
  (cfg : Config) (x0 : E)

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma measurable_noise (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) :
    ∀ t, Measurable (fun ξ : ℕ → Ω => noise cfg x0 g grad ξ t) := by
  intro t
  induction t with
  | zero =>
      simp only [noise]
      refine Measurable.const_smul (Finset.measurable_sum _ fun i _ => ?_) _
      exact (O.meas.comp (measurable_const.prodMk (measurable_pi_apply i))).sub measurable_const
  | succ t ih =>
      simp only [noise]
      have hn := (measurable_nearOf cfg).comp (measurable_traj cfg x0 g O.meas t)
      have hf := (measurable_farOf cfg).comp (measurable_traj cfg x0 g O.meas t)
      exact ((ih.const_smul _).add (((O.meas.comp (hn.prodMk (measurable_pi_apply _))).sub
        (hgrad.measurable.comp hn)).const_smul _)).add
        (((O.meas.comp (hf.prodMk (measurable_pi_apply _))).sub
        (hgrad.measurable.comp hf)).const_smul _)

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma measurable_halfNoise (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => halfNoise cfg x0 g grad ξ t) := by
  simp only [halfNoise]
  have hn := (measurable_nearOf cfg).comp (measurable_traj cfg x0 g O.meas t)
  exact ((measurable_noise cfg x0 O hgrad t).const_smul _).add
    (((O.meas.comp (hn.prodMk (measurable_pi_apply _))).sub (hgrad.measurable.comp hn)).const_smul _)

lemma halfNoise_moment (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (t : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖halfNoise cfg x0 g grad ξ t‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫⁻ ξ, ENNReal.ofReal (keep cfg ^ 2 * ‖noise cfg x0 g grad ξ t‖ ^ 2 + weightNear cfg ^ 2 * σ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  set Φ : ((E × E × E) × E) × Ω → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (‖keep cfg • s.1.2 + weightNear cfg • (g (nearOf cfg s.1.1) s.2 - grad (nearOf cfg s.1.1))‖ ^ 2)
  have hfun : (fun ξ => ENNReal.ofReal (‖halfNoise cfg x0 g grad ξ t‖ ^ 2)) =
      fun ξ => Φ ((traj cfg x0 g ξ t, noise cfg x0 g grad ξ t), ξ (cfg.n0 + 2 * t)) := by
    funext ξ; simp only [Φ, halfNoise]
  rw [hfun]
  have hw := measurable_nearOf (E := E) cfg
  have hΦ : Measurable Φ := by
    simp only [Φ]
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    have h11 : Measurable (fun s : ((E × E × E) × E) × Ω => nearOf cfg s.1.1) :=
      hw.comp (measurable_fst.comp measurable_fst)
    exact ((measurable_snd.comp measurable_fst).const_smul _).add
      (((O.meas.comp (h11.prodMk measurable_snd)).sub (hgrad.measurable.comp h11)).const_smul _)
  rw [OracleTemplate.HessianNcsc.fresh_lintegral μ (cfg.n0 + 2 * t)
    (fun ξ => (traj cfg x0 g ξ t, noise cfg x0 g grad ξ t))
    ((measurable_traj cfg x0 g O.meas t).prodMk (measurable_noise cfg x0 O hgrad t))
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq]
      exact ⟨traj_congr cfg x0 g t (fun i hi => h i (by omega)),
        noise_congr cfg x0 g grad t (fun i hi => h i (by omega))⟩) Φ hΦ]
  refine lintegral_mono fun ξ => ?_
  simp only [Φ]
  refine (inner_step O (keep cfg • noise cfg x0 g grad ξ t) (weightNear cfg)
    (nearOf cfg (traj cfg x0 g ξ t))).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma noise_succ_moment (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (t : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ (t + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫⁻ ξ, ENNReal.ofReal (keep cfg ^ 2 * ‖noise cfg x0 g grad ξ t‖ ^ 2 +
        (weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  set Φ : ((E × E × E) × E) × Ω → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (‖s.1.2 + weightFar cfg • (g (farOf cfg s.1.1) s.2 - grad (farOf cfg s.1.1))‖ ^ 2)
  have hfun : (fun ξ => ENNReal.ofReal (‖noise cfg x0 g grad ξ (t + 1)‖ ^ 2)) =
      fun ξ => Φ ((traj cfg x0 g ξ t, halfNoise cfg x0 g grad ξ t), ξ (cfg.n0 + 2 * t + 1)) := by
    funext ξ; simp only [Φ, noise, halfNoise]
  rw [hfun]
  have hw := measurable_farOf (E := E) cfg
  have hΦ : Measurable Φ := by
    simp only [Φ]
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    have h11 : Measurable (fun s : ((E × E × E) × E) × Ω => farOf cfg s.1.1) :=
      hw.comp (measurable_fst.comp measurable_fst)
    exact (measurable_snd.comp measurable_fst).add
      (((O.meas.comp (h11.prodMk measurable_snd)).sub (hgrad.measurable.comp h11)).const_smul _)
  rw [OracleTemplate.HessianNcsc.fresh_lintegral μ (cfg.n0 + 2 * t + 1)
    (fun ξ => (traj cfg x0 g ξ t, halfNoise cfg x0 g grad ξ t))
    ((measurable_traj cfg x0 g O.meas t).prodMk (measurable_halfNoise cfg x0 O hgrad t))
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq]
      exact ⟨traj_congr cfg x0 g t (fun i hi => h i (by omega)),
        halfNoise_congr cfg x0 g grad t h⟩) Φ hΦ]
  have hstep : ∀ ξ : ℕ → Ω, ∫⁻ ω, Φ ((traj cfg x0 g ξ t, halfNoise cfg x0 g grad ξ t), ω) ∂μ ≤
      ENNReal.ofReal (‖halfNoise cfg x0 g grad ξ t‖ ^ 2) + ENNReal.ofReal (weightFar cfg ^ 2 * σ ^ 2) := by
    intro ξ
    simp only [Φ]
    refine (inner_step O (halfNoise cfg x0 g grad ξ t) (weightFar cfg)
      (farOf cfg (traj cfg x0 g ξ t))).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (lintegral_mono hstep).trans ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  refine (add_le_add (halfNoise_moment cfg x0 O hgrad t) le_rfl).trans (le_of_eq ?_)
  have hsplit : ∀ ξ : ℕ → Ω, ENNReal.ofReal (keep cfg ^ 2 * ‖noise cfg x0 g grad ξ t‖ ^ 2 +
      (weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) =
      ENNReal.ofReal (keep cfg ^ 2 * ‖noise cfg x0 g grad ξ t‖ ^ 2 + weightNear cfg ^ 2 * σ ^ 2) +
        ENNReal.ofReal (weightFar cfg ^ 2 * σ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma noise_moment (O : OracleHyp g grad μ σ) (hgrad : Continuous grad)
    (hn : 1 ≤ cfg.n0) (hγ : 0 < cfg.γ) (hγ1 : cfg.γ ≤ 1) : ∀ t,
    ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) := by
  have hn0 : (0 : ℝ) < cfg.n0 := by exact_mod_cast hn
  intro t
  induction t with
  | zero =>
      have e : ∀ ξ : ℕ → Ω, ‖noise cfg x0 g grad ξ 0‖ ^ 2 =
          (1 / (cfg.n0 : ℝ)) ^ 2 * ‖∑ i ∈ Finset.range cfg.n0, (g x0 (ξ i) - grad x0)‖ ^ 2 := by
        intro ξ
        simp only [noise, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      simp_rw [e]
      simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / (cfg.n0 : ℝ)) ^ 2)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal ((1 / (cfg.n0 : ℝ)) ^ 2) *
            ∫⁻ ξ, ENNReal.ofReal (‖∑ i ∈ Finset.range cfg.n0, (g x0 (ξ i) - grad x0)‖ ^ 2)
              ∂(Measure.infinitePi fun _ : ℕ => μ)
          ≤ ENNReal.ofReal ((1 / (cfg.n0 : ℝ)) ^ 2) * ENNReal.ofReal (cfg.n0 * σ ^ 2) := by
            gcongr; exact init_partial_moment x0 O cfg.n0
        _ = ENNReal.ofReal (σ ^ 2 / cfg.n0) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
        _ ≤ ENNReal.ofReal (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) :=
            ENNReal.ofReal_le_ofReal (by have := sq_nonneg σ; nlinarith)
  | succ t ih =>
      refine (noise_succ_moment cfg x0 O hgrad t).trans ?_
      have hsplit : ∀ ξ, ENNReal.ofReal (keep cfg ^ 2 * ‖noise cfg x0 g grad ξ t‖ ^ 2 +
          (weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) =
          ENNReal.ofReal (keep cfg ^ 2) * ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) +
            ENNReal.ofReal ((weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) := by
        intro ξ
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp_rw [hsplit]
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (keep cfg ^ 2) * ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2)
            ∂(Measure.infinitePi fun _ : ℕ => μ) +
            ENNReal.ofReal ((weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2)
          ≤ ENNReal.ofReal (keep cfg ^ 2) * ENNReal.ofReal (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) +
              ENNReal.ofReal ((weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) := by gcongr
        _ = ENNReal.ofReal (keep cfg ^ 2 * (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) +
              (weightNear cfg ^ 2 + weightFar cfg ^ 2) * σ ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            have hA : 0 ≤ σ ^ 2 / cfg.n0 := by positivity
            have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
            have hk0 : 0 ≤ keep cfg := by
              unfold keep; nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) (by linarith : (0 : ℝ) ≤ 2 - cfg.γ)]
            have hk1 : keep cfg ≤ 1 - cfg.γ := by
              unfold keep; nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) hγ.le]
            have hksq : keep cfg ^ 2 ≤ 1 - cfg.γ := by nlinarith
            have h1 : keep cfg ^ 2 ≤ 1 := by linarith
            have hw : weightNear cfg ^ 2 + weightFar cfg ^ 2 ≤ 5 * cfg.γ ^ 2 := by
              unfold weightNear weightFar
              have h2 : (cfg.γ * (2 - cfg.γ)) ^ 2 ≤ 4 * cfg.γ ^ 2 := by
                have : (2 - cfg.γ) ^ 2 ≤ 4 := by nlinarith
                calc (cfg.γ * (2 - cfg.γ)) ^ 2 = cfg.γ ^ 2 * (2 - cfg.γ) ^ 2 := by ring
                  _ ≤ cfg.γ ^ 2 * 4 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
                  _ = _ := by ring
              have h3 : (-(cfg.γ * (1 - cfg.γ) / 2)) ^ 2 ≤ cfg.γ ^ 2 := by
                have : (1 - cfg.γ) ^ 2 ≤ 1 := by nlinarith
                calc (-(cfg.γ * (1 - cfg.γ) / 2)) ^ 2 = cfg.γ ^ 2 * ((1 - cfg.γ) ^ 2 / 4) := by ring
                  _ ≤ cfg.γ ^ 2 * 1 := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
                  _ = _ := by ring
              linarith
            have h2 : keep cfg ^ 2 * (5 * cfg.γ) + (weightNear cfg ^ 2 + weightFar cfg ^ 2) ≤ 5 * cfg.γ := by
              nlinarith [mul_le_mul_of_nonneg_right hksq (by positivity : (0 : ℝ) ≤ 5 * cfg.γ)]
            nlinarith [mul_le_mul_of_nonneg_right h1 hA, mul_le_mul_of_nonneg_right h2 hs]

end NoiseProcess

end OracleTemplate.LookaheadMomentum
