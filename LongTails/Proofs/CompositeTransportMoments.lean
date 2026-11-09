import LongTails.Proofs.CompositeTransportRun
import LongTails.Proofs.CompositeTransportStep
import LongTails.Proofs.HessianNcscProcess

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CompositeTransport

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Defs

variable (cfg : Config) (x0 : E) (g : E → Ω → E) (grad : E → E) (prox : ℝ → E → E → E)
  (ξ : ℕ → Ω)

noncomputable def wpt (t : ℕ) : E :=
  lead cfg (traj cfg x0 g prox ξ (t + 1)).1 (traj cfg x0 g prox ξ t).1

noncomputable def noise : ℕ → E
  | 0 => (1 / (cfg.n0 : ℝ)) • ∑ i ∈ Finset.range cfg.n0, (g x0 (ξ i) - grad x0)
  | t + 1 => (1 - cfg.α) • noise t +
      cfg.α • (g (wpt cfg x0 g prox ξ t) (ξ (cfg.n0 + 2 * t + 1)) - grad (wpt cfg x0 g prox ξ t))

noncomputable def bias : ℕ → E
  | 0 => 0
  | t + 1 => (1 - cfg.α) • bias t +
      ((1 - cfg.α) • (grad (traj cfg x0 g prox ξ t).1 - grad (traj cfg x0 g prox ξ (t + 1)).1) +
        cfg.α • (grad (wpt cfg x0 g prox ξ t) - grad (traj cfg x0 g prox ξ (t + 1)).1))

lemma traj_succ_snd (t : ℕ) : (traj cfg x0 g prox ξ (t + 1)).2.2 =
    (1 - cfg.α) • (traj cfg x0 g prox ξ t).2.2 + cfg.α • g (wpt cfg x0 g prox ξ t) (ξ (cfg.n0 + 2 * t + 1)) := rfl

lemma traj_succ_mid (t : ℕ) : (traj cfg x0 g prox ξ (t + 1)).2.1 = (traj cfg x0 g prox ξ t).1 := rfl

lemma traj_succ_fst (t : ℕ) : (traj cfg x0 g prox ξ (t + 1)).1 =
    capStep cfg (traj cfg x0 g prox ξ t).1 (prox cfg.γ (traj cfg x0 g prox ξ t).1 (traj cfg x0 g prox ξ t).2.2) := rfl

lemma error_split (hn : 1 ≤ cfg.n0) : ∀ t,
    (traj cfg x0 g prox ξ t).2.2 - grad (traj cfg x0 g prox ξ t).1 =
      noise cfg x0 g grad prox ξ t + bias cfg x0 g grad prox ξ t := by
  intro t
  induction t with
  | zero =>
      simp only [traj, mInit, noise, bias, add_zero, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, smul_sub]
      have hn0 : (cfg.n0 : ℝ) ≠ 0 := by exact_mod_cast (show cfg.n0 ≠ 0 by omega)
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hn0, one_smul]
  | succ t ih =>
      rw [traj_succ_snd]
      simp only [noise, bias]
      have h := ih
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      module

end Defs

section Bias

variable {cfg : Config} {x0 : E} {g : E → Ω → E} {grad : E → E} {prox : ℝ → E → E → E}
  {hess : E → E →L[ℝ] E} {ρ : ℝ}

lemma bias_bound (hρ : 0 ≤ ρ) (hd : ∀ x, HasFDerivAt grad (hess x) x)
    (hl : ∀ x y, ‖hess x - hess y‖ ≤ ρ * ‖x - y‖) (hα : 0 < cfg.α) (hα1 : cfg.α ≤ 1)
    (hγ : 0 < cfg.γ) (hε : 0 < cfg.ε) (ξ : ℕ → Ω) : ∀ t,
    ‖bias cfg x0 g grad prox ξ t‖ ≤ ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2 := by
  intro t
  induction t with
  | zero => simp [bias]; positivity
  | succ t ih =>
      simp only [bias]
      have hmove : ‖(traj cfg x0 g prox ξ (t + 1)).1 - (traj cfg x0 g prox ξ t).1‖ ≤ 2 * cfg.γ * cfg.ε := by
        rw [traj_succ_fst]
        simp only [capStep, add_sub_cancel_left]
        exact capped_move_le hγ hε _ _
      have hb := transport_bias hρ hd hl hα hα1 (traj cfg x0 g prox ξ t).1 (traj cfg x0 g prox ξ (t + 1)).1
      have hb' : ‖(1 - cfg.α) • (grad (traj cfg x0 g prox ξ t).1 - grad (traj cfg x0 g prox ξ (t + 1)).1) +
          cfg.α • (grad (wpt cfg x0 g prox ξ t) - grad (traj cfg x0 g prox ξ (t + 1)).1)‖ ≤
          ρ / cfg.α * (2 * cfg.γ * cfg.ε) ^ 2 := by
        refine hb.trans ?_
        gcongr
      have h1α : 0 ≤ 1 - cfg.α := by linarith
      calc ‖(1 - cfg.α) • bias cfg x0 g grad prox ξ t + _‖
          ≤ (1 - cfg.α) * ‖bias cfg x0 g grad prox ξ t‖ + ρ / cfg.α * (2 * cfg.γ * cfg.ε) ^ 2 := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h1α]
            exact add_le_add le_rfl hb'
        _ ≤ (1 - cfg.α) * (ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2) + ρ / cfg.α * (2 * cfg.γ * cfg.ε) ^ 2 := by
            gcongr
        _ = ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2 := by field_simp; ring

end Bias

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  (cfg : Config) (x0 : E) (g : E → Ω → E) (grad : E → E) (prox : ℝ → E → E → E)

lemma measurable_capStep : Measurable (fun z : E × E => capStep cfg z.1 z.2) := by
  unfold capStep
  fun_prop

lemma measurable_lead' : Measurable (fun z : E × E => lead cfg z.1 z.2) := by
  unfold lead
  fun_prop

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_proxγ (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) :
    Measurable (fun z : E × E => prox cfg.γ z.1 z.2) := by
  have : (fun z : E × E => prox cfg.γ z.1 z.2) =
      (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0) ∘ (fun z => (cfg.γ, z.1, z.2)) := by
    funext z; simp [hγ]
  rw [this]
  exact hprox.comp (by fun_prop)

lemma measurable_traj (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0))
    (hg : Measurable (Function.uncurry g)) : ∀ t, Measurable (fun ξ : ℕ → Ω => traj cfg x0 g prox ξ t) := by
  have hp := measurable_proxγ cfg prox hγ hprox
  have hc := measurable_capStep (E := E) cfg
  have hl := measurable_lead' (E := E) cfg
  intro t
  induction t with
  | zero =>
      simp only [traj, mInit]
      refine measurable_const.prodMk (measurable_const.prodMk ?_)
      refine Measurable.const_smul ?_ _
      refine Finset.measurable_sum _ fun i _ => ?_
      exact hg.comp (measurable_const.prodMk (measurable_pi_apply i))
  | succ t ih =>
      have hx : Measurable (fun ξ : ℕ → Ω => capStep cfg (traj cfg x0 g prox ξ t).1
          (prox cfg.γ (traj cfg x0 g prox ξ t).1 (traj cfg x0 g prox ξ t).2.2)) :=
        hc.comp ((measurable_fst.comp ih).prodMk (hp.comp ((measurable_fst.comp ih).prodMk
          (measurable_snd.comp (measurable_snd.comp ih)))))
      have hw : Measurable (fun ξ : ℕ → Ω => lead cfg (capStep cfg (traj cfg x0 g prox ξ t).1
          (prox cfg.γ (traj cfg x0 g prox ξ t).1 (traj cfg x0 g prox ξ t).2.2)) (traj cfg x0 g prox ξ t).1) :=
        hl.comp (hx.prodMk (measurable_fst.comp ih))
      simp only [traj]
      refine hx.prodMk ((measurable_fst.comp ih).prodMk ?_)
      exact ((measurable_snd.comp (measurable_snd.comp ih)).const_smul _).add
        ((hg.comp (hw.prodMk (measurable_pi_apply _))).const_smul _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma traj_congr {ξ ξ' : ℕ → Ω} : ∀ t, (∀ i, i < cfg.n0 + 2 * t → ξ i = ξ' i) →
    traj cfg x0 g prox ξ t = traj cfg x0 g prox ξ' t := by
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
      rw [h (cfg.n0 + 2 * t + 1) (by omega)]

end Measurable

section Noise

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω]

structure OracleHyp (g : E → Ω → E) (grad : E → E) (μ : Measure Ω) (σ : ℝ) : Prop where
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) μ
  mean : ∀ x, ∫ ω, g x ω ∂μ = grad x
  int2 : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ 2) μ
  var : ∀ x, ∫ ω, ‖g x ω - grad x‖ ^ 2 ∂μ ≤ σ ^ 2

variable {g : E → Ω → E} {grad : E → E} {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma inner_step (O : OracleHyp g grad μ σ) (a : E) (c : ℝ) (w : E) :
    ∫⁻ ω, ENNReal.ofReal (‖a + c • (g w ω - grad w)‖ ^ 2) ∂μ ≤ ENNReal.ofReal (‖a‖ ^ 2 + c ^ 2 * σ ^ 2) := by
  set N : Ω → E := fun ω => c • (g w ω - grad w)
  have hN : Integrable N μ := Integrable.smul c ((O.int w).sub (integrable_const (grad w)))
  have hN0 : ∫ ω, N ω ∂μ = 0 := by
    simp only [N]
    rw [integral_smul, integral_sub (O.int w) (integrable_const _), O.mean w, integral_const]
    simp
  have hNn : ∀ ω, ‖N ω‖ ^ 2 = c ^ 2 * ‖g w ω - grad w‖ ^ 2 := by
    intro ω; simp only [N, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hN2 : Integrable (fun ω => ‖N ω‖ ^ 2) μ := by
    simp_rw [hNn]; exact (O.int2 w).const_mul _
  have hsq := OracleTemplate.HessianNcsc.sq_add_mean_zero μ a N hN hN0 hN2
  have hint : Integrable (fun ω => ‖a + N ω‖ ^ 2) μ := by
    refine Integrable.mono' (((integrable_const (2 * ‖a‖ ^ 2)).add (hN2.const_mul 2))) ?_ ?_
    · exact (((continuous_const.add continuous_id).norm.pow 2).comp_aestronglyMeasurable
        hN.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (N ω)) 2
      nlinarith [norm_nonneg a, norm_nonneg (N ω), sq_nonneg (‖a‖ - ‖N ω‖)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  change ∫ ω, ‖a + N ω‖ ^ 2 ∂μ ≤ _
  rw [hsq]
  simp_rw [hNn]
  rw [integral_const_mul]
  have := O.var w
  nlinarith [sq_nonneg c]

end Noise

section NoiseProcess

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω]
variable {g : E → Ω → E} {grad : E → E} {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : ℝ}
  (cfg : Config) (x0 : E) (prox : ℝ → E → E → E)

noncomputable def wOf (s : E × E × E) : E :=
  lead cfg (capStep cfg s.1 (prox cfg.γ s.1 s.2.2)) s.1

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace Ω] in
lemma wpt_eq (ξ : ℕ → Ω) (t : ℕ) : wpt cfg x0 g prox ξ t = wOf cfg prox (traj cfg x0 g prox ξ t) := rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace Ω] in
lemma noise_congr {ξ ξ' : ℕ → Ω} : ∀ t, (∀ i, i < cfg.n0 + 2 * t → ξ i = ξ' i) →
    noise cfg x0 g grad prox ξ t = noise cfg x0 g grad prox ξ' t := by
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
      simp only [noise, wpt_eq]
      rw [ih (fun i hi => h i (by omega)), traj_congr cfg x0 g prox t (fun i hi => h i (by omega)),
        h (cfg.n0 + 2 * t + 1) (by omega)]

omit [CompleteSpace E] in
lemma measurable_wOf (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) :
    Measurable (wOf cfg prox) := by
  have hp := measurable_proxγ cfg prox hγ hprox
  have hc := measurable_capStep (E := E) cfg
  have hl := measurable_lead' (E := E) cfg
  unfold wOf
  exact hl.comp ((hc.comp (measurable_fst.prodMk (hp.comp (measurable_fst.prodMk
    (measurable_snd.comp measurable_snd))))).prodMk measurable_fst)

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma measurable_noise (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) :
    ∀ t, Measurable (fun ξ : ℕ → Ω => noise cfg x0 g grad prox ξ t) := by
  intro t
  induction t with
  | zero =>
      simp only [noise]
      refine Measurable.const_smul (Finset.measurable_sum _ fun i _ => ?_) _
      exact (O.meas.comp (measurable_const.prodMk (measurable_pi_apply i))).sub measurable_const
  | succ t ih =>
      simp only [noise, wpt_eq]
      have hw := (measurable_wOf cfg prox hγ hprox).comp (measurable_traj cfg x0 g prox hγ hprox O.meas t)
      exact (ih.const_smul _).add (((O.meas.comp (hw.prodMk (measurable_pi_apply _))).sub
        (hgrad.measurable.comp hw)).const_smul _)

lemma noise_succ_moment (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) (t : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ (t + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ∫⁻ ξ, ENNReal.ofReal ((1 - cfg.α) ^ 2 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 + cfg.α ^ 2 * σ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  set Φ : ((E × E × E) × E) × Ω → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (‖(1 - cfg.α) • s.1.2 + cfg.α • (g (wOf cfg prox s.1.1) s.2 - grad (wOf cfg prox s.1.1))‖ ^ 2)
  have hfun : (fun ξ => ENNReal.ofReal (‖noise cfg x0 g grad prox ξ (t + 1)‖ ^ 2)) =
      fun ξ => Φ ((traj cfg x0 g prox ξ t, noise cfg x0 g grad prox ξ t), ξ (cfg.n0 + 2 * t + 1)) := by
    funext ξ; simp only [Φ, noise, wpt_eq]
  rw [hfun]
  have hw := measurable_wOf cfg prox hγ hprox
  have hΦ : Measurable Φ := by
    simp only [Φ]
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    have h11 : Measurable (fun s : ((E × E × E) × E) × Ω => wOf cfg prox s.1.1) :=
      hw.comp (measurable_fst.comp measurable_fst)
    exact ((measurable_snd.comp measurable_fst).const_smul _).add
      (((O.meas.comp (h11.prodMk measurable_snd)).sub (hgrad.measurable.comp h11)).const_smul _)
  rw [OracleTemplate.HessianNcsc.fresh_lintegral μ (cfg.n0 + 2 * t + 1)
    (fun ξ => (traj cfg x0 g prox ξ t, noise cfg x0 g grad prox ξ t))
    ((measurable_traj cfg x0 g prox hγ hprox O.meas t).prodMk (measurable_noise cfg x0 prox O hgrad hγ hprox t))
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq]
      exact ⟨traj_congr cfg x0 g prox t (fun i hi => h i (by omega)),
        noise_congr cfg x0 prox t (fun i hi => h i (by omega))⟩) Φ hΦ]
  refine lintegral_mono fun ξ => ?_
  simp only [Φ]
  refine (inner_step O ((1 - cfg.α) • noise cfg x0 g grad prox ξ t) cfg.α
    (wOf cfg prox (traj cfg x0 g prox ξ t))).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma init_partial_moment (O : OracleHyp g grad μ σ) : ∀ j : ℕ,
    ∫⁻ ξ, ENNReal.ofReal (‖∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal (j * σ ^ 2) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hS : Measurable (fun ξ : ℕ → Ω => ∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0)) :=
        Finset.measurable_sum _ fun i _ => (O.meas.comp (measurable_const.prodMk (measurable_pi_apply i))).sub
          measurable_const
      set Φ : E × Ω → ℝ≥0∞ := fun s => ENNReal.ofReal (‖s.1 + (1 : ℝ) • (g x0 s.2 - grad x0)‖ ^ 2)
      have hfun : (fun ξ : ℕ → Ω => ENNReal.ofReal (‖∑ i ∈ Finset.range (j + 1), (g x0 (ξ i) - grad x0)‖ ^ 2)) =
          fun ξ => Φ (∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0), ξ j) := by
        funext ξ; simp only [Φ, Finset.sum_range_succ, one_smul]
      rw [hfun]
      have hΦ : Measurable Φ := by
        simp only [Φ, one_smul]
        exact ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm
          (measurable_fst.add ((O.meas.comp (measurable_const.prodMk measurable_snd)).sub measurable_const))) 2)
      rw [OracleTemplate.HessianNcsc.fresh_lintegral μ j _ hS (fun ξ ξ' h => Finset.sum_congr rfl
        fun i hi => by rw [h i (Finset.mem_range.mp hi)]) Φ hΦ]
      calc ∫⁻ ξ, ∫⁻ ω, Φ (∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0), ω) ∂μ ∂(Measure.infinitePi fun _ : ℕ => μ)
          ≤ ∫⁻ ξ, ENNReal.ofReal (‖∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0)‖ ^ 2) + ENNReal.ofReal (σ ^ 2)
              ∂(Measure.infinitePi fun _ : ℕ => μ) := by
            refine lintegral_mono fun ξ => ?_
            simp only [Φ]
            refine (inner_step O (∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0)) 1 x0).trans (le_of_eq ?_)
            rw [one_pow, one_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
        _ = ∫⁻ ξ, ENNReal.ofReal (‖∑ i ∈ Finset.range j, (g x0 (ξ i) - grad x0)‖ ^ 2)
              ∂(Measure.infinitePi fun _ : ℕ => μ) + ENNReal.ofReal (σ ^ 2) := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ENNReal.ofReal (j * σ ^ 2) + ENNReal.ofReal (σ ^ 2) := by gcongr
        _ = ENNReal.ofReal (((j + 1 : ℕ) : ℝ) * σ ^ 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; push_cast; ring_nf

lemma noise_moment (O : OracleHyp g grad μ σ) (hgrad : Continuous grad) (hγ : 0 < cfg.γ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0))
    (hn : 1 ≤ cfg.n0) (hα : 0 ≤ cfg.α) (hα1 : cfg.α ≤ 1) : ∀ t,
    ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal (σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) := by
  have hn0 : (0 : ℝ) < cfg.n0 := by exact_mod_cast hn
  intro t
  induction t with
  | zero =>
      have e : ∀ ξ : ℕ → Ω, ‖noise cfg x0 g grad prox ξ 0‖ ^ 2 =
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
        _ ≤ ENNReal.ofReal (σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) :=
            ENNReal.ofReal_le_ofReal (by have := sq_nonneg σ; nlinarith)
  | succ t ih =>
      refine (noise_succ_moment cfg x0 prox O hgrad hγ hprox t).trans ?_
      have hsplit : ∀ ξ, ENNReal.ofReal ((1 - cfg.α) ^ 2 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 + cfg.α ^ 2 * σ ^ 2) =
          ENNReal.ofReal ((1 - cfg.α) ^ 2) * ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) +
            ENNReal.ofReal (cfg.α ^ 2 * σ ^ 2) := by
        intro ξ
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp_rw [hsplit]
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal ((1 - cfg.α) ^ 2) * ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2)
            ∂(Measure.infinitePi fun _ : ℕ => μ) + ENNReal.ofReal (cfg.α ^ 2 * σ ^ 2)
          ≤ ENNReal.ofReal ((1 - cfg.α) ^ 2) * ENNReal.ofReal (σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) +
              ENNReal.ofReal (cfg.α ^ 2 * σ ^ 2) := by gcongr
        _ = ENNReal.ofReal ((1 - cfg.α) ^ 2 * (σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) + cfg.α ^ 2 * σ ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            have hA : 0 ≤ σ ^ 2 / cfg.n0 := by positivity
            have hs : 0 ≤ σ ^ 2 := sq_nonneg σ
            have h1 : (1 - cfg.α) ^ 2 ≤ 1 := by nlinarith
            have h2 : (1 - cfg.α) ^ 2 * cfg.α + cfg.α ^ 2 ≤ cfg.α := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right h1 hA, mul_le_mul_of_nonneg_right h2 hs]

end NoiseProcess

end OracleTemplate.CompositeTransport
