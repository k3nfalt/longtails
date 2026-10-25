import LongTails.Proofs.HeavyTailedSospForecastIntegration
import LongTails.Proofs.HeavyTailedHessianTransport
import LongTails.Proofs.GuardedGeneralizedGeometry

open MeasureTheory

namespace LongTails.Proofs.GuardedHessianNoise

lemma small_power_le_one_add_square {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p)
    (hp2 : p ≤ 2) : x ^ p ≤ 1 + x ^ 2 := by
  by_cases h : x ≤ 1
  · have hpow := Real.rpow_le_rpow hx h hp
    simp only [Real.one_rpow] at hpow
    nlinarith [sq_nonneg x]
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp2
    rw [Real.rpow_two] at hpow
    linarith

lemma scaled_power_le {x M p : ℝ} (hx : 0 ≤ x) (hM : 0 < M) (hp : 0 ≤ p)
    (hp2 : p ≤ 2) : x ^ p ≤ M ^ p + (M ^ p / M ^ 2) * x ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (small_power_le_one_add_square (div_nonneg hx hM.le) hp hp2)
    (Real.rpow_nonneg hM.le p)
  rw [Real.div_rpow hx hM.le] at h
  have hMp : M ^ p ≠ 0 := (Real.rpow_pos_of_pos hM p).ne'
  have he : M ^ p * (x ^ p / M ^ p) = x ^ p := by field_simp
  rw [he] at h
  convert h using 1
  field_simp

lemma moment_from_second {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {M C p : ℝ}
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hM : 0 < M)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (hi : Integrable (fun ω => X ω ^ 2) P)
    (hb : (∫ ω, X ω ^ 2 ∂P) ≤ C * M ^ 2) :
    Integrable (fun ω => X ω ^ p) P ∧
      (∫ ω, X ω ^ p ∂P) ≤ (1 + C) * M ^ p := by
  have hdom := (integrable_const (M ^ p)).add (hi.const_mul (M ^ p / M ^ 2))
  have hbound (ω : Ω) := scaled_power_le (hX0 ω) hM hp hp2
  have hpowi : Integrable (fun ω => X ω ^ p) P := hdom.mono'
    (hX.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hX0 ω) p)]
      exact hbound ω))
  refine ⟨hpowi, ?_⟩
  have h := integral_mono hpowi hdom hbound
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at h
  have hb' := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ M ^ p / M ^ 2 by positivity)
  have he : M ^ p / M ^ 2 * (C * M ^ 2) = C * M ^ p := by field_simp
  rw [he] at hb'
  nlinarith

lemma segment_centered_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (x v : E) (hsmall : L1 * ‖v‖ ≤ 1 / 4) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ‖fderiv ℝ g (x + t • v) v - (g (x + v) - g x)‖ ≤
      4 * (L0 + L1 * ‖g x‖) * ‖v‖ := by
  have hd : ‖x + t • v - x‖ ≤ ‖v‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hdiff := GuardedGeneralizedGeometry.short_gradient_difference hL0 hL1 hg hH
    x (x + t • v) ((mul_le_mul_of_nonneg_left hd hL1).trans hsmall)
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2 * (L0 + L1 * ‖g x‖) by positivity))
  have hgrowth := norm_le_norm_sub_add (g (x + t • v)) (g x)
  have hcurv : L0 + L1 * ‖g (x + t • v)‖ ≤ 2 * (L0 + L1 * ‖g x‖) := by
    have hmul := mul_le_mul_of_nonneg_left hdiff' hL1
    have hmul' := mul_le_mul_of_nonneg_left hgrowth hL1
    have hcap := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ L0 + L1 * ‖g x‖ by positivity)
    nlinarith [mul_nonneg hL1 (norm_nonneg (g x))]
  have ha := (fderiv ℝ g (x + t • v)).le_opNorm v
  have ha' := mul_le_mul_of_nonneg_right ((hH _).trans hcurv) (norm_nonneg v)
  have he := GuardedGeneralizedGeometry.short_gradient_difference hL0 hL1 hg hH
    x (x + v) (by simpa using hsmall)
  simp only [add_sub_cancel_left] at he
  exact (norm_sub_le _ _).trans (by linarith)

set_option maxHeartbeats 800000 in
lemma random_segment_transport {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : E → E} {L0 L1 q κ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hq : 1 ≤ q) (hq2 : q ≤ 2) (hκ : 0 ≤ κ)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (H : (E × E) → Ω → E) (hHm : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (H (y, v)) P)
    (hm : ∀ y v, (∫ ω, H (y, v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q) P)
    (x v : E) (hsmall : L1 * ‖v‖ ≤ 1 / 4)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ ω, ‖H (x + t • v, v) ω - fderiv ℝ g (x + t • v) v‖ ^ q ∂P) ≤ κ) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let F := fun w : ℝ × Ω => H (x + w.1 • v, v) w.2
    Integrable F Q ∧ (∫ w, F w ∂Q) = g (x + v) - g x ∧
      Integrable (fun w => ‖F w - (g (x + v) - g x)‖ ^ q) Q ∧
      (∫ w, ‖F w - (g (x + v) - g x)‖ ^ q ∂Q) ≤
        (4 * (L0 + L1 * ‖g x‖) * ‖v‖) ^ q + 6 * κ := by
  intro Q F
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  have hF : Measurable F := by
    exact hHm.comp (((measurable_const.add (measurable_fst.smul_const v)).prodMk
      measurable_const).prodMk measurable_snd)
  have hpoint : ∀ᵐ t ∂U, Integrable (fun ω => F (t, ω)) P ∧
      (∫ ω, F (t, ω) ∂P) = fderiv ℝ g (x + t • v) v ∧
      Integrable (fun ω => ‖F (t, ω) - fderiv ℝ g (x + t • v) v‖ ^ q) P ∧
      (∫ ω, ‖F (t, ω) - fderiv ℝ g (x + t • v) v‖ ^ q ∂P) ≤ (κ ^ q⁻¹) ^ q ∧
      ‖fderiv ℝ g (x + t • v) v - (g (x + v) - g x)‖ ≤
        4 * (L0 + L1 * ‖g x‖) * ‖v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    dsimp only [F]
    refine ⟨hi (x + t • v) v, hm (x + t • v) v, hpi (x + t • v) v, ?_,
      segment_centered_bound hL0 hL1 hg hH x v hsmall (Set.Ioc_subset_Icc_self ht)⟩
    rw [Real.rpow_inv_rpow hκ (by linarith : q ≠ 0)]
    exact hb t (Set.Ioc_subset_Icc_self ht)
  have hmoment := HeavyTailedHessianTransport.mixture_centered_moment (P := P) (Q := U)
    (g (x + v) - g x) hq hq2 hF hpoint
  have hmean := HeavyTailedHessianTransport.mixture_mean_of_centered_moment (P := P) (Q := U)
    (g (x + v) - g x) hq hF hmoment.1 (hpoint.mono fun _ ht => ht.2.1)
  refine ⟨hmean.1, ?_, hmoment.1, ?_⟩
  · rw [hmean.2]
    exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm.trans
      (HeavyTailedHessianTransport.derivative_segment_integral hg hD x v)
  · simpa only [Real.rpow_inv_rpow hκ (by linarith : q ≠ 0)] using hmoment.2

lemma affine_noise_product_moment {S Ω E : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {F : S × Ω → E} {G : S → ℝ} {M C p σ α : ℝ}
    (hF : Measurable F) (hG : Measurable G) (hG0 : ∀ s, 0 ≤ G s)
    (hM : 0 < M) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hGi : Integrable (fun s => G s ^ 2) μ)
    (hGb : (∫ s, G s ^ 2 ∂μ) ≤ C * M ^ 2)
    (hpi : ∀ s, Integrable (fun ω => ‖F (s, ω)‖ ^ p) P)
    (hb : ∀ s, (∫ ω, ‖F (s, ω)‖ ^ p ∂P) ≤ σ ^ p + α ^ p * G s ^ p)
    (hm : ∀ s, (∫ ω, F (s, ω) ∂P) = 0) (hα : 0 ≤ α) :
    Integrable F (μ.prod P) ∧ (∫ w, F w ∂μ.prod P) = 0 ∧
      Integrable (fun w => ‖F w‖ ^ p) (μ.prod P) ∧
      (∫ w, ‖F w‖ ^ p ∂μ.prod P) ≤ σ ^ p + (1 + C) * α ^ p * M ^ p := by
  have hGp := moment_from_second hG hG0 hM (by linarith : 0 ≤ p) hp2 hGi hGb
  have hbound := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (hF.norm.pow_const p).stronglyMeasurable
    (fun w => Real.rpow_nonneg (norm_nonneg (F w)) p)
    (Filter.Eventually.of_forall hpi)
    ((integrable_const (σ ^ p)).add (hGp.1.const_mul (α ^ p)))
    (Filter.Eventually.of_forall hb)
  have hmean := HeavyTailedHessianTransport.mixture_mean_of_centered_moment
    (P := P) (Q := μ) (0 : E) hp hF (by simpa using hbound.1)
    (Filter.Eventually.of_forall hm)
  refine ⟨hmean.1, ?_, hbound.1, ?_⟩
  · simpa using hmean.2
  · have hmul := mul_le_mul_of_nonneg_left hGp.2 (Real.rpow_nonneg hα p)
    have hh := hbound.2
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) (hGp.1.const_mul _), integral_const_mul,
      integral_const, probReal_univ, one_smul] at hh
    nlinarith

lemma prefix_predictable_inner_zero {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (v : (Fin n → Ω) → E) (e : (Fin n → Ω) → Ω → E)
    (hv : Measurable v) (he : Measurable (Function.uncurry e))
    (hi : ∀ η, Integrable (e η) P) (hz : ∀ η, (∫ ω, e η ω ∂P) = 0)
    (hjoint : Integrable (fun ξ : ℕ → Ω =>
      inner ℝ (v (fun i => ξ i)) (e (fun i => ξ i) (ξ n)))
      (Measure.infinitePi fun _ : ℕ => P)) :
    (∫ ξ : ℕ → Ω, inner ℝ (v (fun i => ξ i)) (e (fun i => ξ i) (ξ n))
      ∂Measure.infinitePi (fun _ : ℕ => P)) = 0 := by
  let F := fun z : (Fin n → Ω) × Ω => inner ℝ (v z.1) (e z.1 z.2)
  have hF : Measurable F := (hv.comp measurable_fst).inner he
  have hp := HeavyTailedSospForecastIntegration.prefix_current_preserving P n
  have hFi : Integrable F ((Measure.pi fun _ : Fin n => P).prod P) :=
    (hp.integrable_comp hF.aestronglyMeasurable).mp hjoint
  have hem := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at hem
  change (∫ ξ : ℕ → Ω, F ((fun i => ξ i), ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) = 0
  rw [← hem, integral_prod _ hFi]
  have hf (η : Fin n → Ω) : (∫ ω, F (η, ω) ∂P) = 0 := by
    dsimp only [F]
    rw [integral_inner (hi η), hz η, inner_zero_right]
  simp only [hf, integral_zero]

lemma prefix_martingale_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (w : (k : ℕ) → (Fin k → Ω) → E) (e : (k : ℕ) → (Fin k → Ω) → Ω → E)
    (hw : ∀ k, Measurable (w k)) (he : ∀ k, Measurable (Function.uncurry (e k)))
    (hi : ∀ k η, Integrable (e k η) P) (hz : ∀ k η, (∫ ω, e k η ω ∂P) = 0)
    (hep : ∀ k, Integrable (fun ξ : ℕ → Ω => ‖e k (fun i => ξ i) (ξ k)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P))
    (hinit : ∀ ξ : ℕ → Ω, w 0 (fun i => ξ i) = 0)
    (hadd : ∀ k (ξ : ℕ → Ω), w (k + 1) (fun i => ξ i) =
      w k (fun i => ξ i) + e k (fun i => ξ i) (ξ k)) (n : ℕ) :
    (∫ ξ : ℕ → Ω, ‖w n (fun i => ξ i)‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      6 * ∑ k ∈ Finset.range n, ∫ ξ : ℕ → Ω, ‖e k (fun i => ξ i) (ξ k)‖ ^ p
        ∂Measure.infinitePi (fun _ : ℕ => P) := by
  let X := fun k (ξ : ℕ → Ω) => w k (fun i => ξ i)
  let Z := fun k (ξ : ℕ → Ω) => e k (fun i => ξ i) (ξ k)
  have hX (k : ℕ) : Measurable (X k) := (hw k).comp (by fun_prop)
  have hZ (k : ℕ) : Measurable (Z k) :=
    (he k).comp (f := fun ξ : ℕ → Ω => ((fun i : Fin k => ξ i), ξ k)) (by fun_prop)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hXp (k : ℕ) : Integrable (fun ξ => ‖X k ξ‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) := by
    induction k with
    | zero => simpa only [X, hinit, norm_zero, Real.zero_rpow hp0.ne'] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : ℕ → Ω => (0 : ℝ))
          (Measure.infinitePi fun _ : ℕ => P))
    | succ k ih =>
        simpa only [X, hadd] using HeavyTailedMomentBounds.integrable_norm_sum_rpow hp0
          (hX k).aestronglyMeasurable (hZ k).aestronglyMeasurable ih (hep k)
  have hlin (k : ℕ) := HeavyTailedMomentBounds.moment_linear_term_integrable hp hp2
    (hX k) (hZ k) (hXp k) (hep k)
  apply HeavyTailedMomentBounds.process_moment_bound hp hp2 hXp hep hlin _ hinit hadd n
  intro k
  let v := fun η : Fin k → Ω => (p * ‖w k η‖ ^ (p - 1)) • (‖w k η‖⁻¹ • w k η)
  have hv : Measurable v := by dsimp [v]; fun_prop
  have hh := prefix_predictable_inner_zero P k v (e k) hv (he k) (hi k) (hz k) (by
    simpa only [v, real_inner_smul_left] using hlin k)
  simpa only [v, real_inner_smul_left] using hh

lemma transport_moment_scale {a σ α U η H Z q : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hU : 0 ≤ U)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hq : 0 ≤ q) (hq2 : q ≤ 2)
    (haH : a ≤ H * Z) (hσH : σ ≤ H * Z) (hαH : α * U ≤ 2 * (H * Z)) :
    (4 * a * η) ^ q + 6 * (σ ^ q + α ^ q * U ^ q) * η ^ q ≤
      64 * (H * η) ^ q * Z ^ q := by
  have htwo : (2 : ℝ) ^ q ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 4 := by norm_num
  have hfour : (4 : ℝ) ^ q ≤ 16 := by
    calc
      _ ≤ (4 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 16 := by norm_num
  have hcurv : (4 * a * η) ^ q ≤ 16 * (H * η) ^ q * Z ^ q := by
    calc
      _ ≤ (4 * (H * η) * Z) ^ q := Real.rpow_le_rpow (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_right haH hη]) hq
      _ = (4 : ℝ) ^ q * (H * η) ^ q * Z ^ q := by
        rw [Real.mul_rpow (by positivity : 0 ≤ 4 * (H * η)) hZ,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hH hη)]
      _ ≤ _ := by gcongr
  have hs := Real.rpow_le_rpow hσ hσH hq
  have halpha : (α * U) ^ q ≤ 4 * (H * Z) ^ q := by
    calc
      _ ≤ (2 * (H * Z)) ^ q := Real.rpow_le_rpow (mul_nonneg hα hU) hαH hq
      _ = (2 : ℝ) ^ q * (H * Z) ^ q := Real.mul_rpow (by norm_num) (mul_nonneg hH hZ)
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (mul_nonneg hH hZ) q)
  have hn : σ ^ q + α ^ q * U ^ q ≤ 5 * (H * Z) ^ q := by
    rw [← Real.mul_rpow hα hU]
    linarith
  have hnη := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hη q)
  have heq : 5 * (H * Z) ^ q * η ^ q = 5 * (H * η) ^ q * Z ^ q := by
    rw [Real.mul_rpow hH hZ, Real.mul_rpow hH hη]
    ring
  rw [heq] at hnη
  nlinarith [mul_nonneg (Real.rpow_nonneg (mul_nonneg hH hη) q) (Real.rpow_nonneg hZ q)]

lemma max_scaled_power_moment {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {G : S → ℝ} {M C p : ℝ}
    (hG : Measurable G) (hG0 : ∀ s, 0 ≤ G s) (hM : 0 < M)
    (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hGi : Integrable (fun s => G s ^ 2) μ)
    (hGb : (∫ s, G s ^ 2 ∂μ) ≤ C * M ^ 2) :
    Integrable (fun s => (max (G s / M) 1) ^ p) μ ∧
      (∫ s, (max (G s / M) 1) ^ p ∂μ) ≤ 2 + C := by
  have hgp := moment_from_second hG hG0 hM hp hp2 hGi hGb
  have hden : 0 < M ^ p := Real.rpow_pos_of_pos hM p
  have hbound (s : S) : (max (G s / M) 1) ^ p ≤ 1 + G s ^ p / M ^ p := by
    by_cases hs : G s / M ≤ 1
    · rw [max_eq_right hs, Real.one_rpow]
      exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg (hG0 s) p) hden.le)
    · rw [max_eq_left (le_of_not_ge hs), Real.div_rpow (hG0 s) hM.le]
      linarith
  have hfm : Measurable (fun s => (max (G s / M) 1) ^ p) := by fun_prop
  have hbi := (integrable_const (1 : ℝ)).add (hgp.1.div_const (M ^ p))
  have hfi : Integrable (fun s => (max (G s / M) 1) ^ p) μ := hbi.mono'
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_trans (by norm_num) (le_max_right _ _)) p)]
      exact hbound s))
  refine ⟨hfi, ?_⟩
  have hh := integral_mono hfi hbi hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hgp.1.div_const _), integral_const,
    probReal_univ, one_smul, integral_div] at hh
  have hr : (∫ s, G s ^ p ∂μ) / M ^ p ≤ 1 + C := (div_le_iff₀ hden).mpr hgp.2
  linarith

lemma affine_random_segment_transport {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : E → E} {L0 L1 q σ α M η K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M) (hη : 0 ≤ η)
    (hK : L0 + L1 * M + σ + α * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (H : (E × E) → Ω → E) (hHm : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (H (y, v)) P)
    (hm : ∀ y v, (∫ ω, H (y, v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q) P)
    (hb : ∀ y v, (∫ ω, ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q ∂P) ≤
      (σ ^ q + α ^ q * ‖g y‖ ^ q) * ‖v‖ ^ q)
    (x v : E) (hv : ‖v‖ ≤ η) (hsmall : L1 * η ≤ 1 / 4) (hbase : L0 * η ≤ M / 4) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let F := fun w : ℝ × Ω => H (x + w.1 • v, v) w.2
    Integrable F Q ∧ (∫ w, F w ∂Q) = g (x + v) - g x ∧
      Integrable (fun w => ‖F w - (g (x + v) - g x)‖ ^ q) Q ∧
      (∫ w, ‖F w - (g (x + v) - g x)‖ ^ q ∂Q) ≤
        64 * (K * η) ^ q * (max (‖g x‖ / M) 1) ^ q := by
  let Z := max (‖g x‖ / M) 1
  let U := 2 * M * Z
  let κ := (σ ^ q + α ^ q * U ^ q) * η ^ q
  have hZ1 : 1 ≤ Z := le_max_right _ _
  have hZ0 : 0 ≤ Z := le_trans (by norm_num) hZ1
  have hGM : ‖g x‖ ≤ M * Z := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (‖g x‖ / M) 1) hM.le
    rw [div_mul_cancel₀ _ hM.ne'] at hh
    exact hh.trans_eq (mul_comm Z M)
  have hMM : M ≤ M * Z := by nlinarith
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hK0 : 0 ≤ K := by nlinarith [mul_nonneg hL1 hM.le, mul_nonneg hα hM.le]
  have hA : L0 + L1 * ‖g x‖ ≤ K * Z := by
    have hh := mul_le_mul_of_nonneg_left hGM hL1
    have hL : L0 + L1 * M ≤ K := by nlinarith [mul_nonneg hα hM.le]
    have hLZ := mul_le_mul_of_nonneg_right hL hZ0
    have hL0Z := mul_le_mul_of_nonneg_left hZ1 hL0
    nlinarith
  have hσK : σ ≤ K * Z := by
    have hh : σ ≤ K := by nlinarith [mul_nonneg hL1 hM.le, mul_nonneg hα hM.le]
    exact hh.trans (le_mul_of_one_le_right hK0 hZ1)
  have hαK : α * U ≤ 2 * (K * Z) := by
    have hh : α * M ≤ K := by nlinarith [mul_nonneg hL1 hM.le]
    have hhz := mul_le_mul_of_nonneg_right hh hZ0
    dsimp [U]
    nlinarith
  have hh := random_segment_transport hL0 hL1 hq hq2
    (by dsimp [κ]; positivity) hg hD hH H hHm hi hm hpi x v
    ((mul_le_mul_of_nonneg_left hv hL1).trans hsmall) (κ := κ) (by
      intro t ht
      have hd : ‖x + t • v - x‖ ≤ η := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hv
      have hseg := GuardedGeneralizedGeometry.short_gradient_growth hL0 hL1 hg hH
        x (x + t • v) hd hsmall hbase
      have hsegU : ‖g (x + t • v)‖ ≤ U := by
        dsimp [U]
        nlinarith [max_le hGM hMM]
      apply (hb _ _).trans
      dsimp [κ]
      gcongr)
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.trans ?_⟩
  have hcurv : (4 * (L0 + L1 * ‖g x‖) * ‖v‖) ^ q ≤
      (4 * (L0 + L1 * ‖g x‖) * η) ^ q := by gcongr
  have hscale := transport_moment_scale
    (by positivity : 0 ≤ L0 + L1 * ‖g x‖) hσ hα hU hη hK0 hZ0
    (by linarith : 0 ≤ q) hq2 hA hσK hαK
  dsimp only [κ] at *
  change _ ≤ 64 * (K * η) ^ q * Z ^ q
  nlinarith

lemma scaled_noise_product_moment {S Ω E : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {F : S × Ω → E} {G : S → ℝ} {M C q K : ℝ}
    (hF : Measurable F) (hG : Measurable G) (hG0 : ∀ s, 0 ≤ G s)
    (hM : 0 < M) (hq : 1 ≤ q) (hq2 : q ≤ 2) (hK : 0 ≤ K)
    (hGi : Integrable (fun s => G s ^ 2) μ)
    (hGb : (∫ s, G s ^ 2 ∂μ) ≤ C * M ^ 2)
    (hpi : ∀ s, Integrable (fun ω => ‖F (s, ω)‖ ^ q) P)
    (hb : ∀ s, (∫ ω, ‖F (s, ω)‖ ^ q ∂P) ≤
      64 * K ^ q * (max (G s / M) 1) ^ q)
    (hm : ∀ s, (∫ ω, F (s, ω) ∂P) = 0) :
    Integrable F (μ.prod P) ∧ (∫ w, F w ∂μ.prod P) = 0 ∧
      Integrable (fun w => ‖F w‖ ^ q) (μ.prod P) ∧
      (∫ w, ‖F w‖ ^ q ∂μ.prod P) ≤ 64 * (2 + C) * K ^ q := by
  have hscaled := max_scaled_power_moment hG hG0 hM (by linarith : 0 ≤ q) hq2 hGi hGb
  have hbound := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (hF.norm.pow_const q).stronglyMeasurable
    (fun w => Real.rpow_nonneg (norm_nonneg (F w)) q)
    (Filter.Eventually.of_forall hpi)
    (hscaled.1.const_mul (64 * K ^ q)) (Filter.Eventually.of_forall hb)
  have hmean := HeavyTailedHessianTransport.mixture_mean_of_centered_moment
    (P := P) (Q := μ) (0 : E) hq hF (by simpa using hbound.1)
    (Filter.Eventually.of_forall hm)
  refine ⟨hmean.1, ?_, hbound.1, ?_⟩
  · simpa using hmean.2
  · rw [integral_const_mul] at hbound
    have hh := mul_le_mul_of_nonneg_left hscaled.2
      (show 0 ≤ 64 * K ^ q by positivity)
    calc
      _ ≤ 64 * K ^ q * (2 + C) := hbound.2.trans hh
      _ = _ := by ring

lemma masked_scaled_noise_product_moment {S Ω E : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure S} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {F : S × Ω → E} {G : S → ℝ} {A : S → Bool} {M C q K : ℝ}
    (hF : Measurable F) (hG : Measurable G) (hA : Measurable A)
    (hG0 : ∀ s, 0 ≤ G s) (hM : 0 < M) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hK : 0 ≤ K)
    (hGi : Integrable (fun s => (if A s then G s else 0) ^ 2) μ)
    (hGb : (∫ s, (if A s then G s else 0) ^ 2 ∂μ) ≤ C * M ^ 2)
    (hpi : ∀ s, A s = true → Integrable (fun ω => ‖F (s, ω)‖ ^ q) P)
    (hb : ∀ s, A s = true → (∫ ω, ‖F (s, ω)‖ ^ q ∂P) ≤
      64 * K ^ q * (max (G s / M) 1) ^ q)
    (hm : ∀ s, A s = true → (∫ ω, F (s, ω) ∂P) = 0) :
    let N := fun w : S × Ω => if A w.1 then F w else 0
    Integrable N (μ.prod P) ∧ (∫ w, N w ∂μ.prod P) = 0 ∧
      Integrable (fun w => ‖N w‖ ^ q) (μ.prod P) ∧
      (∫ w, ‖N w‖ ^ q ∂μ.prod P) ≤ 64 * (2 + C) * K ^ q := by
  intro N
  have hset : MeasurableSet {s | A s = true} := hA (measurableSet_singleton true)
  have hNm : Measurable N := hF.ite (hset.preimage measurable_fst) measurable_const
  have hGm : Measurable (fun s => if A s then G s else 0) :=
    hG.ite hset measurable_const
  apply scaled_noise_product_moment hNm hGm (fun s => by split; exact hG0 s; exact le_refl 0)
    hM hq hq2 hK hGi hGb
  · intro s
    by_cases hs : A s = true
    · simpa [N, hs] using hpi s hs
    · simp [N, hs, Real.zero_rpow (show q ≠ 0 by linarith)]
  · intro s
    by_cases hs : A s = true
    · simpa [N, hs] using hb s hs
    · simp only [N, hs, Bool.false_eq_true, ↓reduceIte, norm_zero,
        Real.zero_rpow (show q ≠ 0 by linarith), integral_zero]
      positivity
  · intro s
    by_cases hs : A s = true
    · simpa [N, hs] using hm s hs
    · simp [N, hs]

lemma masked_affine_random_segment_product {E Ω S : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {g : E → E} {L0 L1 q σ α M η K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M) (hη : 0 ≤ η)
    (hK : L0 + L1 * M + σ + α * M ≤ K)
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (H : (E × E) → Ω → E) (hHm : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (H (y, v)) P)
    (hm : ∀ y v, (∫ ω, H (y, v) ω ∂P) = fderiv ℝ g y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q) P)
    (hb : ∀ y v, (∫ ω, ‖H (y, v) ω - fderiv ℝ g y v‖ ^ q ∂P) ≤
      (σ ^ q + α ^ q * ‖g y‖ ^ q) * ‖v‖ ^ q)
    (X V : S → E) (A : S → Bool)
    (hX : Measurable X) (hV : Measurable V) (hA : Measurable A)
    (hv : ∀ s, ‖V s‖ ≤ η) (hsmall : L1 * η ≤ 1 / 4) (hbase : L0 * η ≤ M / 4)
    {C : ℝ} (hGi : Integrable (fun s => (if A s then ‖g (X s)‖ else 0) ^ 2) μ)
    (hGb : (∫ s, (if A s then ‖g (X s)‖ else 0) ^ 2 ∂μ) ≤ C * M ^ 2) :
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod P
    let N := fun w : S × (ℝ × Ω) => if A w.1 then
      H (X w.1 + w.2.1 • V w.1, V w.1) w.2.2 -
        (g (X w.1 + V w.1) - g (X w.1)) else 0
    Integrable N (μ.prod Q) ∧ (∫ w, N w ∂μ.prod Q) = 0 ∧
      Integrable (fun w => ‖N w‖ ^ q) (μ.prod Q) ∧
      (∫ w, ‖N w‖ ^ q ∂μ.prod Q) ≤ 64 * (2 + C) * (K * η) ^ q := by
  intro Q N
  let U : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioc]⟩
  let : IsProbabilityMeasure Q := inferInstanceAs (IsProbabilityMeasure (U.prod P))
  let F := fun w : S × (ℝ × Ω) =>
    H (X w.1 + w.2.1 • V w.1, V w.1) w.2.2 -
      (g (X w.1 + V w.1) - g (X w.1))
  have hinput : Measurable (fun w : S × (ℝ × Ω) =>
      ((X w.1 + w.2.1 • V w.1, V w.1), w.2.2)) := by fun_prop
  have hgm : Measurable g := hg.continuous.measurable
  have hFm : Measurable F := by
    exact (hHm.comp hinput).sub
      ((hgm.comp ((hX.comp measurable_fst).add (hV.comp measurable_fst))).sub
        (hgm.comp (hX.comp measurable_fst)))
  have hK0 : 0 ≤ K := by nlinarith [mul_nonneg hL1 hM.le, mul_nonneg hα hM.le]
  have hlocal (s : S) := affine_random_segment_transport hL0 hL1 hq hq2 hσ hα hM hη
    hK hg hD hH H hHm hi hm hpi hb (X s) (V s) (hv s) hsmall hbase
  exact masked_scaled_noise_product_moment hFm (hg.continuous.measurable.comp hX).norm
    hA (fun s => norm_nonneg _) hM hq hq2 (mul_nonneg hK0 hη) hGi hGb
    (fun s _ => (hlocal s).2.2.1) (fun s _ => (hlocal s).2.2.2) (fun s _ => by
      change (∫ w, H (X s + w.1 • V s, V s) w.2 -
        (g (X s + V s) - g (X s)) ∂Q) = 0
      rw [integral_sub (hlocal s).1 (integrable_const _), (hlocal s).2.1,
        integral_const, probReal_univ, one_smul, sub_self])

noncomputable def prefixNoiseSum {Ω E : Type*} [AddCommMonoid E]
    (e : (k : ℕ) → (Fin k → Ω) → Ω → E) : (k : ℕ) → (Fin k → Ω) → E
  | 0, _ => 0
  | k + 1, ξ => prefixNoiseSum e k (fun i => ξ i.castSucc) +
      e k (fun i => ξ i.castSucc) (ξ (Fin.last k))

lemma measurable_prefixNoiseSum {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (e : (k : ℕ) → (Fin k → Ω) → Ω → E)
    (he : ∀ k, Measurable (Function.uncurry (e k))) (k : ℕ) :
    Measurable (prefixNoiseSum e k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      change Measurable (fun ξ : Fin (k + 1) → Ω =>
        prefixNoiseSum e k (fun i => ξ i.castSucc) +
          e k (fun i => ξ i.castSucc) (ξ (Fin.last k)))
      have hprefix : Measurable (fun ξ : Fin (k + 1) → Ω =>
          fun i : Fin k => ξ i.castSucc) := by fun_prop
      exact (ih.comp hprefix).add ((he k).comp
        (hprefix.prodMk (measurable_pi_apply (Fin.last k))))

lemma prefix_sum_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (e : (k : ℕ) → (Fin k → Ω) → Ω → E)
    (he : ∀ k, Measurable (Function.uncurry (e k)))
    (hi : ∀ k η, Integrable (e k η) P) (hz : ∀ k η, (∫ ω, e k η ω ∂P) = 0)
    (hep : ∀ k, Integrable (fun ξ : ℕ → Ω => ‖e k (fun i => ξ i) (ξ k)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P)) (n : ℕ) :
    (∫ ξ : ℕ → Ω, ‖prefixNoiseSum e n (fun i => ξ i)‖ ^ p
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      6 * ∑ k ∈ Finset.range n, ∫ ξ : ℕ → Ω, ‖e k (fun i => ξ i) (ξ k)‖ ^ p
        ∂Measure.infinitePi (fun _ : ℕ => P) := by
  exact prefix_martingale_moment P hp hp2 (prefixNoiseSum e) e
    (measurable_prefixNoiseSum e he) he hi hz hep (fun _ => rfl) (fun _ _ => rfl) n

lemma prefixNoiseSum_eq_sum {Ω E : Type*} [AddCommMonoid E]
    (e : (k : ℕ) → (Fin k → Ω) → Ω → E) (n : ℕ) (ξ : ℕ → Ω) :
    prefixNoiseSum e n (fun i => ξ i) =
      ∑ k ∈ Finset.range n, e k (fun i => ξ i) (ξ k) := by
  induction n with
  | zero => simp [prefixNoiseSum]
  | succ n ih =>
      change prefixNoiseSum e n (fun i => ξ i) + e n (fun i => ξ i) (ξ n) = _
      rw [ih, Finset.sum_range_succ]

lemma prefix_sum_integrable_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp : 0 < p) (e : (k : ℕ) → (Fin k → Ω) → Ω → E)
    (he : ∀ k, Measurable (Function.uncurry (e k)))
    (hep : ∀ k, Integrable (fun ξ : ℕ → Ω => ‖e k (fun i => ξ i) (ξ k)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P)) (n : ℕ) :
    Integrable (fun ξ : ℕ → Ω => ‖prefixNoiseSum e n (fun i => ξ i)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) := by
  induction n with
  | zero => simp [prefixNoiseSum, Real.zero_rpow hp.ne']
  | succ n ih =>
      have hsum : Measurable (fun ξ : ℕ → Ω => prefixNoiseSum e n (fun i => ξ i)) :=
        (measurable_prefixNoiseSum e he n).comp (by fun_prop)
      have hinc : Measurable (fun ξ : ℕ → Ω => e n (fun i => ξ i) (ξ n)) :=
        (he n).comp (f := fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ n)) (by fun_prop)
      exact HeavyTailedMomentBounds.integrable_norm_sum_rpow hp
        hsum.aestronglyMeasurable hinc.aestronglyMeasurable ih (hep n)

lemma scaled_root_power {c A B p : ℝ} (hc : 1 ≤ c) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hp : 1 ≤ p) : c * B * A ^ p ≤ (c * A * B ^ p⁻¹) ^ p := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcp : c ≤ c ^ p := by
    calc
      c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
      _ ≤ c ^ p := Real.rpow_le_rpow_of_exponent_le hc hp
  rw [Real.mul_rpow (mul_nonneg hc0 hA) (Real.rpow_nonneg hB _),
    Real.mul_rpow hc0 hA, Real.rpow_inv_rpow hB (by linarith : p ≠ 0)]
  nlinarith [mul_le_mul_of_nonneg_right hcp
    (mul_nonneg (Real.rpow_nonneg hA p) hB)]

lemma norm_first_from_power {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} {p r : ℝ}
    (hX : Measurable X) (hp : 1 ≤ p) (hr : 0 ≤ r)
    (hi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hb : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ r ^ p) :
    Integrable (fun ω => ‖X ω‖) P ∧ (∫ ω, ‖X ω‖ ∂P) ≤ r := by
  have hfirst : Integrable (fun ω => ‖X ω‖) P := by
    have hh := integrable_norm_rpow_of_le hX.aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ p) hp hi
    simpa using hh
  refine ⟨hfirst, ?_⟩
  have hh := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω))) hfirst hi
  exact (Real.rpow_le_rpow_iff (integral_nonneg (fun ω => norm_nonneg _)) hr
    (by linarith : 0 < p)).mp (hh.trans hb)

lemma reset_moment_scale {σ α M p : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 ≤ M) (hp : 1 ≤ p) :
    6 * (σ ^ p + 9 * α ^ p * M ^ p) ≤ 54 * (σ + α * M) ^ p := by
  have hh := Real.add_rpow_le_rpow_add hσ (mul_nonneg hα hM) hp
  rw [Real.mul_rpow hα hM] at hh
  nlinarith [Real.rpow_nonneg hσ p]

lemma batch_first_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} {p σ α M B : ℝ}
    (hX : Measurable X) (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 ≤ M) (hB : 0 < B)
    (hi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hb : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ 6 * (σ ^ p + 9 * α ^ p * M ^ p) / B ^ (p - 1)) :
    Integrable (fun ω => ‖X ω‖) P ∧
      (∫ ω, ‖X ω‖ ∂P) ≤ 54 * (σ + α * M) * (B ^ (p - 1))⁻¹ ^ p⁻¹ := by
  have hden : 0 < B ^ (p - 1) := Real.rpow_pos_of_pos hB _
  apply norm_first_from_power hX hp (by positivity) hi
  have hh := scaled_root_power (by norm_num : (1 : ℝ) ≤ 54)
    (show 0 ≤ σ + α * M by positivity) (inv_nonneg.mpr hden.le) hp
  have hs := div_le_div_of_nonneg_right (reset_moment_scale hσ hα hM hp) hden.le
  calc
    _ ≤ 54 * (σ + α * M) ^ p / B ^ (p - 1) := hb.trans hs
    _ = 54 * (B ^ (p - 1))⁻¹ * (σ + α * M) ^ p := by ring
    _ ≤ _ := hh

end LongTails.Proofs.GuardedHessianNoise
