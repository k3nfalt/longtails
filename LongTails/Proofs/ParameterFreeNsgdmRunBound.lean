import LongTails.Proofs.ParameterFreeNsgdmRunMoments
import Mathlib.Algebra.Order.Field.GeomSum

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ParameterFreeNsgdmRunBound

open ParameterFreeNsgdmRun ParameterFreeNsgdmMoments ParameterFreeNsgdmRunMoments

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

structure Oracle (ν : Measure Ω) (g : E → Ω → E) (grad : E → E) (σ p : ℝ) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) ν
  unbiased : ∀ x, (∫ ω, g x ω ∂ν) = grad x
  moment_integrable : ∀ x, Integrable (fun ω => ‖g x ω - grad x‖ ^ p) ν
  moment : ∀ x, (∫ ω, ‖g x ω - grad x‖ ^ p ∂ν) ≤ σ ^ p

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {g : E → Ω → E} {grad : E → E} {σ p L : ℝ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma grad_measurable (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) :
    Measurable grad := by
  have hcont : Continuous grad := by
    apply LipschitzWith.continuous (K := Real.toNNReal L)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal L hL]
    exact hlip x y
  exact hcont.measurable

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
lemma sampleNoise_measurable (hO : Oracle ν g grad σ p) (hgrad : Measurable grad) :
    Measurable (Function.uncurry (sampleNoise g grad)) := by
  unfold sampleNoise Function.uncurry
  exact hO.measurable.sub (hgrad.comp measurable_fst)

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma sampleNoise_integrable (hO : Oracle ν g grad σ p) (x : E) :
    Integrable (sampleNoise g grad x) ν :=
  (hO.integrable x).sub (integrable_const _)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma sampleNoise_mean (hO : Oracle ν g grad σ p) (x : E) :
    (∫ ω, sampleNoise g grad x ω ∂ν) = 0 := by
  unfold sampleNoise
  rw [integral_sub (hO.integrable x) (integrable_const _), hO.unbiased, integral_const]
  simp

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure ν] in
lemma scaled_noise_moment (hO : Oracle ν g grad σ p) {w : ℝ}
    (hw : 0 ≤ w) (x : E) :
    Integrable (fun ω => ‖w • sampleNoise g grad x ω‖ ^ p) ν ∧
      (∫ ω, ‖w • sampleNoise g grad x ω‖ ^ p ∂ν) ≤ w ^ p * σ ^ p := by
  have heq : (fun ω => ‖w • sampleNoise g grad x ω‖ ^ p) =
      fun ω => w ^ p * ‖sampleNoise g grad x ω‖ ^ p := by
    funext ω
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, Real.mul_rpow hw (norm_nonneg _)]
  rw [heq]
  refine ⟨(hO.moment_integrable x).const_mul _, ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hO.moment x) (by positivity)

lemma noisePart_moment (hO : Oracle ν g grad σ p) (hgrad : Measurable grad) (hp : 1 ≤ p)
    (hp2 : p ≤ 2) (hσ : 0 ≤ σ) {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (x0 : E) (t : ℕ) :
    Integrable (fun ξ => ‖noisePart α η g grad x0 ξ t‖ ^ p) (Measure.infinitePi fun _ : ℕ => ν) ∧
      (∫ ξ, ‖noisePart α η g grad x0 ξ t‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤
        6 * σ ^ p * ((1 - α) ^ (p * t) + α ^ (p - 1)) := by
  have hmeas : ∀ k, Measurable (Function.uncurry
      (fun (st : E × E × ℕ) ω => weight α t k • sampleNoise g grad st.1 ω)) := by
    intro k
    exact measurable_const.smul ((sampleNoise_measurable hO hgrad).comp
      (measurable_fst.fst.prodMk measurable_snd))
  have hw : ∀ k, 0 ≤ weight α t k := weight_nonneg hα0.le hα1 t
  have hh := timedSum_moment ν (step := runStep α η g)
    (runStep_measurable (α := α) (η := η) hO.measurable) hmeas hp hp2
    (κ := fun k => weight α t k ^ p * σ ^ p)
    (fun k st => (sampleNoise_integrable hO st.1).smul _)
    (fun k st => by rw [integral_smul, sampleNoise_mean hO]; simp)
    (fun k st => (scaled_noise_moment hO (hw k) st.1).1)
    (fun k st => (scaled_noise_moment hO (hw k) st.1).2) (t + 1) 0 (x0, 0, 0) 0
  simp only [noisePart_eq_timedSum, zero_add] at hh ⊢
  refine ⟨hh.1, hh.2.trans ?_⟩
  rw [norm_zero, Real.zero_rpow (by linarith), zero_add]
  have := weight_sum_rpow hα0 hα1 hp t
  calc 6 * (∑ k ∈ Finset.range (t + 1), weight α t k ^ p * σ ^ p) =
        6 * σ ^ p * ∑ k ∈ Finset.range (t + 1), weight α t k ^ p := by
          rw [← Finset.sum_mul]; ring
    _ ≤ 6 * σ ^ p * ((1 - α) ^ (p * t) + α ^ (p - 1)) := by gcongr

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
lemma noisePart_measurable (hO : Oracle ν g grad σ p) (hgrad : Measurable grad) (α η : ℝ)
    (x0 : E) (t : ℕ) : Measurable (fun ξ : ℕ → Ω => noisePart α η g grad x0 ξ t) := by
  have hmeas : ∀ k, Measurable (Function.uncurry
      (fun (st : E × E × ℕ) ω => weight α t k • sampleNoise g grad st.1 ω)) := by
    intro k
    exact measurable_const.smul ((sampleNoise_measurable hO hgrad).comp
      (measurable_fst.fst.prodMk measurable_snd))
  have hT : Measurable (fun u : ((E × E × ℕ) × E) × (ℕ → Ω) =>
      timedSum (runStep α η g) (fun k st ω => weight α t k • sampleNoise g grad st.1 ω) (t + 1) 0
        u.1.1 u.1.2 u.2) :=
    timedSum_measurable (step := runStep α η g)
      (runStep_measurable (α := α) (η := η) hO.measurable) hmeas (t + 1) 0
  have hc : Measurable (fun ξ : ℕ → Ω => (((x0, (0 : E), (0 : ℕ)), (0 : E)), ξ)) :=
    measurable_const.prodMk measurable_id
  have heq : (fun ξ : ℕ → Ω => noisePart α η g grad x0 ξ t) = fun ξ =>
      timedSum (runStep α η g) (fun s st ω => weight α t s • sampleNoise g grad st.1 ω) (t + 1) 0
        (x0, 0, 0) 0 ξ :=
    funext fun ξ => noisePart_eq_timedSum α η g grad x0 ξ t
  rw [heq]
  exact hT.comp hc

lemma noisePart_expectation (hO : Oracle ν g grad σ p) (hgrad : Measurable grad) (hp : 1 < p)
    (hp2 : p ≤ 2) (hσ : 0 ≤ σ) {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (x0 : E) (t : ℕ) :
    Integrable (fun ξ => ‖noisePart α η g grad x0 ξ t‖) (Measure.infinitePi fun _ : ℕ => ν) ∧
      (∫ ξ, ‖noisePart α η g grad x0 ξ t‖ ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤
        6 * σ * ((1 - α) ^ t + α ^ ((p - 1) / p)) := by
  have hm := noisePart_moment hO hgrad hp.le hp2 hσ hα0 hα1 (η := η) x0 t
  have hmeas := (noisePart_measurable hO hgrad α η x0 t).aestronglyMeasurable
    (μ := Measure.infinitePi fun _ : ℕ => ν)
  have hp0 : 0 < p := by linarith
  have hint : Integrable (fun ξ => ‖noisePart α η g grad x0 ξ t‖)
      (Measure.infinitePi fun _ : ℕ => ν) := by
    have hLp : MemLp (fun ξ => noisePart α η g grad x0 ξ t) (ENNReal.ofReal p)
        (Measure.infinitePi fun _ : ℕ => ν) := by
      apply (integrable_norm_rpow_iff hmeas (by simp [hp0]) (by simp)).mp
      simpa only [ENNReal.toReal_ofReal hp0.le] using hm.1
    exact (memLp_one_iff_integrable.mp (hLp.mono_exponent (p := 1) (by simpa using hp.le))).norm
  refine ⟨hint, ?_⟩
  have hroot := HeavyTailedMomentBounds.integral_norm_le_root_moment hp hmeas hm.1
  refine hroot.trans ?_
  have h1 : 0 ≤ 1 - α := by linarith
  have hA : 0 ≤ (1 - α) ^ (p * t) := Real.rpow_nonneg h1 _
  have hB : 0 ≤ α ^ (p - 1) := by positivity
  calc (∫ ξ, ‖noisePart α η g grad x0 ξ t‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => ν)) ^ (1 / p)
      ≤ (6 * σ ^ p * ((1 - α) ^ (p * t) + α ^ (p - 1))) ^ (1 / p) := by
        apply Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hm.2 (by positivity)
    _ = 6 ^ (1 / p) * σ * ((1 - α) ^ (p * t) + α ^ (p - 1)) ^ (1 / p) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_mul hσ, mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ ≤ 6 * σ * ((1 - α) ^ t + α ^ ((p - 1) / p)) := by
        have h6 : (6 : ℝ) ^ (1 / p) ≤ 6 := by
          calc (6 : ℝ) ^ (1 / p) ≤ (6 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                  rw [div_le_one hp0]; exact hp.le)
            _ = 6 := Real.rpow_one _
        have hsub : ((1 - α) ^ (p * t) + α ^ (p - 1)) ^ (1 / p) ≤
            ((1 - α) ^ (p * t)) ^ (1 / p) + (α ^ (p - 1)) ^ (1 / p) :=
          Real.rpow_add_le_add_rpow hA hB (by positivity) (by rw [div_le_one hp0]; exact hp.le)
        have hA' : ((1 - α) ^ (p * t)) ^ (1 / p) = (1 - α) ^ t := by
          rw [← Real.rpow_mul h1, mul_comm p, mul_assoc, mul_one_div_cancel hp0.ne', mul_one,
            Real.rpow_natCast]
        have hB' : (α ^ (p - 1)) ^ (1 / p) = α ^ ((p - 1) / p) := by
          rw [← Real.rpow_mul hα0.le]; congr 1; ring
        rw [hA', hB'] at hsub
        have hσ6 : 0 ≤ 6 ^ (1 / p) * σ := by positivity
        have hX : 0 ≤ (1 - α) ^ t + α ^ ((p - 1) / p) :=
          add_nonneg (pow_nonneg h1 t) (Real.rpow_nonneg hα0.le _)
        calc 6 ^ (1 / p) * σ * ((1 - α) ^ (p * t) + α ^ (p - 1)) ^ (1 / p)
            ≤ 6 ^ (1 / p) * σ * ((1 - α) ^ t + α ^ ((p - 1) / p)) :=
              mul_le_mul_of_nonneg_left hsub hσ6
          _ ≤ 6 * σ * ((1 - α) ^ t + α ^ ((p - 1) / p)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 hσ) hX


omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma run_displacement {α η : ℝ} (hη : 0 ≤ η) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    ‖(run α η g x0 ξ t).1 - x0‖ ≤ t * η := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      have hstep : ‖(run α η g x0 ξ (t + 1)).1 - (run α η g x0 ξ t).1‖ ≤ η := by
        rw [run_point_succ]
        exact normalized_move_norm η hη _ _
      calc ‖(run α η g x0 ξ (t + 1)).1 - x0‖
          = ‖((run α η g x0 ξ (t + 1)).1 - (run α η g x0 ξ t).1) + ((run α η g x0 ξ t).1 - x0)‖ := by
            congr 1; abel
        _ ≤ η + t * η := (norm_add_le _ _).trans (add_le_add hstep ih)
        _ = (t + 1 : ℕ) * η := by push_cast; ring

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma run_grad_bound (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {α η : ℝ} (hη : 0 ≤ η) (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    ‖grad (run α η g x0 ξ t).1‖ ≤ ‖grad x0‖ + L * (t * η) := by
  have h1 := hlip (run α η g x0 ξ t).1 x0
  have h2 := run_displacement (α := α) hη g x0 ξ t
  have h3 : ‖grad (run α η g x0 ξ t).1‖ ≤ ‖grad x0‖ + ‖grad (run α η g x0 ξ t).1 - grad x0‖ := by
    have := norm_add_le (grad x0) (grad (run α η g x0 ξ t).1 - grad x0)
    simpa using this
  calc ‖grad (run α η g x0 ξ t).1‖ ≤ ‖grad x0‖ + L * ‖(run α η g x0 ξ t).1 - x0‖ := by linarith
    _ ≤ ‖grad x0‖ + L * (t * η) := by gcongr

omit [CompleteSpace E] in
lemma run_measurable (hg : Measurable (Function.uncurry g)) (α η : ℝ) (x0 : E) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => run α η g x0 ξ t) := by
  have hc : Measurable (fun ξ : ℕ → Ω => ((x0, (0 : E), (0 : ℕ)), ξ)) :=
    measurable_const.prodMk measurable_id
  have h := (HeavyTailedProductProcess.trajectory_measurable
    (runStep_measurable (α := α) (η := η) hg) (E := E × E × ℕ) t).comp hc
  have heq : (fun ξ : ℕ → Ω => run α η g x0 ξ t) = fun ξ =>
      HeavyTailedProductProcess.trajectory (runStep α η g) t (x0, 0, 0) ξ :=
    funext fun ξ => run_eq_trajectory α η g x0 ξ t
  rw [heq]
  exact h

omit [CompleteSpace E] in
lemma run_grad_integrable (hO : Oracle ν g grad σ p) (hgrad : Measurable grad)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {α η : ℝ} (hη : 0 ≤ η) (x0 : E) (t : ℕ) :
    Integrable (fun ξ : ℕ → Ω => ‖grad (run α η g x0 ξ t).1‖) (Measure.infinitePi fun _ : ℕ => ν) := by
  have hmeas : Measurable (fun ξ : ℕ → Ω => ‖grad (run α η g x0 ξ t).1‖) :=
    (hgrad.comp (measurable_fst.comp (run_measurable hO.measurable α η x0 t))).norm
  refine Integrable.of_bound hmeas.aestronglyMeasurable (‖grad x0‖ + L * (t * η)) ?_
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact run_grad_bound hlip hL hη g x0 ξ t

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma run_sum_pathwise {f : E → ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {lower Δ : ℝ} (hlow : ∀ x, lower ≤ f x) (hΔ : f x0 - lower ≤ Δ)
    {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hη : 0 < η) (g : E → Ω → E) (ξ : ℕ → Ω) (T : ℕ) :
    ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖ ≤
      Δ / η + 2 * ∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖ +
      T * (2 * L * η * (1 - α) / α + L / 2 * η) := by
  have hsum := descent_sum hg hlip hL (α := α) hη.le g x0 ξ T
  have herr : ∑ t ∈ Finset.range T, ‖(run α η g x0 ξ (t + 1)).2.1 - gradient f (run α η g x0 ξ t).1‖ ≤
      ∑ t ∈ Finset.range T, (‖noisePart α η g (gradient f) x0 ξ t‖ + L * η * (1 - α) / α) :=
    Finset.sum_le_sum (fun t _ => momentum_error_le hlip hL hα0 hα1 hη.le g x0 ξ t)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at herr
  have hgap : f x0 - f (run α η g x0 ξ T).1 ≤ Δ := by linarith [hlow (run α η g x0 ξ T).1]
  have hdiv : ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖ ≤
      (f x0 - f (run α η g x0 ξ T).1) / η +
      2 * ∑ t ∈ Finset.range T, ‖(run α η g x0 ξ (t + 1)).2.1 - gradient f (run α η g x0 ξ t).1‖ +
      T * (L / 2 * η) := by
    have hkey : ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖ ≤
        (f x0 - f (run α η g x0 ξ T).1 +
          2 * η * ∑ t ∈ Finset.range T, ‖(run α η g x0 ξ (t + 1)).2.1 - gradient f (run α η g x0 ξ t).1‖ +
          T * (L / 2 * η ^ 2)) / η := by
      rw [le_div_iff₀ hη]
      linarith [hsum]
    refine hkey.trans (le_of_eq ?_)
    field_simp
    try ring
  have hgapdiv : (f x0 - f (run α η g x0 ξ T).1) / η ≤ Δ / η :=
    div_le_div_of_nonneg_right hgap hη.le
  calc ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖
      ≤ (f x0 - f (run α η g x0 ξ T).1) / η +
        2 * ∑ t ∈ Finset.range T, ‖(run α η g x0 ξ (t + 1)).2.1 - gradient f (run α η g x0 ξ t).1‖ +
        T * (L / 2 * η) := hdiv
    _ ≤ Δ / η + 2 * (∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖ +
        T * (L * η * (1 - α) / α)) + T * (L / 2 * η) := by gcongr
    _ = Δ / η + 2 * ∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖ +
        T * (2 * L * η * (1 - α) / α + L / 2 * η) := by ring


lemma geom_sum_le_inv {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, q ^ t ≤ 1 / (1 - q) := by
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := T) hq0 hq1
  simpa using this

lemma run_average_expectation {f : E → ℝ} (hO : Oracle ν g (gradient f) σ p)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L)
    {lower Δ : ℝ} (hlow : ∀ x, lower ≤ f x) (hΔ : f x0 - lower ≤ Δ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    {α η : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hη : 0 < η) (T : ℕ) :
    Integrable (fun ξ : ℕ → Ω => ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖)
      (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ξ, ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖
        ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤
      Δ / η + 12 * σ / α + 12 * σ * T * α ^ ((p - 1) / p) +
        T * (2 * L * η * (1 - α) / α + L / 2 * η) := by
  have hgrad : Measurable (gradient f) := grad_measurable hlip hL
  have hint : Integrable (fun ξ : ℕ → Ω => ∑ t ∈ Finset.range T, ‖gradient f (run α η g x0 ξ t).1‖)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    integrable_finsetSum _ (fun t _ => run_grad_integrable hO hgrad hlip hL hη.le x0 t)
  refine ⟨hint, ?_⟩
  have hN : ∀ t, Integrable (fun ξ : ℕ → Ω => ‖noisePart α η g (gradient f) x0 ξ t‖)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    fun t => (noisePart_expectation hO hgrad hp hp2 hσ hα0 hα1 (η := η) x0 t).1
  have hf2 : Integrable (fun ξ : ℕ → Ω =>
      2 * ∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    (integrable_finsetSum _ (fun t _ => hN t)).const_mul 2
  have hf1 : Integrable (fun ξ : ℕ → Ω => Δ / η +
      2 * ∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖)
      (Measure.infinitePi fun _ : ℕ => ν) :=
    (integrable_const _).add hf2
  have hrhs : Integrable (fun ξ : ℕ → Ω => Δ / η +
      2 * ∑ t ∈ Finset.range T, ‖noisePart α η g (gradient f) x0 ξ t‖ +
      T * (2 * L * η * (1 - α) / α + L / 2 * η)) (Measure.infinitePi fun _ : ℕ => ν) :=
    hf1.add (integrable_const _)
  have hmono := integral_mono hint hrhs
    (fun ξ => run_sum_pathwise hg hlip hL hlow hΔ hα0 hα1 hη g ξ T)
  rw [integral_add hf1 (integrable_const _), integral_add (integrable_const _) hf2,
    integral_const, integral_const, integral_const_mul, integral_finsetSum _ (fun t _ => hN t)] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have hsumN : ∑ t ∈ Finset.range T, (∫ ξ, ‖noisePart α η g (gradient f) x0 ξ t‖
      ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤
      6 * σ * (1 / α) + 6 * σ * T * α ^ ((p - 1) / p) := by
    calc ∑ t ∈ Finset.range T, (∫ ξ, ‖noisePart α η g (gradient f) x0 ξ t‖
          ∂Measure.infinitePi (fun _ : ℕ => ν))
        ≤ ∑ t ∈ Finset.range T, 6 * σ * ((1 - α) ^ t + α ^ ((p - 1) / p)) :=
          Finset.sum_le_sum (fun t _ =>
            (noisePart_expectation hO hgrad hp hp2 hσ hα0 hα1 (η := η) x0 t).2)
      _ = 6 * σ * ∑ t ∈ Finset.range T, (1 - α) ^ t + 6 * σ * T * α ^ ((p - 1) / p) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          ring
      _ ≤ 6 * σ * (1 / α) + 6 * σ * T * α ^ ((p - 1) / p) := by
          gcongr
          have := geom_sum_le_inv (q := 1 - α) (by linarith) (by linarith) T
          simpa using this
  have h12 : 2 * (6 * σ * (1 / α) + 6 * σ * T * α ^ ((p - 1) / p)) =
      12 * σ / α + 12 * σ * T * α ^ ((p - 1) / p) := by ring
  nlinarith [hmono, hsumN, h12]

end LongTails.Proofs.ParameterFreeNsgdmRunBound
