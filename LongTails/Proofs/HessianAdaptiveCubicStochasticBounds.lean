import LongTails.Proofs.HessianAdaptiveCubicResidual
import LongTails.Proofs.HessianAdaptiveCubicMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HessianAdaptiveCubicStochasticBounds

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicMeasurability
open LongTails.Proofs.HessianAdaptiveCubicStep
open LongTails.Proofs.HessianAdaptiveCubicNormalization
open LongTails.Proofs.HessianAdaptiveCubicResidual

lemma measurable_movement {X : Type*} [MeasurableSpace X] (p : Public)
    (s : X → State p.d) (hs : MeasurableState p s) : Measurable (fun x => movement p (s x)) := by
  have ha := measurable_increment p s hs
  have hi := hs.iteration
  have hτ := measurable_damping p s hs
  have hκ := hs.scale
  have hu := hs.trial
  have hz := hs.dual
  unfold movement mixing
  fun_prop

lemma integrable_movement {X : Type*} [MeasurableSpace X] (p : Public)
    (μ : Measure X) [IsFiniteMeasure μ] (s : X → State p.d) (hs : MeasurableState p s)
    (hD : 0 < p.D) (hinv : ∀ x, Invariant p (s x))
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    Integrable (fun x => movement p (s x)) μ := by
  apply (integrable_const (p.D ^ 2)).mono' (measurable_movement p s hs).aestronglyMeasurable
  filter_upwards [] with x
  have hb := movement_bounds p (s x) hD (hinv x) hdiam
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

lemma integrable_scale_squares {X : Type*} [MeasurableSpace X] (p : Public)
    (μ : Measure X) [IsFiniteMeasure μ] (S : ℕ → X → State p.d)
    (gd : ℕ → X → Point p.d) (f : Point p.d → ℝ)
    (hm : ∀ n, MeasurableState p (S n)) (hD : 0 < p.D) (hσ : 0 ≤ p.σg)
    (hinv : ∀ n x, Invariant p (S n x))
    (ht : ∀ n x, (S n x).iteration = n + 1)
    (hfloor : ∀ n x, p.σg * ((n + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2 ≤ (S n x).scale)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hinit : ∀ x, (S 0 x).scale = 2 * p.ρ + p.σg / p.D ^ 2)
    (hnext : ∀ n x, (S (n + 1) x).scale = (advance p (S n x) (gd n x)).scale)
    (hdual : ∀ n, Integrable (fun x => ‖gd n x - gradient f (queryPoint (S n x))‖ ^ 2) μ)
    (hmodel : ∀ n, Integrable (fun x => ‖(S n x).modelGradient - gradient f (center (S n x))‖ ^ 2) μ)
    (hhess : ∀ n, Integrable (fun x =>
      ‖(S n x).modelHessian - fderiv ℝ (gradient f) (center (S n x))‖ ^ 2) μ) :
    ∀ n, Integrable (fun x => (S n x).scale ^ 2) μ := by
  intro n
  induction n with
  | zero => simpa only [hinit] using (integrable_const ((2 * p.ρ + p.σg / p.D ^ 2) ^ 2) :
      Integrable (fun _ : X => (2 * p.ρ + p.σg / p.D ^ 2) ^ 2) μ)
  | succ n ih =>
    let B : X → ℝ := fun x => (S n x).scale ^ 2 +
      (4 * (((n + 1 : ℕ) : ℝ) ^ 5 / p.D ^ 2) * ‖gd n x - gradient f (queryPoint (S n x))‖ ^ 2 +
      4 * (((n + 1 : ℕ) : ℝ) ^ 5 / p.D ^ 2) * ‖(S n x).modelGradient - gradient f (center (S n x))‖ ^ 2 +
      4 * ((n + 1 : ℕ) : ℝ) ^ 2 * ‖(S n x).modelHessian - fderiv ℝ (gradient f) (center (S n x))‖ ^ 2 +
      p.ρ ^ 2 * movement p (S n x)) / p.D ^ 2 +
      (p.σg * ((n + 1 + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2) ^ 2 -
      (p.σg * ((n + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2) ^ 2
    have hmove := integrable_movement p μ (S n) (hm n) hD (hinv n) hdiam
    have hB : Integrable B μ := by
      apply Integrable.sub _ (integrable_const _)
      apply Integrable.add _ (integrable_const _)
      apply ih.add
      apply Integrable.div_const
      exact ((((hdual n).const_mul _).add ((hmodel n).const_mul _)).add
        ((hhess n).const_mul _)).add (hmove.const_mul _)
    apply integrable_square_of_bound μ (fun x => (S (n + 1) x).scale) B (hm (n + 1)).scale hB
    intro x
    have hf : p.σg * ((S n x).iteration : ℝ) ^ 3 / p.D ^ 2 ≤ (S n x).scale := by
      simpa only [ht] using hfloor n x
    have hb := model_scale_square_bound p (S n x) (gd n x) f hD hσ (hinv n x) hf hdiff hLip
    simpa only [hnext, ht, B] using hb

lemma round_scale_lower_bound {Ω : Type*} (p : Public)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (ξ : ℕ → Ω) (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (n : ℕ) : 2 * p.ρ + p.σg / p.D ^ 2 ≤ (roundState p g H ξ n).scale := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hs := modelAt_invariant p g H ξ hD hρ hσ hx n
    exact ih.trans (advance_scale_ge p (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) hD hs)

lemma integrable_norm_of_square {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → E) (he : Measurable e)
    (hi : Integrable (fun x => ‖e x‖ ^ 2) μ) : Integrable (fun x => ‖e x‖) μ := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' he.norm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖e x‖ - 1)]

open LongTails.Proofs.HessianAdaptiveCubicMoments
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma model_scale_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (σh : ℝ)
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hhi : ∀ x ∈ p.C, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2) μ)
    (hhb : ∀ x ∈ p.C, (∫ ω, ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2 ∂μ) ≤ σh ^ 2)
    (n : ℕ) : Integrable (fun ξ => (modelAt p g H ξ n).scale ^ 2) P := by
  let S := fun n ξ => modelAt p g H ξ n
  let gd := fun n ξ => g (queryPoint (S n ξ)) (ξ (3 * n + 2))
  have hm (n : ℕ) : MeasurableState p (S n) :=
    measurable_modelAt p hD hρ hσ hx g H hg hH hPSD (fun k (ξ : ℕ → Ω) => ξ k)
      (fun k => measurable_pi_apply k) n
  apply integrable_scale_squares p P S gd f hm hD hσ
    (fun n ξ => modelAt_invariant p g H ξ hD hρ hσ hx n)
    (fun n ξ => roundState_iteration p g H ξ n)
    (fun n ξ => roundState_scale_floor p g H ξ hρ.le n)
    hdiam hdiff hLip (fun _ => rfl) (fun _ _ => rfl) _ _ _ n
  · intro k
    exact (model_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
      p.σg hgi hgb k).1
  · intro k
    exact (center_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
      p.σg hgi hgb k (3 * k) le_rfl).1
  · intro k
    exact (center_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => H x ω - fderiv ℝ (gradient f) x) (measurable_hessian_error p f H hH)
      σh hhi hhb k (3 * k + 1) (by omega)).1

lemma normalized_linear_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v e : E) {a B D κ Λ : ℝ} (ha : 0 ≤ a) (haB : a ≤ B) (hv : ‖v‖ ≤ D)
    (hκ : 0 < κ) (hΛ : κ ≤ Λ) :
    |-a * ⟪v, e⟫ / Λ| ≤ (B * D / κ) * ‖e‖ := by
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have hB : 0 ≤ B := ha.trans haB
  have hΛp := hκ.trans_le hΛ
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg ha, abs_of_pos hΛp]
  have hi := (abs_real_inner_le_norm v e).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg e))
  have hm := mul_le_mul haB hi (abs_nonneg _) hB
  have hd := div_le_div_of_nonneg_left (show 0 ≤ B * (D * ‖e‖) by positivity) hκ hΛ
  calc
    _ ≤ B * (D * ‖e‖) / Λ := div_le_div_of_nonneg_right hm hΛp.le
    _ ≤ B * (D * ‖e‖) / κ := hd
    _ = _ := by ring

lemma integrable_normalized_linear {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) (a Λ : X → ℝ) (v e : X → E) (B D κ : ℝ)
    (hκ : 0 < κ) (ha : Measurable a) (hΛ : Measurable Λ) (hv : Measurable v)
    (he : Measurable e) (hie : Integrable (fun x => ‖e x‖) μ)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ B) (hvb : ∀ x, ‖v x‖ ≤ D) (hΛb : ∀ x, κ ≤ Λ x) :
    Integrable (fun x => -a x * ⟪v x, e x⟫ / Λ x) μ := by
  apply (hie.const_mul (B * D / κ)).mono'
    (((ha.neg.mul (hv.inner he)).div hΛ).aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, Pi.div_apply, Pi.mul_apply, Pi.neg_apply] using
    normalized_linear_bound (v x) (e x) (hab x).1 (hab x).2 (hvb x) hκ (hΛb x)

lemma integrable_step_normalized_noise {X : Type*} [MeasurableSpace X]
    (p : Public) (μ : Measure X) [IsFiniteMeasure μ] (s : X → State p.d)
    (gd : X → Point p.d) (f : Point p.d → ℝ) (xstar : Point p.d) (t : ℕ) (κ : ℝ)
    (hs : MeasurableState p s) (hg : Measurable gd) (hdiff : Differentiable ℝ (gradient f))
    (hD : 0 < p.D) (hinv : ∀ x, Invariant p (s x)) (hx : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (ht : ∀ x, (s x).iteration = t) (hκ : 0 < κ) (hscale : ∀ x, κ ≤ (s x).scale)
    (hi : Integrable (fun x => ‖gd x - gradient f (queryPoint (s x))‖ ^ 2) μ) :
    Integrable (fun x => -increment p (s x) *
      ⟪(s x).trial - xstar, gd x - gradient f (queryPoint (s x))⟫ /
        (advance p (s x) (gd x)).scale) μ := by
  have he := hg.sub (hdiff.continuous.measurable.comp (measurable_queryPoint p s hs))
  apply integrable_normalized_linear μ _ _ _ _ ((t : ℝ) ^ 2 * Real.sqrt t / p.D) p.D κ hκ
    (measurable_increment p s hs) (measurable_advance p s hs hD hinv gd hg).scale
    (hs.trial.sub_const xstar) he (integrable_norm_of_square μ _ he hi)
  · intro x
    constructor
    · exact (HessianAdaptiveCubicWeights.increment_pos p (s x) hD (hinv x).scale
        (hinv x).iteration (hinv x).weight_pos).le
    · simpa only [ht] using HessianAdaptiveCubicWeights.increment_upper_bound p (s x) hD
        (hinv x).scale (hinv x).iteration
  · exact fun x => hdiam _ (hinv x).trial _ hx
  · exact fun x => (hscale x).trans (advance_scale_ge p (s x) (gd x) hD (hinv x))

lemma integrable_linear_square {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) (a : X → ℝ) (v e : X → E) (B D : ℝ)
    (ha : Measurable a) (hv : Measurable v) (he : Measurable e)
    (hie : Integrable (fun x => ‖e x‖ ^ 2) μ)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ B) (hvb : ∀ x, ‖v x‖ ≤ D) :
    Integrable (fun x => (-a x * ⟪v x, e x⟫) ^ 2) μ := by
  apply integrable_square_of_bound μ _ (fun x => (B * D) ^ 2 * ‖e x‖ ^ 2)
    (ha.neg.mul (hv.inner he)) (hie.const_mul _)
  intro x
  have hb := normalized_linear_bound (v x) (e x) (hab x).1 (hab x).2 (hvb x)
    (show (0 : ℝ) < 1 by norm_num) (le_refl (1 : ℝ))
  simp only [div_one] at hb
  have hsq := mul_self_le_mul_self (abs_nonneg (-a x * ⟪v x, e x⟫)) hb
  simpa only [← sq, sq_abs, mul_pow, Pi.mul_apply, Pi.neg_apply] using hsq

lemma expected_movement_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F V κ noise : ℕ → X → ℝ) (D : ℝ)
    (hκ : ∀ n x, 0 < κ n x) (hmono : ∀ n x, κ n x ≤ κ (n + 1) x)
    (hF : ∀ n x, 0 ≤ F n x) (hV : ∀ n x, V n x ≤ D ^ 2)
    (hinit : ∀ x, F 0 x ≤ D ^ 2 / 2)
    (hstep : ∀ n x, F (n + 1) x + (κ n x / κ (n + 1) x) / 2 * V n x ≤
      F n x + (7 / 2) * D ^ 2 * (1 - κ n x / κ (n + 1) x) + noise n x)
    (N : ℕ) (hiV : ∀ n < N, Integrable (V n) μ) (hiNoise : ∀ n < N, Integrable (noise n) μ)
    (hNoise : ∀ n < N, (∫ x, noise n x ∂μ) ≤ D ^ 2 / (n + 1))
    (hiLog : Integrable (fun x => Real.log (κ N x) - Real.log (κ 0 x)) μ) :
    (∫ x, ∑ n ∈ Finset.range N, V n x ∂μ) ≤
      D ^ 2 + 8 * D ^ 2 * (∫ x, Real.log (κ N x) - Real.log (κ 0 x) ∂μ) +
        2 * D ^ 2 * ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) := by
  have hVsum : Integrable (fun x => ∑ n ∈ Finset.range N, V n x) μ :=
    integrable_finsetSum _ (fun n hn => hiV n (Finset.mem_range.mp hn))
  have hNsum : Integrable (fun x => ∑ n ∈ Finset.range N, noise n x) μ :=
    integrable_finsetSum _ (fun n hn => hiNoise n (Finset.mem_range.mp hn))
  have hright := ((integrable_const (D ^ 2)).add (hiLog.const_mul (8 * D ^ 2))).add
    (hNsum.const_mul 2)
  have hp (x : X) : (∑ n ∈ Finset.range N, V n x) ≤ D ^ 2 +
      8 * D ^ 2 * (Real.log (κ N x) - Real.log (κ 0 x)) +
      2 * ∑ n ∈ Finset.range N, noise n x := by
    have h := movement_telescope (fun n => F n x) (fun n => V n x)
      (fun n => κ n x) (fun n => noise n x) D (fun n => hκ n x)
      (fun n => hmono n x) (fun n => hF n x) (fun n => hV n x) (fun n => hstep n x) N
    linarith [hinit x]
  have hi := integral_mono hVsum hright hp
  change (∫ x, ∑ n ∈ Finset.range N, V n x ∂μ) ≤
    (∫ x, D ^ 2 + 8 * D ^ 2 * (Real.log (κ N x) - Real.log (κ 0 x)) +
      2 * (∑ n ∈ Finset.range N, noise n x) ∂μ) at hi
  rw [integral_add
    (f := fun x => D ^ 2 + 8 * D ^ 2 * (Real.log (κ N x) - Real.log (κ 0 x)))
    (g := fun x => 2 * ∑ n ∈ Finset.range N, noise n x)
    ((integrable_const _).add (hiLog.const_mul _)) (hNsum.const_mul _),
    integral_add (f := fun _ => D ^ 2)
    (g := fun x => 8 * D ^ 2 * (Real.log (κ N x) - Real.log (κ 0 x)))
    (integrable_const _) (hiLog.const_mul _)] at hi
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at hi
  rw [integral_finsetSum _ (fun n hn => hiNoise n (Finset.mem_range.mp hn))] at hi
  have hsum := Finset.sum_le_sum (s := Finset.range N)
    (fun n hn => hNoise n (Finset.mem_range.mp hn))
  have hid : (∑ n ∈ Finset.range N, D ^ 2 / ((n : ℝ) + 1)) =
      D ^ 2 * ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    simp only [mul_one_div]
  rw [hid] at hsum
  linarith

lemma integral_log_scale_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → ℝ) (κ0 : ℝ)
    (hκ0 : 0 < κ0) (hκ : Measurable κ) (hlower : ∀ x, κ0 ≤ κ x)
    (hi : Integrable (fun x => κ x ^ 2) μ) :
    Integrable (fun x => Real.log (κ x) - Real.log κ0) μ ∧
      (∫ x, Real.log (κ x) - Real.log κ0 ∂μ) ≤
        (1 / 2) * Real.log ((∫ x, κ x ^ 2 ∂μ) / κ0 ^ 2) := by
  have hpos (x : X) : 0 < κ x := hκ0.trans_le (hlower x)
  have hone (x : X) : 1 ≤ κ x ^ 2 / κ0 ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hκ0)).2
    nlinarith [hlower x]
  have hb := integral_log_bound μ (fun x => κ x ^ 2 / κ0 ^ 2)
    ((hκ.pow_const 2).div_const _) (hi.div_const _) hone
  have he (x : X) : Real.log (κ x ^ 2 / κ0 ^ 2) =
      2 * (Real.log (κ x) - Real.log κ0) := by
    rw [Real.log_div (ne_of_gt (sq_pos_of_pos (hpos x))) (ne_of_gt (sq_pos_of_pos hκ0)),
      Real.log_pow, Real.log_pow]
    norm_num
    ring
  have hid (x : X) : Real.log (κ x) - Real.log κ0 =
      (1 / 2) * Real.log (κ x ^ 2 / κ0 ^ 2) := by rw [he]; ring
  have hlog : Integrable (fun x => Real.log (κ x) - Real.log κ0) μ := by
    simpa only [← hid] using hb.1.const_mul (1 / 2)
  refine ⟨hlog, ?_⟩
  have heint : (∫ x, Real.log (κ x ^ 2 / κ0 ^ 2) ∂μ) =
      2 * (∫ x, Real.log (κ x) - Real.log κ0 ∂μ) := by
    simp only [he, integral_const_mul]
  rw [heint, integral_div] at hb
  linarith [hb.2]

lemma model_normalized_noise_integrable {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (n : ℕ)
    (hi : Integrable (fun ξ => ‖g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)) -
      gradient f (queryPoint (modelAt p g H ξ n))‖ ^ 2) P) :
    Integrable (fun ξ => normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))) P := by
  let s := fun ξ => modelAt p g H ξ n
  let gd := fun ξ => g (queryPoint (s ξ)) (ξ (3 * n + 2))
  have hm : MeasurableState p s :=
    measurable_modelAt p hD hρ hσ hx g H hg hH hPSD (fun k (ξ : ℕ → Ω) => ξ k)
      (fun k => measurable_pi_apply k) n
  have hgd : Measurable gd :=
    hg.comp ((measurable_queryPoint p s hm).prodMk (measurable_pi_apply _))
  have hκ : 0 < 2 * p.ρ + p.σg / p.D ^ 2 := by positivity
  exact integrable_step_normalized_noise p P s gd f xstar (n + 1) _ hm hgd hdiff hD
    (fun ξ => modelAt_invariant p g H ξ hD hρ hσ hx n) hxstar hdiam
    (fun ξ => roundState_iteration p g H ξ n) hκ
    (fun ξ => round_scale_lower_bound p g H ξ hD hρ hσ hx n) hi

lemma model_expected_movement {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hmin : IsMinOn f p.C xstar)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (N : ℕ)
    (hiNoise : ∀ n < N, Integrable (fun ξ => normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))) P)
    (hbNoise : ∀ n < N, (∫ ξ, normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) ∂P) ≤ p.D ^ 2 / (n + 1))
    (hiLog : Integrable (fun ξ => Real.log (roundState p g H ξ N).scale -
      Real.log (2 * p.ρ + p.σg / p.D ^ 2)) P) :
    (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤
      p.D ^ 2 + 8 * p.D ^ 2 * (∫ ξ, Real.log (roundState p g H ξ N).scale -
        Real.log (2 * p.ρ + p.σg / p.D ^ 2) ∂P) +
      2 * p.D ^ 2 * ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) := by
  let S := fun n ξ => modelAt p g H ξ n
  let K := fun n ξ => (roundState p g H ξ n).scale
  let F := fun n ξ => energy p f xstar (roundState p g H ξ n) / K n ξ
  let V := fun n ξ => movement p (S n ξ)
  let noise := fun n ξ => normalizedNoise p f xstar (S n ξ)
    (g (queryPoint (S n ξ)) (ξ (3 * n + 2)))
  have hinv (n : ℕ) (ξ : ℕ → Ω) := roundState_invariant p g H ξ hD hρ hσ hx n
  have hsinv (n : ℕ) (ξ : ℕ → Ω) := modelAt_invariant p g H ξ hD hρ hσ hx n
  have hK (n : ℕ) (ξ : ℕ → Ω) : 0 < K n ξ := (hinv n ξ).scale
  have hmono (n : ℕ) (ξ : ℕ → Ω) : K n ξ ≤ K (n + 1) ξ :=
    advance_scale_ge p (S n ξ) _ hD (hsinv n ξ)
  have hF (n : ℕ) (ξ : ℕ → Ω) : 0 ≤ F n ξ :=
    div_nonneg (energy_nonneg p f xstar _ (hinv n ξ) hmin) (hK n ξ).le
  have hV (n : ℕ) (ξ : ℕ → Ω) : V n ξ ≤ p.D ^ 2 :=
    (movement_bounds p (S n ξ) hD (hsinv n ξ) hdiam).2
  have hinit (ξ : ℕ → Ω) : F 0 ξ ≤ p.D ^ 2 / 2 := by
    have hκ := hK 0 ξ
    have hd := hdiam p.x0 hx xstar hxstar
    have he : F 0 ξ = ‖p.x0 - xstar‖ ^ 2 / 2 := by
      dsimp [F, K, roundState, initial, energy]
      field_simp
      ring
    rw [he]
    nlinarith [norm_nonneg (p.x0 - xstar)]
  have hstep (n : ℕ) (ξ : ℕ → Ω) : F (n + 1) ξ + (K n ξ / K (n + 1) ξ) / 2 * V n ξ ≤
      F n ξ + (7 / 2) * p.D ^ 2 * (1 - K n ξ / K (n + 1) ξ) + noise n ξ := by
    have hpsd : IsPSD (S n ξ).modelHessian :=
      hPSD _ (center_mem p _ (hinv n ξ)) _
    have hb := normalized_step_energy p (S n ξ)
      (g (queryPoint (S n ξ)) (ξ (3 * n + 2))) xstar f hf hgrad hD (hsinv n ξ)
      hxstar hmin hpsd (LongTails.Proofs.HessianAdaptiveCubicExecution.modelAt_trial p g H ξ n) hdiam
    have hES : energy p f xstar (modelAt p g H ξ n) = energy p f xstar (roundState p g H ξ n) := rfl
    have hKS : (modelAt p g H ξ n).scale = (roundState p g H ξ n).scale := rfl
    simpa only [F, K, V, noise, S, normalizedNoise, dualNoise, real_inner_comm,
      LongTails.Proofs.HessianAdaptiveCubicExecution.roundState_succ_modelAt, hES, hKS] using hb
  have hiV (n : ℕ) (_hn : n < N) : Integrable (V n) P :=
    integrable_movement p P (S n)
      (measurable_modelAt p hD hρ hσ hx g H hg hH hPSD (fun k (ξ : ℕ → Ω) => ξ k)
        (fun k => measurable_pi_apply k) n) hD (hsinv n) hdiam
  exact expected_movement_sum P F V K noise p.D hK hmono hF hV hinit hstep N hiV hiNoise hbNoise hiLog

lemma sum_successor_powers (N k : ℕ) :
    (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ k) ≤ (N : ℝ) ^ (k + 1) := by
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (N : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show n + 1 ≤ N from Nat.succ_le_of_lt (Finset.mem_range.mp hn))
    _ = _ := by simp [pow_succ]; ring

lemma scale_moment_telescope (S V : ℕ → ℝ) (D σg σh ρ : ℝ) (hD : 0 < D)
    (hstep : ∀ n, S (n + 1) ≤ S n +
      8 * ((n : ℝ) + 1) ^ 5 * σg ^ 2 / D ^ 4 +
      4 * ((n : ℝ) + 1) ^ 2 * σh ^ 2 / D ^ 2 + ρ ^ 2 * V n / D ^ 2 +
      (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2 - (σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2)
    (N : ℕ) :
    S N ≤ S 0 + 9 * σg ^ 2 * ((N : ℝ) + 1) ^ 6 / D ^ 4 +
      4 * σh ^ 2 * (N : ℝ) ^ 3 / D ^ 2 + ρ ^ 2 * (∑ n ∈ Finset.range N, V n) / D ^ 2 := by
  have hsum : ∀ N, S N ≤ S 0 +
      8 * σg ^ 2 / D ^ 4 * (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 5) +
      4 * σh ^ 2 / D ^ 2 * (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 2) +
      ρ ^ 2 / D ^ 2 * (∑ n ∈ Finset.range N, V n) +
      (σg * ((N : ℝ) + 1) ^ 3 / D ^ 2) ^ 2 - (σg / D ^ 2) ^ 2 := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      have h := hstep n
      have he : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      rw [he]
      simp only [div_eq_mul_inv] at h ih ⊢
      nlinarith only [h, ih]
  have hg := mul_le_mul_of_nonneg_left (sum_successor_powers N 5)
    (show 0 ≤ 8 * σg ^ 2 / D ^ 4 by positivity)
  have hh := mul_le_mul_of_nonneg_left (sum_successor_powers N 2)
    (show 0 ≤ 4 * σh ^ 2 / D ^ 2 by positivity)
  have hp : (N : ℝ) ^ 6 ≤ ((N : ℝ) + 1) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (by linarith) 6
  have hgp := mul_le_mul_of_nonneg_left hp (show 0 ≤ 8 * σg ^ 2 / D ^ 4 by positivity)
  have hf : (σg * ((N : ℝ) + 1) ^ 3 / D ^ 2) ^ 2 =
      σg ^ 2 * ((N : ℝ) + 1) ^ 6 / D ^ 4 := by ring
  have hs := hsum N
  rw [hf] at hs
  norm_num only [show 5 + 1 = 6 by rfl, show 2 + 1 = 3 by rfl] at hg hh
  have hzero := sq_nonneg (σg / D ^ 2)
  simp only [div_eq_mul_inv] at hg hh hgp hs hzero ⊢
  nlinarith only [hg, hh, hgp, hs, hzero]

lemma integral_four_linear {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f₁ f₂ f₃ f₄ : X → ℝ) (a b c d : ℝ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) :
    (∫ x, a * f₁ x + b * f₂ x + c * f₃ x + d * f₄ x ∂μ) =
      a * (∫ x, f₁ x ∂μ) + b * (∫ x, f₂ x ∂μ) + c * (∫ x, f₃ x ∂μ) + d * (∫ x, f₄ x ∂μ) := by
  rw [integral_add (f := fun x => a * f₁ x + b * f₂ x + c * f₃ x)
      (g := fun x => d * f₄ x)
      (((h₁.const_mul a).add (h₂.const_mul b)).add (h₃.const_mul c)) (h₄.const_mul d),
    integral_add (f := fun x => a * f₁ x + b * f₂ x) (g := fun x => c * f₃ x)
      ((h₁.const_mul a).add (h₂.const_mul b)) (h₃.const_mul c),
    integral_add (f := fun x => a * f₁ x) (g := fun x => b * f₂ x)
      (h₁.const_mul a) (h₂.const_mul b)]
  simp only [integral_const_mul]

lemma expected_scale_step {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (K Knext eg₁ eg₂ eh V : X → ℝ) (D σg σh ρ : ℝ) (n : ℕ) (hD : 0 < D)
    (hiK : Integrable K μ) (hiKnext : Integrable Knext μ)
    (hi₁ : Integrable eg₁ μ) (hi₂ : Integrable eg₂ μ) (hih : Integrable eh μ) (hiV : Integrable V μ)
    (h₁ : (∫ x, eg₁ x ∂μ) ≤ σg ^ 2) (h₂ : (∫ x, eg₂ x ∂μ) ≤ σg ^ 2)
    (hh : (∫ x, eh x ∂μ) ≤ σh ^ 2)
    (hstep : ∀ x, Knext x ≤ K x +
      (4 * (((n : ℝ) + 1) ^ 5 / D ^ 2) * eg₁ x +
      4 * (((n : ℝ) + 1) ^ 5 / D ^ 2) * eg₂ x + 4 * ((n : ℝ) + 1) ^ 2 * eh x + ρ ^ 2 * V x) / D ^ 2 +
      (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2 - (σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2) :
    (∫ x, Knext x ∂μ) ≤ (∫ x, K x ∂μ) +
      8 * ((n : ℝ) + 1) ^ 5 * σg ^ 2 / D ^ 4 +
      4 * ((n : ℝ) + 1) ^ 2 * σh ^ 2 / D ^ 2 + ρ ^ 2 * (∫ x, V x ∂μ) / D ^ 2 +
      (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2 - (σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2 := by
  let a := 4 * (((n : ℝ) + 1) ^ 5 / D ^ 2)
  let b := 4 * ((n : ℝ) + 1) ^ 2
  let C := fun x => a * eg₁ x + a * eg₂ x + b * eh x + ρ ^ 2 * V x
  have hiC : Integrable C μ := (((hi₁.const_mul a).add (hi₂.const_mul a)).add
    (hih.const_mul b)).add (hiV.const_mul (ρ ^ 2))
  have hiR := ((hiK.add (hiC.div_const (D ^ 2))).add
    (integrable_const ((σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2))).sub
    (integrable_const ((σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2))
  have hi := integral_mono hiKnext hiR hstep
  change (∫ x, Knext x ∂μ) ≤ (∫ x, K x + C x / D ^ 2 +
    (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2 - (σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2 ∂μ) at hi
  rw [integral_sub (f := fun x => K x + C x / D ^ 2 + (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2)
      (g := fun _ => (σg * ((n : ℝ) + 1) ^ 3 / D ^ 2) ^ 2)
      ((hiK.add (hiC.div_const _)).add (integrable_const _)) (integrable_const _),
    integral_add (f := fun x => K x + C x / D ^ 2)
      (g := fun _ => (σg * ((n : ℝ) + 2) ^ 3 / D ^ 2) ^ 2)
      (hiK.add (hiC.div_const _)) (integrable_const _),
    integral_add (f := K) (g := fun x => C x / D ^ 2) hiK (hiC.div_const _), integral_div] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hC := integral_four_linear μ eg₁ eg₂ eh V a a b (ρ ^ 2) hi₁ hi₂ hih hiV
  change (∫ x, C x ∂μ) = _ at hC
  rw [hC] at hi
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg₁ := mul_le_mul_of_nonneg_left h₁ ha
  have hg₂ := mul_le_mul_of_nonneg_left h₂ ha
  have hh' := mul_le_mul_of_nonneg_left hh hb
  have hbound : a * (∫ x, eg₁ x ∂μ) + a * (∫ x, eg₂ x ∂μ) +
      b * (∫ x, eh x ∂μ) + ρ ^ 2 * (∫ x, V x ∂μ) ≤
      2 * a * σg ^ 2 + b * σh ^ 2 + ρ ^ 2 * (∫ x, V x ∂μ) := by linarith
  have hd := div_le_div_of_nonneg_right hbound (sq_nonneg D)
  have he : (2 * a * σg ^ 2 + b * σh ^ 2 + ρ ^ 2 * (∫ x, V x ∂μ)) / D ^ 2 =
      8 * ((n : ℝ) + 1) ^ 5 * σg ^ 2 / D ^ 4 +
      4 * ((n : ℝ) + 1) ^ 2 * σh ^ 2 / D ^ 2 + ρ ^ 2 * (∫ x, V x ∂μ) / D ^ 2 := by
    dsimp [a, b]
    field_simp
    ring
  rw [he] at hd
  linarith

lemma model_scale_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (σh : ℝ)
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hhi : ∀ x ∈ p.C, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2) μ)
    (hhb : ∀ x ∈ p.C, (∫ ω, ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2 ∂μ) ≤ σh ^ 2)
    (N : ℕ) :
    (∫ ξ, (modelAt p g H ξ N).scale ^ 2 ∂P) ≤
      (2 * p.ρ + p.σg / p.D ^ 2) ^ 2 + 9 * p.σg ^ 2 * ((N : ℝ) + 1) ^ 6 / p.D ^ 4 +
      4 * σh ^ 2 * (N : ℝ) ^ 3 / p.D ^ 2 +
      p.ρ ^ 2 * (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) / p.D ^ 2 := by
  let S := fun n ξ => modelAt p g H ξ n
  let gd := fun n ξ => g (queryPoint (S n ξ)) (ξ (3 * n + 2))
  let V := fun n ξ => movement p (S n ξ)
  have hinv (n : ℕ) (ξ : ℕ → Ω) := modelAt_invariant p g H ξ hD hρ hσ hx n
  have ht (n : ℕ) (ξ : ℕ → Ω) : (S n ξ).iteration = n + 1 := roundState_iteration p g H ξ n
  have hm (n : ℕ) : MeasurableState p (S n) :=
    measurable_modelAt p hD hρ hσ hx g H hg hH hPSD (fun k (ξ : ℕ → Ω) => ξ k)
      (fun k => measurable_pi_apply k) n
  have hiK (n : ℕ) : Integrable (fun ξ => (S n ξ).scale ^ 2) P :=
    model_scale_square_integrable p μ P hIID ω0 hD hρ hσ hx hdiam f hdiff hLip
      g H hg hH hPSD σh hgi hgb hhi hhb n
  have hiV (n : ℕ) : Integrable (V n) P := integrable_movement p P (S n) (hm n) hD (hinv n) hdiam
  have hstep (n : ℕ) : (∫ ξ, (S (n + 1) ξ).scale ^ 2 ∂P) ≤
      (∫ ξ, (S n ξ).scale ^ 2 ∂P) + 8 * ((n : ℝ) + 1) ^ 5 * p.σg ^ 2 / p.D ^ 4 +
      4 * ((n : ℝ) + 1) ^ 2 * σh ^ 2 / p.D ^ 2 + p.ρ ^ 2 * (∫ ξ, V n ξ ∂P) / p.D ^ 2 +
      (p.σg * ((n : ℝ) + 2) ^ 3 / p.D ^ 2) ^ 2 - (p.σg * ((n : ℝ) + 1) ^ 3 / p.D ^ 2) ^ 2 := by
    have hd := model_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff) p.σg hgi hgb n
    have hg0 := center_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
      p.σg hgi hgb n (3 * n) le_rfl
    have hh0 := center_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => H x ω - fderiv ℝ (gradient f) x) (measurable_hessian_error p f H hH)
      σh hhi hhb n (3 * n + 1) (by omega)
    apply expected_scale_step P (fun ξ => (S n ξ).scale ^ 2) (fun ξ => (S (n + 1) ξ).scale ^ 2)
      (fun ξ => ‖gd n ξ - gradient f (queryPoint (S n ξ))‖ ^ 2)
      (fun ξ => ‖(S n ξ).modelGradient - gradient f (center (S n ξ))‖ ^ 2)
      (fun ξ => ‖(S n ξ).modelHessian - fderiv ℝ (gradient f) (center (S n ξ))‖ ^ 2)
      (V n) p.D p.σg σh p.ρ n hD (hiK n) (hiK (n + 1)) hd.1 hg0.1 hh0.1 (hiV n)
      hd.2 hg0.2 hh0.2
    intro ξ
    have hf : p.σg * ((S n ξ).iteration : ℝ) ^ 3 / p.D ^ 2 ≤ (S n ξ).scale := by
      rw [ht]
      exact roundState_scale_floor p g H ξ hρ.le n
    have hb := model_scale_square_bound p (S n ξ) (gd n ξ) f hD hσ (hinv n ξ) hf hdiff hLip
    have hn : (S (n + 1) ξ).scale = (advance p (S n ξ) (gd n ξ)).scale := rfl
    simpa only [hn, ht, Nat.cast_add, Nat.cast_one, V, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using hb
  have hb := scale_moment_telescope (fun n => ∫ ξ, (S n ξ).scale ^ 2 ∂P)
    (fun n => ∫ ξ, V n ξ ∂P) p.D p.σg σh p.ρ hD hstep N
  have hinit : (∫ ξ, (S 0 ξ).scale ^ 2 ∂P) = (2 * p.ρ + p.σg / p.D ^ 2) ^ 2 := by
    change (∫ _ξ : ℕ → Ω, (2 * p.ρ + p.σg / p.D ^ 2) ^ 2 ∂P) = _
    simp
  rw [hinit, ← integral_finsetSum _ (fun n _ => hiV n)] at hb
  exact hb

lemma self_bound_from_movement {S B c M L H : ℝ}
    (hS : 0 < S) (hc : 0 ≤ c) (hcmax : c ≤ 1 / 4) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hM : M ≤ 40 * (1 + L + H)) (hstate : S ≤ B + c * M)
    (hlog : L ≤ (1 / 2) * Real.log S) : S ≤ 2 * B + 20 * H + 34 := by
  apply logarithmic_self_bound hS
  have h₁ := mul_le_mul_of_nonneg_left hM hc
  have h₂ := mul_le_mul_of_nonneg_right hcmax (show 0 ≤ 40 * (1 + L + H) by positivity)
  nlinarith

lemma model_scale_closed_bound {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hmin : IsMinOn f p.C xstar)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (σh : ℝ)
    (hgint : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgmean : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hhi : ∀ x ∈ p.C, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2) μ)
    (hhb : ∀ x ∈ p.C, (∫ ω, ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2 ∂μ) ≤ σh ^ 2)
    (N : ℕ) :
    (∫ ξ, (modelAt p g H ξ N).scale ^ 2 ∂P) ≤
      (2 * p.ρ + p.σg / p.D ^ 2) ^ 2 *
        (36 + 20 * ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))) +
      18 * p.σg ^ 2 * ((N : ℝ) + 1) ^ 6 / p.D ^ 4 + 8 * σh ^ 2 * (N : ℝ) ^ 3 / p.D ^ 2 := by
  let κ0 := 2 * p.ρ + p.σg / p.D ^ 2
  let K := fun ξ => (modelAt p g H ξ N).scale
  let S := (∫ ξ, K ξ ^ 2 ∂P) / κ0 ^ 2
  let L := ∫ ξ, Real.log (K ξ) - Real.log κ0 ∂P
  let HN := ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))
  let M := (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) / p.D ^ 2
  let c := p.ρ ^ 2 / κ0 ^ 2
  let B := ((κ0 ^ 2 + 9 * p.σg ^ 2 * ((N : ℝ) + 1) ^ 6 / p.D ^ 4) +
    4 * σh ^ 2 * (N : ℝ) ^ 3 / p.D ^ 2) / κ0 ^ 2
  have hκ0 : 0 < κ0 := by dsimp [κ0]; positivity
  have hKl (ξ : ℕ → Ω) : κ0 ≤ K ξ := round_scale_lower_bound p g H ξ hD hρ hσ hx N
  have hmK : Measurable K := (measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) N).scale
  have hiK : Integrable (fun ξ => K ξ ^ 2) P :=
    model_scale_square_integrable p μ P hIID ω0 hD hρ hσ hx hdiam f hdiff hLip
      g H hg hH hPSD σh hgi hgb hhi hhb N
  have hlog := integral_log_scale_bound P K κ0 hκ0 hmK hKl hiK
  have hL : 0 ≤ L := integral_nonneg (fun ξ => sub_nonneg.mpr
    (Real.log_le_log hκ0 (hKl ξ)))
  have hHN : 0 ≤ HN := Finset.sum_nonneg (fun n _ => by positivity)
  have hSone : 1 ≤ S := by
    have hpoint (ξ : ℕ → Ω) : κ0 ^ 2 ≤ K ξ ^ 2 := by nlinarith [hKl ξ]
    have hb := integral_mono (integrable_const (κ0 ^ 2)) hiK hpoint
    simp only [integral_const, probReal_univ, one_smul] at hb
    exact (le_div_iff₀ (sq_pos_of_pos hκ0)).2 (by simpa using hb)
  have hnoisei (n : ℕ) : Integrable (fun ξ => normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))) P := by
    have he := (model_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
      p.σg hgi hgb n).1
    exact model_normalized_noise_integrable p P hD hρ hσ hx xstar hxstar hdiam f hdiff
      g H hg hH hPSD n he
  have hnoiseb (n : ℕ) : (∫ ξ, normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) ∂P) ≤ p.D ^ 2 / (n + 1) :=
    model_normalized_drift p μ P hIID ω0 hD hρ hσ hx xstar hxstar hdiam f hdiff
      g H hg hH hPSD hgint hgmean hgi hgb n (hnoisei n)
  have hmov := model_expected_movement p P hD hρ hσ hx xstar hxstar hdiam f hf hgrad hmin
    g H hg hH hPSD N (fun n _ => hnoisei n) (fun n _ => hnoiseb n) hlog.1
  have hM : M ≤ 40 * (1 + L + HN) := by
    apply (div_le_iff₀ (sq_pos_of_pos hD)).2
    change _ ≤ _ at hmov
    change (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤ _
    have hmov' : (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤
        p.D ^ 2 + 8 * p.D ^ 2 * L + 2 * p.D ^ 2 * HN := hmov
    nlinarith [sq_nonneg p.D]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcmax : c ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hκ0)).2
    have hl : 2 * p.ρ ≤ κ0 := by
      dsimp [κ0]
      linarith [div_nonneg hσ (sq_nonneg p.D)]
    nlinarith
  have hsraw := model_scale_moment_bound p μ P hIID ω0 hD hρ hσ hx hdiam f hdiff hLip
    g H hg hH hPSD σh hgi hgb hhi hhb N
  have hstate : S ≤ B + c * M := by
    apply (div_le_iff₀ (sq_pos_of_pos hκ0)).2
    have he : (B + c * M) * κ0 ^ 2 = κ0 ^ 2 +
        9 * p.σg ^ 2 * ((N : ℝ) + 1) ^ 6 / p.D ^ 4 + 4 * σh ^ 2 * (N : ℝ) ^ 3 / p.D ^ 2 +
        p.ρ ^ 2 * (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) / p.D ^ 2 := by
      dsimp [B, c, M]
      field_simp
    rw [he]
    exact hsraw
  have hclosed := self_bound_from_movement (lt_of_lt_of_le zero_lt_one hSone) hc hcmax hL hHN hM hstate hlog.2
  have hmul := mul_le_mul_of_nonneg_right hclosed (sq_nonneg κ0)
  have hleft : S * κ0 ^ 2 = ∫ ξ, K ξ ^ 2 ∂P := by dsimp [S]; field_simp
  have hright : (2 * B + 20 * HN + 34) * κ0 ^ 2 =
      κ0 ^ 2 * (36 + 20 * HN) + 18 * p.σg ^ 2 * ((N : ℝ) + 1) ^ 6 / p.D ^ 4 +
      8 * σh ^ 2 * (N : ℝ) ^ 3 / p.D ^ 2 := by
    dsimp [B]
    field_simp
    ring
  rw [hleft, hright] at hmul
  exact hmul

end LongTails.Proofs.HessianAdaptiveCubicStochasticBounds
