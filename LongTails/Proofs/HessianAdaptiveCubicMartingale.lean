import LongTails.Proofs.HessianAdaptiveCubicStochasticBounds
import LongTails.Proofs.MatrixOracleMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HessianAdaptiveCubicMartingale

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicWeights
open LongTails.Proofs.HessianAdaptiveCubicMeasurability
open LongTails.Proofs.HessianAdaptiveCubicMoments
open LongTails.Proofs.HessianAdaptiveCubicStochasticBounds

lemma fixed_state_noise_mean {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : State p.d) (f : Point p.d → ℝ)
    (xstar : Point p.d) (g : Point p.d → Ω → Point p.d)
    (hi : Integrable (g (queryPoint s)) μ)
    (hm : (∫ ω, g (queryPoint s) ω ∂μ) = gradient f (queryPoint s)) :
    Integrable (fun ω => dualNoise p f xstar s (g (queryPoint s) ω)) μ ∧
      (∫ ω, dualNoise p f xstar s (g (queryPoint s) ω) ∂μ) = 0 := by
  have he := centered_gradient_error p μ f g (queryPoint s) hi hm
  refine ⟨(he.1.const_inner (s.trial - xstar)).const_mul (-increment p s), ?_⟩
  unfold dualNoise
  rw [integral_const_mul, integral_inner he.1, he.2]
  simp

lemma measurable_dualNoise {X : Type*} [MeasurableSpace X] (p : Public)
    (s : X → State p.d) (gd : X → Point p.d) (f : Point p.d → ℝ) (xstar : Point p.d)
    (hs : MeasurableState p s) (hg : Measurable gd) (hf : Differentiable ℝ (gradient f)) :
    Measurable (fun x => dualNoise p f xstar (s x) (gd x)) :=
  (measurable_increment p s hs).neg.mul ((hs.trial.sub_const xstar).inner
    (hg.sub (hf.continuous.measurable.comp (measurable_queryPoint p s hs))))

lemma dual_noise_square_bound (p : Public) (s : State p.d) (gd xstar : Point p.d)
    (f : Point p.d → ℝ) (hD : 0 < p.D) (hs : Invariant p s)
    (hx : xstar ∈ p.C) (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) :
    dualNoise p f xstar s gd ^ 2 ≤
      (s.iteration : ℝ) ^ 5 * ‖gd - gradient f (queryPoint s)‖ ^ 2 := by
  have hb := normalized_linear_bound (s.trial - xstar) (gd - gradient f (queryPoint s))
    (increment_pos p s hD hs.scale hs.iteration hs.weight_pos).le
    (increment_upper_bound p s hD hs.scale hs.iteration) (hdiam _ hs.trial _ hx)
    (show (0 : ℝ) < 1 by norm_num) (le_refl (1 : ℝ))
  simp only [div_one] at hb
  have hsq := mul_self_le_mul_self (abs_nonneg (dualNoise p f xstar s gd)) hb
  have he : (((s.iteration : ℝ) ^ 2 * Real.sqrt s.iteration / p.D) * p.D *
      ‖gd - gradient f (queryPoint s)‖) ^ 2 =
      (s.iteration : ℝ) ^ 5 * ‖gd - gradient f (queryPoint s)‖ ^ 2 := by
    rw [div_mul_cancel₀ _ (ne_of_gt hD)]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  rw [← sq, sq_abs, ← sq, he] at hsq
  exact hsq

lemma step_noise_second_moment {X : Type*} [MeasurableSpace X]
    (p : Public) (μ : Measure X) (s : X → State p.d) (gd : X → Point p.d)
    (f : Point p.d → ℝ) (xstar : Point p.d) (t : ℕ)
    (hs : MeasurableState p s) (hg : Measurable gd) (hdiff : Differentiable ℝ (gradient f))
    (hD : 0 < p.D) (hinv : ∀ x, Invariant p (s x)) (hx : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D) (ht : ∀ x, (s x).iteration = t)
    (hi : Integrable (fun x => ‖gd x - gradient f (queryPoint (s x))‖ ^ 2) μ)
    (hb : (∫ x, ‖gd x - gradient f (queryPoint (s x))‖ ^ 2 ∂μ) ≤ p.σg ^ 2) :
    Integrable (fun x => dualNoise p f xstar (s x) (gd x) ^ 2) μ ∧
      (∫ x, dualNoise p f xstar (s x) (gd x) ^ 2 ∂μ) ≤ (t : ℝ) ^ 5 * p.σg ^ 2 := by
  have hpoint (x : X) : dualNoise p f xstar (s x) (gd x) ^ 2 ≤
      (t : ℝ) ^ 5 * ‖gd x - gradient f (queryPoint (s x))‖ ^ 2 := by
    simpa only [ht] using dual_noise_square_bound p (s x) (gd x) xstar f hD (hinv x) hx hdiam
  have hni := HessianAdaptiveCubicNormalization.integrable_square_of_bound μ _ _
    (measurable_dualNoise p s gd f xstar hs hg hdiff) (hi.const_mul ((t : ℝ) ^ 5)) hpoint
  refine ⟨hni, ?_⟩
  have hi' := integral_mono hni (hi.const_mul ((t : ℝ) ^ 5)) hpoint
  rw [integral_const_mul] at hi'
  exact hi'.trans (mul_le_mul_of_nonneg_left hb (by positivity))

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex
open LongTails.Proofs.HessianAdaptiveCubicExecution

lemma fresh_prefix_zero {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ)
    (F : (Fin n → Ω) × Ω → ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω => F ((fun i : Fin n => ξ i ω), ξ n ω)) P)
    (hzero : ∀ u, (∫ ω, F (u, ω) ∂p) = 0) :
    (∫ ω, F ((fun i : Fin n => ξ i ω), ξ n ω) ∂P) = 0 := by
  have hp : Integrable F ((Measure.pi fun _ : Fin n => p).prod p) :=
    ((prefix_current_law h n).integrable_comp hF.aestronglyMeasurable).mp hi
  rw [fresh_prefix_integral h n F hp]
  simp only [hzero, integral_zero]

noncomputable def roundNoise {Ω : Type*} (p : Public) (f : Point p.d → ℝ)
    (xstar : Point p.d) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ) (ξ : ℕ → Ω) : ℝ :=
  dualNoise p f xstar (modelAt p g H ξ n) (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))

noncomputable def noiseSum {Ω : Type*} (p : Public) (f : Point p.d → ℝ)
    (xstar : Point p.d) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ) (ξ : ℕ → Ω) : ℝ :=
  ∑ k ∈ Finset.range n, roundNoise p f xstar g H k ξ

lemma roundNoise_congr {Ω : Type*} (p : Public) (f : Point p.d → ℝ)
    (xstar : Point p.d) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ) (ξ ζ : ℕ → Ω)
    (hξ : ∀ k < 3 * n + 3, ξ k = ζ k) :
    roundNoise p f xstar g H n ξ = roundNoise p f xstar g H n ζ := by
  have hm := modelAt_congr p g H n ξ ζ (fun k hk => hξ k (by omega))
  simp only [roundNoise, hm, hξ (3 * n + 2) (by omega)]

lemma noiseSum_congr {Ω : Type*} (p : Public) (f : Point p.d → ℝ)
    (xstar : Point p.d) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ) (ξ ζ : ℕ → Ω)
    (hξ : ∀ k < 3 * n, ξ k = ζ k) :
    noiseSum p f xstar g H n ξ = noiseSum p f xstar g H n ζ := by
  apply Finset.sum_congr rfl
  intro k hk
  apply roundNoise_congr p f xstar g H k ξ ζ
  intro i hi
  have hk' := Finset.mem_range.mp hk
  exact hξ i (by omega)

lemma measurable_roundNoise {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f)) (xstar : Point p.d)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (n : ℕ) :
    Measurable (roundNoise p f xstar g H n) := by
  have hm := measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) n
  exact measurable_dualNoise p _ _ f xstar hm
    (hg.comp ((measurable_queryPoint p _ hm).prodMk (measurable_pi_apply _))) hdiff

lemma measurable_noiseSum {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f)) (xstar : Point p.d)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (n : ℕ) :
    Measurable (noiseSum p f xstar g H n) :=
  Finset.measurable_sum _ (fun k _ => measurable_roundNoise p hD hρ hσ hx f hdiff xstar g H hg hH hPSD k)

lemma noiseSum_cross_zero {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f)) (xstar : Point p.d)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (hgi : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgm : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x) (n : ℕ)
    (hi : Integrable (fun ξ => noiseSum p f xstar g H n ξ * roundNoise p f xstar g H n ξ) P) :
    (∫ ξ, noiseSum p f xstar g H n ξ * roundNoise p f xstar g H n ξ ∂P) = 0 := by
  let ext := prefixExtend ω0 (3 * n + 2)
  let s := fun u : Fin (3 * n + 2) → Ω => modelAt p g H (ext u) n
  let past := fun u : Fin (3 * n + 2) → Ω => noiseSum p f xstar g H n (ext u)
  let F := fun z : (Fin (3 * n + 2) → Ω) × Ω =>
    past z.1 * dualNoise p f xstar (s z.1) (g (queryPoint (s z.1)) z.2)
  have hs : MeasurableState p s :=
    measurable_modelAt p hD hρ hσ hx g H hg hH hPSD (fun k u => ext u k)
      (fun k => (measurable_pi_apply k).comp (measurable_prefixExtend ω0 (3 * n + 2))) n
  have hpast : Measurable past := (measurable_noiseSum p hD hρ hσ hx f hdiff xstar g H hg hH hPSD n).comp
    (measurable_prefixExtend ω0 (3 * n + 2))
  have hm : MeasurableState p (fun z : (Fin (3 * n + 2) → Ω) × Ω => s z.1) :=
    ⟨hs.iteration.comp measurable_fst, hs.phase.comp measurable_fst,
      hs.weight.comp measurable_fst, hs.point.comp measurable_fst, hs.dual.comp measurable_fst,
      hs.scale.comp measurable_fst, hs.modelGradient.comp measurable_fst,
      hs.modelHessian.comp measurable_fst, hs.trial.comp measurable_fst⟩
  have hF : Measurable F := (hpast.comp measurable_fst).mul
    (measurable_dualNoise p _ _ f xstar hm
      (hg.comp ((measurable_queryPoint p _ hm).prodMk measurable_snd)) hdiff)
  have hsf (ξ : ℕ → Ω) : s (fun i => ξ i) = modelAt p g H ξ n :=
    modelAt_congr p g H n _ _ (fun k hk => by simp [ext, prefixExtend, hk])
  have hpf (ξ : ℕ → Ω) : past (fun i => ξ i) = noiseSum p f xstar g H n ξ :=
    noiseSum_congr p f xstar g H n _ _ (fun k hk => by
      simp [ext, prefixExtend, show k < 3 * n + 2 by omega])
  have hiF : Integrable (fun ξ : ℕ → Ω => F ((fun i => ξ i), ξ (3 * n + 2))) P := by
    simpa only [F, hsf, hpf, roundNoise] using hi
  have hzero (u : Fin (3 * n + 2) → Ω) : (∫ ω, F (u, ω) ∂μ) = 0 := by
    have hq := queryPoint_mem p (s u) (modelAt_invariant p g H _ hD hρ hσ hx n)
    have hz := (fixed_state_noise_mean p μ (s u) f xstar g (hgi _ hq) (hgm _ hq)).2
    dsimp only [F]
    rw [integral_const_mul, hz, mul_zero]
  have hz := fresh_prefix_zero hIID (3 * n + 2) F hF hiF hzero
  simpa only [F, hsf, hpf, roundNoise] using hz

lemma noiseSum_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f)) (xstar : Point p.d)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (hgi : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgm : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hni : ∀ n, Integrable (fun ξ => roundNoise p f xstar g H n ξ ^ 2) P)
    (hnb : ∀ n, (∫ ξ, roundNoise p f xstar g H n ξ ^ 2 ∂P) ≤ ((n : ℝ) + 1) ^ 5 * p.σg ^ 2)
    (N : ℕ) :
    Integrable (fun ξ => noiseSum p f xstar g H N ξ ^ 2) P ∧
      (∫ ξ, noiseSum p f xstar g H N ξ ^ 2 ∂P) ≤ p.σg ^ 2 * (N : ℝ) ^ 6 := by
  have hmem (n : ℕ) : MemLp (roundNoise p f xstar g H n) 2 P :=
    (memLp_two_iff_integrable_sq
      (measurable_roundNoise p hD hρ hσ hx f hdiff xstar g H hg hH hPSD n).aestronglyMeasurable).2 (hni n)
  have hsmem (n : ℕ) : MemLp (noiseSum p f xstar g H n) 2 P :=
    memLp_finsetSum _ (fun k _ => hmem k)
  have heq : ∀ n, (∫ ξ, noiseSum p f xstar g H n ξ ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (∫ ξ, roundNoise p f xstar g H k ξ ^ 2 ∂P) := by
    intro n
    induction n with
    | zero => simp [noiseSum]
    | succ n ih =>
      have hc := noiseSum_cross_zero p μ P hIID ω0 hD hρ hσ hx f hdiff xstar
        g H hg hH hPSD hgi hgm n ((hsmem n).integrable_mul (hmem n))
      have hadd := MatrixOracleMoments.second_moment_add_of_orthogonal (hsmem n) (hmem n) hc
      have hstep (ξ : ℕ → Ω) : noiseSum p f xstar g H (n + 1) ξ =
          noiseSum p f xstar g H n ξ + roundNoise p f xstar g H n ξ := by
        simp only [noiseSum, Finset.sum_range_succ]
      simp only [hstep]
      rw [hadd, ih, Finset.sum_range_succ]
  refine ⟨(hsmem N).integrable_sq, ?_⟩
  rw [heq]
  have hb := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hnb n)
  rw [← Finset.sum_mul] at hb
  have hp := mul_le_mul_of_nonneg_right (sum_successor_powers N 5) (sq_nonneg p.σg)
  simpa only [show 5 + 1 = 6 by rfl, mul_comm] using hb.trans hp


lemma model_roundNoise_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (n : ℕ) :
    Integrable (fun ξ => roundNoise p f xstar g H n ξ ^ 2) P ∧
      (∫ ξ, roundNoise p f xstar g H n ξ ^ 2 ∂P) ≤ ((n : ℝ) + 1) ^ 5 * p.σg ^ 2 := by
  have he := model_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
    (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
    p.σg hgi hgb n
  have hs := measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) n
  have hgd : Measurable (fun ξ => g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) :=
    hg.comp ((measurable_queryPoint p _ hs).prodMk (measurable_pi_apply _))
  have hb := step_noise_second_moment p P (fun ξ => modelAt p g H ξ n)
    (fun ξ => g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) f xstar (n + 1)
    hs hgd hdiff hD (fun ξ => modelAt_invariant p g H ξ hD hρ hσ hx n)
    hxstar hdiam (fun ξ => roundState_iteration p g H ξ n) he.1 he.2
  simpa only [roundNoise, Nat.cast_add, Nat.cast_one] using hb

end LongTails.Proofs.HessianAdaptiveCubicMartingale
