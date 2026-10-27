import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.HessianAdaptiveCubicMeasurability
import LongTails.Proofs.HessianAdaptiveCubicExecution
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import LongTails.Proofs.HessianAdaptiveCubicNormalization

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HessianAdaptiveCubicMoments

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma prefix_current_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ) :
    MeasurePreserving (fun ω => ((fun i : Fin n => ξ i ω), ξ n ω))
      P ((Measure.pi fun _ : Fin n => p).prod p) := by
  have hev : MeasurePreserving (fun z : ℕ → Ω => z 0)
      (Measure.infinitePi fun _ : ℕ => p) p :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod hev).comp
    (h.prefix_tail_law n)
  simpa only [Function.comp_def, Prod.map, id_eq, Nat.add_zero] using hp

lemma nonnegative_product_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [SFinite Q]
    (F : Ω × Ξ → ℝ) (B : ℝ) (hF : Measurable F) (hFpos : ∀ z, 0 ≤ F z)
    (hsections : ∀ ω, Integrable (fun ξ => F (ω, ξ)) Q)
    (hbound : ∀ ω, (∫ ξ, F (ω, ξ) ∂Q) ≤ B) :
    Integrable F (P.prod Q) ∧ (∫ z, F z ∂P.prod Q) ≤ B := by
  have hm := hF.stronglyMeasurable.integral_prod_right' (ν := Q)
  have hi : Integrable (fun ω => ∫ ξ, F (ω, ξ) ∂Q) P := by
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ξ => hFpos (ω, ξ)))]
    exact hbound ω
  have hp : Integrable F (P.prod Q) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hsections, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFpos _)] using hi
  refine ⟨hp, ?_⟩
  rw [integral_prod _ hp]
  exact (integral_mono hi (integrable_const B) hbound).trans_eq (by simp)

lemma preserving_integral {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Measure Ω} {Q : Measure Ξ}
    {f : Ω → Ξ} (hf : MeasurePreserving f P Q) {F : Ξ → E}
    (hF : AEStronglyMeasurable F Q) : (∫ ω, F (f ω) ∂P) = ∫ z, F z ∂Q := by
  have hm : AEStronglyMeasurable F (P.map f) := hf.map_eq.symm ▸ hF
  have hi := integral_map hf.measurable.aemeasurable hm
  rw [hf.map_eq] at hi
  exact hi.symm

lemma fresh_prefix_nonnegative_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ)
    (F : (Fin n → Ω) × Ω → ℝ) (B : ℝ) (hF : Measurable F) (hpos : ∀ z, 0 ≤ F z)
    (hsections : ∀ u, Integrable (fun ω => F (u, ω)) p)
    (hbound : ∀ u, (∫ ω, F (u, ω) ∂p) ≤ B) :
    Integrable (fun ω => F ((fun i : Fin n => ξ i ω), ξ n ω)) P ∧
      (∫ ω, F ((fun i : Fin n => ξ i ω), ξ n ω) ∂P) ≤ B := by
  have hp := nonnegative_product_bound (Measure.pi fun _ : Fin n => p) p F B hF hpos hsections hbound
  have hlaw := prefix_current_law h n
  refine ⟨hlaw.integrable_comp_of_integrable hp.1, ?_⟩
  rw [preserving_integral hlaw hF.aestronglyMeasurable]
  exact hp.2

def prefixExtend {Ω : Type*} (ω0 : Ω) (n : ℕ) (u : Fin n → Ω) (i : ℕ) : Ω :=
  if hi : i < n then u ⟨i, hi⟩ else ω0

lemma measurable_prefixExtend {Ω : Type*} [MeasurableSpace Ω] (ω0 : Ω) (n : ℕ) :
    Measurable (prefixExtend ω0 n) := by
  apply Measurable.of_eval
  intro i
  unfold prefixExtend
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma factor_prefix {Ω Y : Type*} (ω0 : Ω) (n : ℕ) (F : (ℕ → Ω) → Y)
    (hF : ∀ ξ ζ, (∀ i < n, ξ i = ζ i) → F ξ = F ζ) (ξ : ℕ → Ω) :
    F ξ = F (prefixExtend ω0 n (fun i => ξ i)) := by
  apply hF
  intro i hi
  simp only [prefixExtend, dite_eq_left hi]

lemma fresh_prefix_integral {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ)
    (F : (Fin n → Ω) × Ω → E) (hF : Integrable F ((Measure.pi fun _ : Fin n => p).prod p)) :
    (∫ ω, F ((fun i : Fin n => ξ i ω), ξ n ω) ∂P) =
      ∫ u, ∫ ω, F (u, ω) ∂p ∂Measure.pi (fun _ : Fin n => p) := by
  rw [preserving_integral (prefix_current_law h n) hF.aestronglyMeasurable, integral_prod _ hF]

lemma fresh_prefix_square_moment {Ω Ξ U V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace U] [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ)
    (q : (Fin n → Ω) → U) (e : U → Ω → V) (σ : ℝ)
    (hq : Measurable q) (he : Measurable (Function.uncurry e))
    (hsections : ∀ u, Integrable (fun ω => ‖e (q u) ω‖ ^ 2) p)
    (hbound : ∀ u, (∫ ω, ‖e (q u) ω‖ ^ 2 ∂p) ≤ σ ^ 2) :
    Integrable (fun ω => ‖e (q (fun i : Fin n => ξ i ω)) (ξ n ω)‖ ^ 2) P ∧
      (∫ ω, ‖e (q (fun i : Fin n => ξ i ω)) (ξ n ω)‖ ^ 2 ∂P) ≤ σ ^ 2 := by
  apply fresh_prefix_nonnegative_bound h n
    (fun z => ‖e (q z.1) z.2‖ ^ 2) (σ ^ 2)
  · exact ((he.comp ((hq.comp measurable_fst).prodMk measurable_snd)).norm).pow_const 2
  · intro z
    positivity
  · exact hsections
  · exact hbound

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicMeasurability
open LongTails.Proofs.HessianAdaptiveCubicExecution

lemma model_query_square_moment {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (e : Point p.d → Ω → V) (he : Measurable (Function.uncurry e)) (σ : ℝ)
    (hei : ∀ x ∈ p.C, Integrable (fun ω => ‖e x ω‖ ^ 2) μ)
    (heb : ∀ x ∈ p.C, (∫ ω, ‖e x ω‖ ^ 2 ∂μ) ≤ σ ^ 2) (n : ℕ) :
    Integrable (fun ξ => ‖e (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))‖ ^ 2) P ∧
      (∫ ξ, ‖e (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))‖ ^ 2 ∂P) ≤ σ ^ 2 := by
  let q : (Fin (3 * n + 2) → Ω) → Point p.d := fun u =>
    queryPoint (modelAt p g H (prefixExtend ω0 (3 * n + 2) u) n)
  have hm := measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k u => prefixExtend ω0 (3 * n + 2) u k)
    (fun k => (measurable_pi_apply k).comp (measurable_prefixExtend ω0 (3 * n + 2))) n
  have hq : Measurable q := measurable_queryPoint p _ hm
  have hqC (u : Fin (3 * n + 2) → Ω) : q u ∈ p.C :=
    queryPoint_mem p _ (modelAt_invariant p g H _ hD hρ hσ hx n)
  have hquery (ξ : ℕ → Ω) : q (fun i => ξ i) = queryPoint (modelAt p g H ξ n) := by
    apply congrArg queryPoint
    exact modelAt_congr p g H n _ _ (fun k hk => by simp [prefixExtend, hk])
  have hb := fresh_prefix_square_moment hIID (3 * n + 2) q e σ hq he
    (fun u => hei _ (hqC u)) (fun u => heb _ (hqC u))
  simpa only [hquery] using hb

lemma center_query_square_moment {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (e : Point p.d → Ω → V) (he : Measurable (Function.uncurry e)) (σ : ℝ)
    (hei : ∀ x ∈ p.C, Integrable (fun ω => ‖e x ω‖ ^ 2) μ)
    (heb : ∀ x ∈ p.C, (∫ ω, ‖e x ω‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (n k : ℕ) (hk : 3 * n ≤ k) :
    Integrable (fun ξ => ‖e (center (roundState p g H ξ n)) (ξ k)‖ ^ 2) P ∧
      (∫ ξ, ‖e (center (roundState p g H ξ n)) (ξ k)‖ ^ 2 ∂P) ≤ σ ^ 2 := by
  let q : (Fin k → Ω) → Point p.d := fun u =>
    center (roundState p g H (prefixExtend ω0 k u) n)
  have hm := measurable_roundState p hD hρ hσ hx g H hg hH hPSD
    (fun j u => prefixExtend ω0 k u j)
    (fun j => (measurable_pi_apply j).comp (measurable_prefixExtend ω0 k)) n
  have hq : Measurable q := measurable_center p _ hm
  have hqC (u : Fin k → Ω) : q u ∈ p.C :=
    center_mem p _ (roundState_invariant p g H _ hD hρ hσ hx n)
  have hquery (ξ : ℕ → Ω) : q (fun i => ξ i) = center (roundState p g H ξ n) := by
    apply congrArg center
    exact roundState_congr p g H n _ _ (fun j hj => by simp [prefixExtend, show j < k by omega])
  have hb := fresh_prefix_square_moment hIID k q e σ hq he
    (fun u => hei _ (hqC u)) (fun u => heb _ (hqC u))
  simpa only [hquery] using hb

lemma measurable_gradient_error {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (hg : Measurable (Function.uncurry g)) (hf : Differentiable ℝ (gradient f)) :
    Measurable (Function.uncurry (fun x ω => g x ω - gradient f x)) :=
  hg.sub (hf.continuous.measurable.comp measurable_fst)

lemma measurable_hessian_error {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (f : Point p.d → ℝ) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (fun x ω => H x ω - fderiv ℝ (gradient f) x)) :=
  hH.sub ((measurable_fderiv ℝ (gradient f)).comp measurable_fst)

lemma centered_gradient_error {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Point p.d → ℝ)
    (g : Point p.d → Ω → Point p.d) (x : Point p.d)
    (hi : Integrable (g x) μ) (hm : ∫ ω, g x ω ∂μ = gradient f x) :
    Integrable (fun ω => g x ω - gradient f x) μ ∧
      (∫ ω, g x ω - gradient f x ∂μ) = 0 := by
  refine ⟨hi.sub (integrable_const _), ?_⟩
  rw [integral_sub hi (integrable_const _), hm]
  simp

lemma fixed_state_normalized_drift {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (μ : Measure Ω) (s : State p.d) (e : Ω → Point p.d) (v m : Point p.d)
    (hD : 0 < p.D) (hσ : 0 ≤ p.σg) (hs : Invariant p s) (hv : ‖v‖ ≤ p.D)
    (hfloor : p.σg * (s.iteration : ℝ) ^ 3 / p.D ^ 2 ≤ s.scale)
    (he : Measurable e) (hie : Integrable e μ) (hme : ∫ ω, e ω ∂μ = 0)
    (hisq : Integrable (fun ω => ‖e ω‖ ^ 2) μ)
    (hsq : (∫ ω, ‖e ω‖ ^ 2 ∂μ) ≤ p.σg ^ 2) :
    Integrable (fun ω => -increment p s * ⟪v, e ω⟫ /
      (advance p s (m + e ω)).scale) μ ∧
    (∫ ω, -increment p s * ⟪v, e ω⟫ / (advance p s (m + e ω)).scale ∂μ) ≤
      p.D ^ 2 / s.iteration := by
  have hW := residualWeight_nonneg p s hD hs
  have htnat := hs.iteration
  have ht : (0 : ℝ) < s.iteration := by exact_mod_cast (show 0 < s.iteration by omega)
  have hb := HessianAdaptiveCubicNormalization.normalized_noise_drift μ e v
    (m - s.modelGradient - s.modelHessian (displacement s))
    (increment p s) (Real.sqrt (residualWeight p s)) s.scale
    (p.σg * ((s.iteration + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2) p.σg p.D s.iteration
    (HessianAdaptiveCubicWeights.increment_pos p s hD hs.scale hs.iteration hs.weight_pos).le
    (Real.sqrt_nonneg _) hs.scale hD ht hσ hv
    (HessianAdaptiveCubicWeights.increment_sqrt_weight_cap p s hD hs.scale hs.iteration)
    hfloor he hie hme hisq hsq
  have hcoeff : (Real.sqrt (residualWeight p s) / p.D) ^ 2 = residualWeight p s / p.D ^ 2 := by
    rw [div_pow, Real.sq_sqrt hW]
  have heq (ω : Ω) : e ω + (m - s.modelGradient - s.modelHessian (displacement s)) =
      m + e ω - s.modelGradient - s.modelHessian (displacement s) := by abel
  dsimp only at hb
  simp only [hcoeff, heq] at hb
  simpa only [advance, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb

lemma fresh_prefix_upper_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] (h : IID ξ p P) (n : ℕ)
    (F : (Fin n → Ω) × Ω → ℝ) (B : ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω => F ((fun i : Fin n => ξ i ω), ξ n ω)) P)
    (hbound : ∀ u, (∫ ω, F (u, ω) ∂p) ≤ B) :
    (∫ ω, F ((fun i : Fin n => ξ i ω), ξ n ω) ∂P) ≤ B := by
  have hp : Integrable F ((Measure.pi fun _ : Fin n => p).prod p) :=
    ((prefix_current_law h n).integrable_comp hF.aestronglyMeasurable).mp hi
  rw [fresh_prefix_integral h n F hp]
  exact (integral_mono hp.integral_prod_left (integrable_const B) hbound).trans_eq (by simp)

lemma adaptive_normalized_drift {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) {ξ : ℕ → Ξ → Ω} {μ : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] (hIID : IID ξ μ P) (n t : ℕ)
    (s : (Fin n → Ω) → State p.d) (hs : MeasurableState p s)
    (hD : 0 < p.D) (hσ : 0 ≤ p.σg) (hinv : ∀ u, Invariant p (s u))
    (ht : ∀ u, (s u).iteration = t)
    (hfloor : ∀ u, p.σg * (t : ℝ) ^ 3 / p.D ^ 2 ≤ (s u).scale)
    (xstar : Point p.d) (hx : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (g : Point p.d → Ω → Point p.d) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgm : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hgs : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hi : Integrable (fun ω =>
      -increment p (s (fun i => ξ i ω)) *
        ⟪(s (fun i => ξ i ω)).trial - xstar,
          g (queryPoint (s (fun i => ξ i ω))) (ξ n ω) - gradient f (queryPoint (s (fun i => ξ i ω)))⟫ /
        (advance p (s (fun i => ξ i ω)) (g (queryPoint (s (fun i => ξ i ω))) (ξ n ω))).scale) P) :
    (∫ ω, -increment p (s (fun i => ξ i ω)) *
        ⟪(s (fun i => ξ i ω)).trial - xstar,
          g (queryPoint (s (fun i => ξ i ω))) (ξ n ω) - gradient f (queryPoint (s (fun i => ξ i ω)))⟫ /
        (advance p (s (fun i => ξ i ω)) (g (queryPoint (s (fun i => ξ i ω))) (ξ n ω))).scale ∂P) ≤
      p.D ^ 2 / t := by
  let F := fun z : (Fin n → Ω) × Ω => -increment p (s z.1) *
    ⟪(s z.1).trial - xstar, g (queryPoint (s z.1)) z.2 - gradient f (queryPoint (s z.1))⟫ /
      (advance p (s z.1) (g (queryPoint (s z.1)) z.2)).scale
  have hm : MeasurableState p (fun z : (Fin n → Ω) × Ω => s z.1) :=
    ⟨hs.iteration.comp measurable_fst, hs.phase.comp measurable_fst,
      hs.weight.comp measurable_fst, hs.point.comp measurable_fst, hs.dual.comp measurable_fst,
      hs.scale.comp measurable_fst, hs.modelGradient.comp measurable_fst,
      hs.modelHessian.comp measurable_fst, hs.trial.comp measurable_fst⟩
  have hq := measurable_queryPoint p _ hm
  have hgf : Measurable (fun z : (Fin n → Ω) × Ω => g (queryPoint (s z.1)) z.2) :=
    hg.comp (hq.prodMk measurable_snd)
  have hnew := measurable_advance p _ hm hD (fun z => hinv z.1) _ hgf
  have hF : Measurable F :=
    ((measurable_increment p _ hm).neg.mul
      ((hm.trial.sub_const xstar).inner (hgf.sub (hdiff.continuous.measurable.comp hq)))).div hnew.scale
  apply fresh_prefix_upper_bound hIID n F (p.D ^ 2 / t) hF hi
  intro u
  have hqC := queryPoint_mem p (s u) (hinv u)
  have he := centered_gradient_error p μ f g (queryPoint (s u)) (hgi _ hqC) (hgm _ hqC)
  have hem : Measurable (fun ω => g (queryPoint (s u)) ω - gradient f (queryPoint (s u))) :=
    (hg.comp (measurable_const.prodMk measurable_id)).sub_const _
  have hf : p.σg * ((s u).iteration : ℝ) ^ 3 / p.D ^ 2 ≤ (s u).scale := by
    simpa only [ht] using hfloor u
  have hb := fixed_state_normalized_drift p μ (s u)
    (fun ω => g (queryPoint (s u)) ω - gradient f (queryPoint (s u)))
    ((s u).trial - xstar) (gradient f (queryPoint (s u))) hD hσ (hinv u)
    (hdiam _ (hinv u).trial _ hx) hf hem he.1 he.2 (hgs _ hqC) (hgb _ hqC)
  simpa only [F, ht, add_sub_cancel] using hb.2

noncomputable def dualNoise (p : Public) (f : Point p.d → ℝ) (xstar : Point p.d)
    (s : State p.d) (gd : Point p.d) : ℝ :=
  -increment p s * ⟪s.trial - xstar, gd - gradient f (queryPoint s)⟫

noncomputable def normalizedNoise (p : Public) (f : Point p.d → ℝ) (xstar : Point p.d)
    (s : State p.d) (gd : Point p.d) : ℝ :=
  dualNoise p f xstar s gd / (advance p s gd).scale

lemma model_normalized_drift {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hdiff : Differentiable ℝ (gradient f))
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω))
    (hgi : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgm : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hgs : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (n : ℕ) (hi : Integrable (fun ξ => normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))) P) :
    (∫ ξ, normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) ∂P) ≤ p.D ^ 2 / (n + 1) := by
  let s := fun u : Fin (3 * n + 2) → Ω => modelAt p g H (prefixExtend ω0 (3 * n + 2) u) n
  have hs : MeasurableState p s :=
    measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
      (fun k u => prefixExtend ω0 (3 * n + 2) u k)
      (fun k => (measurable_pi_apply k).comp (measurable_prefixExtend ω0 (3 * n + 2))) n
  have hf (ξ : ℕ → Ω) : s (fun i => ξ i) = modelAt p g H ξ n :=
    modelAt_congr p g H n _ _ (fun k hk => by simp [prefixExtend, hk])
  have hsinv (u : Fin (3 * n + 2) → Ω) : Invariant p (s u) :=
    modelAt_invariant p g H _ hD hρ hσ hx n
  have hst (u : Fin (3 * n + 2) → Ω) : (s u).iteration = n + 1 :=
    roundState_iteration p g H _ n
  have hsf (u : Fin (3 * n + 2) → Ω) : p.σg * ((n + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2 ≤ (s u).scale :=
    roundState_scale_floor p g H _ hρ.le n
  have hi' : Integrable (fun ξ : ℕ → Ω => -increment p (s (fun i => ξ i)) *
      ⟪(s (fun i => ξ i)).trial - xstar,
        g (queryPoint (s (fun i => ξ i))) (ξ (3 * n + 2)) - gradient f (queryPoint (s (fun i => ξ i)))⟫ /
      (advance p (s (fun i => ξ i)) (g (queryPoint (s (fun i => ξ i))) (ξ (3 * n + 2)))).scale) P := by
    simpa only [hf, normalizedNoise, dualNoise] using hi
  have hb := adaptive_normalized_drift p hIID (3 * n + 2) (n + 1) s hs hD hσ hsinv hst hsf
    xstar hxstar hdiam f hdiff g hg hgi hgm hgs hgb hi'
  simpa only [hf, normalizedNoise, dualNoise, Nat.cast_add, Nat.cast_one] using hb

end LongTails.Proofs.HessianAdaptiveCubicMoments
