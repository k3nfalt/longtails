import LongTails.Proofs.AdamCenteredProcess
import LongTails.Proofs.AdamExponentialProcess
import LongTails.Proofs.AdamGeneralizedTrajectory
import LongTails.Proofs.AdamNormalizedMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedNoise

open OracleTemplate.Adam AdamNormalizedMoments

noncomputable def response {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (ρ τ : ℝ) (s : Point d × Point d × Point d) (ω : Ω) : Point d :=
  normalized (fun i => (1 - ρ) * s.2.2 i) ρ τ (g s.1 ω)

noncomputable def meanResponse {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Point d → Ω → Point d) (ρ τ : ℝ)
    (s : Point d × Point d × Point d) : Point d := ∫ ω, response g ρ τ s ω ∂P

lemma response_direction {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (ρ τ : ℝ) (s : Point d × Point d × Point d) (ω : Ω) :
    response g ρ τ s ω = direction τ (g s.1 ω) (secondMomentStep ρ s.2.2 (g s.1 ω)) := rfl

lemma measurable_response {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g)) (ρ τ : ℝ) :
    Measurable (Function.uncurry (response g ρ τ)) := by
  have hreply : Measurable (fun z : (Point d × Point d × Point d) × Ω => g z.1.1 z.2) :=
    hg.comp (by fun_prop : Measurable
      (fun z : (Point d × Point d × Point d) × Ω => (z.1.1, z.2)))
  simp only [Function.uncurry_def, response_direction]
  have hv : Measurable (fun z : (Point d × Point d × Point d) × Ω => z.1.2.2) := by fun_prop
  exact (measurable_direction τ).comp
    (hreply.prodMk ((measurable_secondMomentStep ρ).comp (hv.prodMk hreply)))

lemma measurable_meanResponse {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (ρ τ : ℝ) : Measurable (meanResponse P g ρ τ) :=
  (measurable_response hg ρ τ).stronglyMeasurable.integral_prod_right'.measurable

lemma response_bias {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (s : Point d × Point d × Point d) (h : Point d)
    (hi : Integrable (g s.1) P) (hmean : (∫ ω, g s.1 ω ∂P) = h)
    (h2 : Integrable (fun ω => ‖g s.1 ω - h‖ ^ 2) P)
    {ρ τ A σ : ℝ} (hA : 0 < A) (ha : ∀ i, A ≤ (1 - ρ) * s.2.2 i)
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hvar : (∫ ω, ‖g s.1 ω - h‖ ^ 2 ∂P) ≤ σ ^ 2) :
    ‖meanResponse P g ρ τ s - normalized (fun i => (1 - ρ) * s.2.2 i) ρ τ h‖ ≤
      3 * Real.sqrt ρ / A * σ ^ 2 := by
  exact (integral_normalized_bias (hg.comp measurable_prodMk_left) hi hmean h2 hA ha hρ hτ).trans
    (mul_le_mul_of_nonneg_left hvar (by positivity))

lemma response_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (s : Point d × Point d × Point d) (h : Point d)
    (hi : Integrable (g s.1) P) (h2 : Integrable (fun ω => ‖g s.1 ω - h‖ ^ 2) P)
    {ρ τ A σ : ℝ} (hA : 0 < A) (ha : ∀ i, A ≤ (1 - ρ) * s.2.2 i)
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hvar : (∫ ω, ‖g s.1 ω - h‖ ^ 2 ∂P) ≤ σ ^ 2) :
    Integrable (fun ω => ‖response g ρ τ s ω - meanResponse P g ρ τ s‖ ^ 2) P ∧
      (∫ ω, ‖response g ρ τ s ω - meanResponse P g ρ τ s‖ ^ 2 ∂P) ≤ σ ^ 2 / A := by
  have hh := integral_normalized_variance (hg.comp measurable_prodMk_left) hi h h2 hA ha hρ hτ
  exact ⟨hh.1, hh.2.trans (div_le_div_of_nonneg_right hvar hA.le)⟩

noncomputable def flooredResponse {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (A ρ τ : ℝ) (s : Point d × Point d × Point d) (ω : Ω) : Point d :=
  normalized (fun i => max A ((1 - ρ) * s.2.2 i)) ρ τ (g s.1 ω)

noncomputable def flooredMean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Point d → Ω → Point d) (A ρ τ : ℝ)
    (s : Point d × Point d × Point d) : Point d := ∫ ω, flooredResponse g A ρ τ s ω ∂P

lemma flooredResponse_eq {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (A ρ τ : ℝ) (s : Point d × Point d × Point d)
    (hs : ∀ i, A ≤ (1 - ρ) * s.2.2 i) (ω : Ω) :
    flooredResponse g A ρ τ s ω = response g ρ τ s ω := by
  simp only [flooredResponse, response, max_eq_right (hs _)]

lemma flooredMean_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Point d → Ω → Point d) (A ρ τ : ℝ)
    (s : Point d × Point d × Point d) (hs : ∀ i, A ≤ (1 - ρ) * s.2.2 i) :
    flooredMean P g A ρ τ s = meanResponse P g ρ τ s := by
  unfold flooredMean meanResponse
  simp only [flooredResponse_eq g A ρ τ s hs]

lemma measurable_flooredResponse {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g)) (A ρ τ : ℝ) :
    Measurable (Function.uncurry (flooredResponse g A ρ τ)) := by
  have hreply : Measurable (fun z : (Point d × Point d × Point d) × Ω => g z.1.1 z.2) :=
    hg.comp (by fun_prop : Measurable
      (fun z : (Point d × Point d × Point d) × Ω => (z.1.1, z.2)))
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hi := (measurable_coordinate i).comp hreply
  dsimp [flooredResponse, normalized, AdamNormalizedKernel.kernel]
  fun_prop

lemma measurable_flooredMean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (A ρ τ : ℝ) : Measurable (flooredMean P g A ρ τ) :=
  (measurable_flooredResponse hg A ρ τ).stronglyMeasurable.integral_prod_right'.measurable

lemma flooredResponse_norm {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    {A ρ τ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (s : Point d × Point d × Point d) (ω : Ω) :
    ‖flooredResponse g A ρ τ s ω‖ ≤ Real.sqrt d / Real.sqrt ρ := by
  have hh := normalized_square_bound (a := fun i => max A ((1 - ρ) * s.2.2 i))
    (fun i => hA.trans_le (le_max_left _ _)) hρ hτ (g s.1 ω)
  have he : (Real.sqrt d / Real.sqrt ρ) ^ 2 = (d : ℝ) / ρ := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt hρ.le]
  have hn : 0 ≤ Real.sqrt d / Real.sqrt ρ := by positivity
  change ‖flooredResponse g A ρ τ s ω‖ ^ 2 ≤ (d : ℝ) / ρ at hh
  nlinarith [norm_nonneg (flooredResponse g A ρ τ s ω)]

lemma flooredResponse_trajectory {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (β η τ : ℝ) {vinit : ℝ} (hv : 0 < vinit) {T t : ℕ} (hT : 2 ≤ T) (ht : t < T)
    (x0 : Point d) (ξ : ℕ → Ω) (ω : Ω) :
    flooredResponse g (vinit / 4) (1 / T) τ
      (LongTails.Algorithms.GeneralizedSmoothAdam.trajectory g β (1 / T) η τ vinit x0 ξ t) ω =
    response g (1 / T) τ
      (LongTails.Algorithms.GeneralizedSmoothAdam.trajectory g β (1 / T) η τ vinit x0 ξ t) ω :=
  flooredResponse_eq _ _ _ _ _
    (fun i => AdamGeneralizedTrajectory.predictable_secondMoment_lower g β η τ hv hT ht x0 ξ i) ω

lemma flooredMean_trajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Point d → Ω → Point d) (β η τ : ℝ) {vinit : ℝ} (hv : 0 < vinit)
    {T t : ℕ} (hT : 2 ≤ T) (ht : t < T) (x0 : Point d) (ξ : ℕ → Ω) :
    flooredMean P g (vinit / 4) (1 / T) τ
      (LongTails.Algorithms.GeneralizedSmoothAdam.trajectory g β (1 / T) η τ vinit x0 ξ t) =
    meanResponse P g (1 / T) τ
      (LongTails.Algorithms.GeneralizedSmoothAdam.trajectory g β (1 / T) η τ vinit x0 ξ t) :=
  flooredMean_eq _ _ _ _ _ _
    (fun i => AdamGeneralizedTrajectory.predictable_secondMoment_lower g β η τ hv hT ht x0 ξ i)

noncomputable def innovation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Point d → Ω → Point d) (u : Point d → Point d) (A ρ τ α : ℝ)
    (s : Point d × Point d × Point d) (ω : Ω) : ℝ :=
  -α * ⟪u s.1, flooredResponse g A ρ τ s ω - flooredMean P g A ρ τ s⟫

lemma measurable_innovation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {g : Point d → Ω → Point d} {u : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hu : Measurable u) (A ρ τ α : ℝ) :
    Measurable (Function.uncurry (innovation P g u A ρ τ α)) := by
  have hr := measurable_flooredResponse hg A ρ τ
  have hm : Measurable (fun z : (Point d × Point d × Point d) × Ω =>
      flooredMean P g A ρ τ z.1) := (measurable_flooredMean P hg A ρ τ).comp measurable_fst
  have hpoint : Measurable (fun z : (Point d × Point d × Point d) × Ω => u z.1.1) :=
    hu.comp (by fun_prop)
  exact (continuous_inner.measurable.comp (hpoint.prodMk (hr.sub hm))).const_mul (-α)

lemma integrable_flooredResponse {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (s : Point d × Point d × Point d) (hi : Integrable (g s.1) P)
    {A ρ τ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) :
    Integrable (flooredResponse g A ρ τ s) P :=
  integrable_normalized (hg.comp measurable_prodMk_left) hi
    (fun _ => hA.trans_le (le_max_left _ _)) hρ hτ

lemma innovation_mean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (u : Point d → Point d)
    (s : Point d × Point d × Point d) (hi : Integrable (g s.1) P)
    {A ρ τ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (α : ℝ) :
    (∫ ω, innovation P g u A ρ τ α s ω ∂P) = 0 :=
  centered_pairing_mean (integrable_flooredResponse P hg s hi hA hρ hτ) (u s.1) α

lemma innovation_abs {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Point d → Ω → Point d)
    (u : Point d → Point d) {A ρ τ α K : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α) (hu : ∀ x, ‖u x‖ ≤ K)
    (s : Point d × Point d × Point d) (ω : Ω) :
    |innovation P g u A ρ τ α s ω| ≤ 2 * α * K * (Real.sqrt d / Real.sqrt ρ) := by
  have hh := centered_pairing_abs (P := P) (flooredResponse_norm g hA hρ hτ s) (u s.1) α ω
  rw [abs_of_nonneg hα] at hh
  apply hh.trans
  gcongr
  exact hu s.1


lemma innovation_variance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    (hg : Measurable (Function.uncurry g)) (u : Point d → Point d)
    (s : Point d × Point d × Point d) (h : Point d)
    (hi : Integrable (g s.1) P) (h2 : Integrable (fun ω => ‖g s.1 ω - h‖ ^ 2) P)
    {A ρ τ α σ K : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hu : ‖u s.1‖ ≤ K) (hvar : (∫ ω, ‖g s.1 ω - h‖ ^ 2 ∂P) ≤ σ ^ 2) :
    Integrable (fun ω => (innovation P g u A ρ τ α s ω) ^ 2) P ∧
      (∫ ω, (innovation P g u A ρ τ α s ω) ^ 2 ∂P) ≤ α ^ 2 * K ^ 2 * σ ^ 2 / A := by
  have hv := integral_normalized_variance (hg.comp measurable_prodMk_left) hi h h2 hA
    (a := fun i => max A ((1 - ρ) * s.2.2 i)) (fun _ => le_max_left _ _) hρ hτ
  have hve := hv.2.trans (div_le_div_of_nonneg_right hvar hA.le)
  have hh := centered_pairing_variance (integrable_flooredResponse P hg s hi hA hρ hτ)
    hv.1 hve (u s.1) α
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hp := mul_le_mul_of_nonneg_left hnorm (sq_nonneg α)
  have hp' := mul_le_mul_of_nonneg_right hp (div_nonneg (sq_nonneg σ) hA.le)
  convert hp' using 1; ring

lemma innovation_maximum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {u : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hu : Measurable u)
    (h : Point d → Point d) (hi : ∀ x, Integrable (g x) P)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    {A ρ τ α σ K θ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hα : 0 ≤ α) (hθ : 0 ≤ θ) (huk : ∀ x, ‖u x‖ ≤ K)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hsmall : θ * (2 * α * K * (Real.sqrt d / Real.sqrt ρ)) ≤ 1)
    {next : (Point d × Point d × Point d) → Ω → (Point d × Point d × Point d)}
    (hn : Measurable (Function.uncurry next)) (s : Point d × Point d × Point d) (ω0 : Ω) (n : ℕ) :
    Integrable (fun ξ => Real.exp (θ / 2 * AdamExponentialProcess.partialMax next
      (innovation P g u A ρ τ α) s ξ n)) (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, Real.exp (θ / 2 * AdamExponentialProcess.partialMax next
      (innovation P g u A ρ τ α) s ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      2 * Real.exp (θ ^ 2 * n * (α ^ 2 * K ^ 2 * σ ^ 2 / A) / 2) := by
  have hm := measurable_innovation P hg hu A ρ τ α
  have hb := innovation_abs P g u hA hρ hτ hα huk
  have hiU (s : Point d × Point d × Point d) : Integrable (innovation P g u A ρ τ α s) P := by
    apply Integrable.of_bound (hm.comp measurable_prodMk_left).aestronglyMeasurable
      (2 * α * K * (Real.sqrt d / Real.sqrt ρ))
    exact Filter.Eventually.of_forall (fun ω => hb s ω)
  have hv (s : Point d × Point d × Point d) := innovation_variance P hg u s (h s.1)
    (hi s.1) (h2 s.1) hA hρ.le hτ (α := α) (huk s.1) (hvar s.1)
  apply AdamExponentialProcess.exponential_partialMax P hn hm (by positivity) hiU
    (fun s => (hv s).1) (fun s => innovation_mean P hg u s (hi s.1) hA hρ.le hτ α)
    (fun s => (hv s).2) _ s ω0 n
  intro z ω
  rw [abs_mul, abs_of_nonneg hθ]
  exact (mul_le_mul_of_nonneg_left (hb z ω) hθ).trans hsmall

lemma innovation_pointwise {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Point d → Ω → Point d)
    (u : Point d → Point d) {A ρ τ α : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (s : Point d × Point d × Point d) (ω : Ω) :
    |innovation P g u A ρ τ α s ω| ≤
      (2 * |α| * (Real.sqrt d / Real.sqrt ρ)) * ‖u s.1‖ := by
  have hh := centered_pairing_abs (P := P) (flooredResponse_norm g hA hρ hτ s) (u s.1) α ω
  dsimp [innovation, flooredMean]
  convert hh using 1; ring

lemma innovation_sum_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {u : Point d → Point d} (hg : Measurable (Function.uncurry g)) (hu : Measurable u)
    (h : Point d → Point d) (hi : ∀ x, Integrable (g x) P)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    {A ρ τ α σ K C : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {next : (Point d × Point d × Point d) → Ω → (Point d × Point d × Point d)}
    (hn : Measurable (Function.uncurry next)) (s : Point d × Point d × Point d) (ω0 : Ω) (n : ℕ)
    (M : (ℕ → Ω) → ℝ)
    (hMi : Integrable (fun ξ => (M ξ) ^ 2) (Measure.infinitePi (fun _ : ℕ => P)))
    (hME : (∫ ξ, (M ξ) ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ C ^ 2)
    (hbound : ∀ ξ t, t < n → ‖u (AdamHeavyTailedProcess.stateAt next s ξ t).1‖ ≤ K * M ξ) :
    Integrable (fun ξ => (AdamExponentialProcess.partialSum next (innovation P g u A ρ τ α) s ξ n) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, (AdamExponentialProcess.partialSum next (innovation P g u A ρ τ α) s ξ n) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ n * (α ^ 2 * K ^ 2 * σ ^ 2 / A) * C ^ 2 := by
  let U := innovation P g u A ρ τ α
  let L := 2 * |α| * (Real.sqrt d / Real.sqrt ρ)
  have hmU := measurable_innovation P hg hu A ρ τ α
  have hUi (z : Point d × Point d × Point d) : Integrable (U z) P := by
    apply Integrable.of_bound (hmU.comp measurable_prodMk_left).aestronglyMeasurable (L * ‖u z.1‖)
    exact Filter.Eventually.of_forall (fun ω => innovation_pointwise P g u hA hρ hτ z ω)
  have hzero (z) : (∫ ω, U z ω ∂P) = 0 := innovation_mean P hg u z (hi z.1) hA hρ.le hτ α
  have hmstate (t) := AdamHeavyTailedProcess.measurable_stateAt hn s t
  have hup (t) : Measurable (fun ξ => u (AdamHeavyTailedProcess.stateAt next s ξ t).1) :=
    hu.comp (hmstate t).fst
  have hpoint (t : ℕ) (ht : t < n) (ξ) : ‖u (AdamHeavyTailedProcess.stateAt next s ξ t).1‖ ^ 2 ≤
      K ^ 2 * (M ξ) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound ξ t ht) 2
  have hip (t : ℕ) (ht : t < n) : Integrable
      (fun ξ => ‖u (AdamHeavyTailedProcess.stateAt next s ξ t).1‖ ^ 2) (Measure.infinitePi (fun _ : ℕ => P)) := by
    apply (hMi.const_mul (K ^ 2)).mono' ((hup t).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint t ht ξ)
  have hiU2 (t : ℕ) (ht : t < n) : Integrable
      (fun ξ => (U (AdamHeavyTailedProcess.stateAt next s ξ t) (ξ t)) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)) := by
    have hmt := hmU.comp ((hmstate t).prodMk (measurable_pi_apply t))
    apply ((hip t ht).const_mul (L ^ 2)).mono' (hmt.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := pow_le_pow_left₀ (abs_nonneg _) (innovation_pointwise P g u (α := α) hA hρ hτ
      (AdamHeavyTailedProcess.stateAt next s ξ t) (ξ t)) 2
    simpa only [U, L, Function.comp_apply, Function.uncurry_apply_pair, sq_abs, mul_pow] using hh
  have hE (t : ℕ) (ht : t < n) :
      (∫ ξ, (U (AdamHeavyTailedProcess.stateAt next s ξ t) (ξ t)) ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (α ^ 2 * K ^ 2 * σ ^ 2 / A) * C ^ 2 := by
    let V := fun z : Point d × Point d × Point d => α ^ 2 * ‖u z.1‖ ^ 2 * σ ^ 2 / A
    have hiV : Integrable (fun ξ => V (AdamHeavyTailedProcess.stateAt next s ξ t))
        (Measure.infinitePi (fun _ : ℕ => P)) := (((hip t ht).const_mul (α ^ 2)).mul_const (σ ^ 2)).div_const A
    have hv (z : Point d × Point d × Point d) := innovation_variance P hg u z (h z.1)
      (hi z.1) (h2 z.1) hA hρ.le hτ (α := α) (le_rfl : ‖u z.1‖ ≤ ‖u z.1‖) (hvar z.1)
    have hh := AdamHeavyTailedProcess.stateAt_sample_integral_le P next s ω0 t
      (fun z ω => (U z ω) ^ 2) V (hiU2 t ht) hiV (fun b => (hv _).1) (fun b => (hv _).2)
    have hVbound (ξ) : V (AdamHeavyTailedProcess.stateAt next s ξ t) ≤
        (α ^ 2 * K ^ 2 * σ ^ 2 / A) * (M ξ) ^ 2 := by
      dsimp [V]
      have hp := mul_le_mul_of_nonneg_left (hpoint t ht ξ) (by positivity : 0 ≤ α ^ 2 * σ ^ 2 / A)
      convert hp using 1 <;> ring
    have hvint := integral_mono hiV (hMi.const_mul (α ^ 2 * K ^ 2 * σ ^ 2 / A)) hVbound
    rw [integral_const_mul] at hvint
    exact hh.trans (hvint.trans (mul_le_mul_of_nonneg_left hME (by positivity)))
  have hh := AdamCenteredProcess.partialSum_second_moment P hn hmU s ω0 n hUi hzero hiU2
  refine ⟨hh.1, ?_⟩
  rw [hh.2]
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun t ht => hE t (Finset.mem_range.1 ht))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using hsum

end LongTails.Proofs.AdamGeneralizedNoise
