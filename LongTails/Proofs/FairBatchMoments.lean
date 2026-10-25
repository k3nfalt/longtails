import LongTails.Proofs.FairTrajectory
import LongTails.Proofs.ScalarClippedMoments
import LongTails.Proofs.MixedNoiseMoments

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory ProbabilityTheory

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def observationMean (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (t : ℕ) (x y : E) : E :=
  ∫ ω, blockObservation cfg g t x y ω ∂p

noncomputable def centeredObservation (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (t : ℕ) (x y : E) (ω : Fin cfg.m → Ω) : E :=
  blockObservation cfg g t x y ω - observationMean cfg p g t x y

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma blockObservation_norm (cfg : Config) (hR : 0 ≤ cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B)
    (g : E → Ω → E) (t : ℕ) (x y : E) (ω : Fin cfg.m → Ω) :
    ‖blockObservation cfg g t x y ω‖ ≤ if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B := by
  unfold blockObservation
  split_ifs
  · exact norm_clip_le (by positivity) _
  · exact norm_clip_le hB _

lemma measurable_observationMean (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : E × E => observationMean cfg p g t z.1 z.2) :=
  (measurable_blockObservation cfg hm hR hg t).stronglyMeasurable.integral_prod_right.measurable

lemma measurable_centeredObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : (E × E) × (Fin cfg.m → Ω) => centeredObservation cfg p g t z.1.1 z.1.2 z.2) :=
  (measurable_blockObservation cfg hm hR hg t).sub
    ((measurable_observationMean cfg hm hR p hg t).comp measurable_fst)

lemma integrable_blockObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y : E) :
    Integrable (blockObservation cfg g t x y) p := by
  have hmeas : Measurable (fun ω => blockObservation cfg g t x y ω) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_blockObservation cfg hm hR hg t).comp
        ((measurable_const : Measurable (fun _ : Fin cfg.m → Ω => (x, y))).prodMk measurable_id)
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B)
    (Filter.Eventually.of_forall (blockObservation_norm cfg hR.le hG hB g t x y))

lemma integral_centeredObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y : E) :
    ∫ ω, centeredObservation cfg p g t x y ω ∂p = 0 := by
  rw [show centeredObservation cfg p g t x y = fun ω => blockObservation cfg g t x y ω -
    observationMean cfg p g t x y from rfl]
  rw [integral_sub (integrable_blockObservation cfg hm hR hG hB p hg t x y) (integrable_const _)]
  simp [observationMean]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centered_moment_le {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {X : Ξ → E} (hXi : Integrable X P) (u : E)
    (hX2 : Integrable (fun ω => ‖X ω - u‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P ∧
      (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P) ≤ ∫ ω, ‖X ω - u‖ ^ 2 ∂P := by
  have h := LongTails.Proofs.ScalarClippedMoments.centered_vector_second_moment
    (hXi.sub (integrable_const u)) hX2
  have he : ∫ ω, X ω - u ∂P = (∫ ω, X ω ∂P) - u := by
    rw [integral_sub hXi (integrable_const u)]
    simp
  simp only [Pi.sub_apply] at h
  rw [he] at h
  simpa only [sub_sub_sub_cancel_right] using h

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma observationMean_norm (cfg : Config) (hR : 0 ≤ cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B)
    (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    (g : E → Ω → E) (t : ℕ) (x y : E) :
    ‖observationMean cfg p g t x y‖ ≤ if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B := by
  have he := norm_integral_le_of_norm_le (μ := p)
    (integrable_const (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B))
    (Filter.Eventually.of_forall (blockObservation_norm cfg hR hG hB g t x y))
  simpa only [observationMean, integral_const, probReal_univ, one_smul] using he

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centeredObservation_norm (cfg : Config) (hR : 0 ≤ cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B)
    (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    (g : E → Ω → E) (t : ℕ) (x y : E) (ω : Fin cfg.m → Ω) :
    ‖centeredObservation cfg p g t x y ω‖ ≤
      2 * (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B) := by
  have h₁ := blockObservation_norm cfg hR hG hB g t x y ω
  have h₂ := observationMean_norm cfg hR hG hB p g t x y
  exact (norm_sub_le _ _).trans (by linarith)

lemma integrable_centeredObservation (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y : E) :
    Integrable (centeredObservation cfg p g t x y) p :=
  (integrable_blockObservation cfg hm hR hG hB p hg t x y).sub (integrable_const _)

lemma integrable_centeredObservation_sq (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y : E) :
    Integrable (fun ω => ‖centeredObservation cfg p g t x y ω‖ ^ 2) p := by
  have hc : 0 ≤ if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B := by
    split_ifs <;> positivity
  apply Integrable.of_bound
    (((measurable_centeredObservation cfg hm hR p hg t).comp
      ((measurable_const : Measurable (fun _ : Fin cfg.m → Ω => (x, y))).prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
    ((2 * (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B)) ^ 2)
  filter_upwards [] with ω
  change |‖centeredObservation cfg p g t x y ω‖ ^ 2| ≤ _
  rw [abs_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (centeredObservation_norm cfg hR.le hG hB p g t x y ω) 2

lemma centeredObservation_moment (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y u : E)
    (h2 : Integrable (fun ω => ‖blockObservation cfg g t x y ω - u‖ ^ 2) p) :
    (∫ ω, ‖centeredObservation cfg p g t x y ω‖ ^ 2 ∂p) ≤
      ∫ ω, ‖blockObservation cfg g t x y ω - u‖ ^ 2 ∂p :=
  (centered_moment_le (integrable_blockObservation cfg hm hR hG hB p hg t x y) u h2).2

noncomputable def observationVariance (cfg : Config) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (t : ℕ) (x y : E) : ℝ :=
  ∫ ω, ‖centeredObservation cfg p g t x y ω‖ ^ 2 ∂p

lemma measurable_observationVariance (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [SFinite p] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : E × E => observationVariance cfg p g t z.1 z.2) :=
  ((measurable_centeredObservation cfg hm hR p hg t).norm.pow_const 2).stronglyMeasurable.integral_prod_right.measurable

lemma observationVariance_bounds (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (x y : E) :
    0 ≤ observationVariance cfg p g t x y ∧ observationVariance cfg p g t x y ≤
      (2 * (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B)) ^ 2 := by
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  have he := integral_mono (integrable_centeredObservation_sq cfg hm hR hG hB p hg t x y)
    (integrable_const ((2 * (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B)) ^ 2))
    (fun ω => pow_le_pow_left₀ (norm_nonneg _) (centeredObservation_norm cfg hR.le hG hB p g t x y ω) 2)
  simpa only [observationVariance, integral_const, probReal_univ, one_smul] using he

lemma centered_batch_step (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (t : ℕ) (hb : 0 < cfg.batch t)
    (S : (ℕ → Fin cfg.m → Ω) → E × E) (hS : Measurable S)
    (hdep : ∀ ξ ξ', (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) → S ξ = S ξ')
    (U : (ℕ → Fin cfg.m → Ω) → E) (hU : Measurable U)
    (hUdep : ∀ ξ ξ', (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) → U ξ = U ξ')
    (hUi2 : Integrable (fun ξ => ‖U ξ‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p))
    {V : ℝ} (hV : ∀ ξ, observationVariance cfg p g t (S ξ).1 (S ξ).2 ≤ V) :
    Integrable (fun ξ => ‖U ξ + (cfg.batch t : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch t),
      centeredObservation cfg p g t (S ξ).1 (S ξ).2 (ξ (cfg.blockOffset t + j))‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, ‖U ξ + (cfg.batch t : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch t),
      centeredObservation cfg p g t (S ξ).1 (S ξ).2 (ξ (cfg.blockOffset t + j))‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
      (∫ ξ, ‖U ξ‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) + V / cfg.batch t := by
  have hvi : Integrable (fun ξ => observationVariance cfg p g t (S ξ).1 (S ξ).2)
      (Measure.infinitePi fun _ : ℕ => p) := by
    apply Integrable.of_bound
      ((measurable_observationVariance cfg hm hR p hg t).comp hS).aestronglyMeasurable
      ((2 * (if cfg.isRefresh t then cfg.G + 3 * cfg.R else cfg.B)) ^ 2)
    filter_upwards [] with ξ
    change |observationVariance cfg p g t (S ξ).1 (S ξ).2| ≤ _
    rw [abs_of_nonneg (observationVariance_bounds cfg hm hR hG hB p hg t _ _).1]
    exact (observationVariance_bounds cfg hm hR hG hB p hg t _ _).2
  have he := MixedNoise.batch_average_variable_variance p (cfg.blockOffset t) S hS hdep U hU hUdep hUi2
    (fun z ω => centeredObservation cfg p g t z.1 z.2 ω)
    (measurable_centeredObservation cfg hm hR p hg t)
    (fun z => integrable_centeredObservation cfg hm hR hG hB p hg t z.1 z.2)
    (fun z => integral_centeredObservation cfg hm hR hG hB p hg t z.1 z.2)
    (fun z => integrable_centeredObservation_sq cfg hm hR hG hB p hg t z.1 z.2)
    (fun z => observationVariance cfg p g t z.1 z.2) (fun _ => le_rfl) hvi (cfg.batch t) hb
  have hv := integral_mono hvi (integrable_const V) hV
  simp only [integral_const, probReal_univ, one_smul] at hv
  refine ⟨he.1, he.2.trans ?_⟩
  gcongr

end OracleTemplate.FairVarianceReduction
