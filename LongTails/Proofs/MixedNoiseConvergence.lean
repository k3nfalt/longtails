import LongTails.Proofs.MixedNoiseTuning
import LongTails.Proofs.HeavyTailedPLStep
import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.MixedNoiseMeasurability
import LongTails.Proofs.PairedOracleExecution

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OracleTemplate.MixedNoise

lemma tuned_iterations_bounds {L r M σ Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hlarge : ε ^ 2 < 2 * L * Δ) :
    0 < (tunedConfig L r M σ Δ ε).T ∧
    8 * Δ ≤ (tunedConfig L r M σ Δ ε).η * (tunedConfig L r M σ Δ ε).T * ε ^ 2 ∧
    ((tunedConfig L r M σ Δ ε).T : ℝ) ≤ 36 * L * Δ / ε ^ 2 := by
  let N := iterationTarget L Δ ε
  let q := 4 ^ hierarchyDepth L M σ Δ ε
  have hN := iterationTarget_bounds hL hΔ hε hlarge
  have hq : 0 < q := by dsimp [q]; positivity
  have hqN : q ≤ N := hierarchy_power_le_target L M σ Δ ε (by omega)
  have hb := rounded_multiple_bounds N q hq hqN
  have hT : (tunedConfig L r M σ Δ ε).T = q * ⌈(N : ℝ) / q⌉₊ := by
    simp only [tunedConfig, not_le.mpr hlarge, ↓reduceIte, q, N]
  rw [hT]
  have hlo : (N : ℝ) ≤ q * ⌈(N : ℝ) / q⌉₊ := by exact_mod_cast hb.1
  have hhi : (q : ℝ) * ⌈(N : ℝ) / q⌉₊ ≤ 2 * N := by exact_mod_cast hb.2
  refine ⟨by omega, ?_, ?_⟩
  · have hlow := hN.1.trans hlo
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hlow
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1 / (2 * L) by positivity)
    have he : (1 / (2 * L)) * (16 * L * Δ) = 8 * Δ := by field_simp; ring
    rw [he] at hh'
    simpa only [tunedConfig, Nat.cast_mul, mul_assoc] using hh'
  · dsimp only [N] at hhi ⊢
    push_cast
    have he : 36 * L * Δ / ε ^ 2 = 2 * (18 * L * Δ / ε ^ 2) := by ring
    rw [he]
    exact hhi.trans (mul_le_mul_of_nonneg_left hN.2.1 (by norm_num))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]

lemma tuned_gradient_energy (p : Measure Ω) [IsProbabilityMeasure p]
    {L r M σ Δ ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hlarge : ε ^ 2 < 2 * L * Δ)
    (f : E → ℝ) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hG : LipschitzWith ⟨L, hL.le⟩ (gradient f))
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ r * ‖gradient f x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2 ∂p ≤
      r * (‖gradient f x‖ ^ 2 + ‖gradient f y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (hgap : ∀ y, f x0 - f y ≤ Δ) :
    let cfg := tunedConfig L r M σ Δ ε
    (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      ‖gradient f ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤ cfg.T * ε ^ 2 := by
  dsimp only
  let cfg := tunedConfig L r M σ Δ ε
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let X := fun seed ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs
  let U := fun seed ξ t => ∑ l ∈ Finset.range (cfg.m + 1),
    (batchState cfg g x0 seed ξ (cfg.eventOffset (t + 1))).estimates l
  have hlip (x y : E) : ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ :=
    hG.norm_sub_le x y
  have hX (seed : RepresentativeSeed cfg) (k : ℕ) :=
    (batchState_memLp p cfg g hg (gradient f) hG r σ hnoise hbound x0 seed cfg.tasks.length).1 k
  have hGi (seed : RepresentativeSeed cfg) (k : ℕ) :
      MemLp (fun ξ => gradient f (X seed ξ k)) 2 P := lipschitz_comp_memLp hG (hX seed k)
  have hUi (seed : RepresentativeSeed cfg) (k : ℕ) : MemLp (fun ξ => U seed ξ k) 2 P :=
    memLp_finsetSum _ (fun l _ =>
      (batchState_memLp p cfg g hg (gradient f) hG r σ hnoise hbound x0 seed
        (cfg.eventOffset (k + 1))).2 l)
  have hd := integrated_inexact_path_energy P hgrad hlip X U x0 cfg.T
    (fun seed ξ => batchState_initial_point cfg g x0 seed ξ cfg.tasks.length)
    (fun seed ξ _ ht => iteration_path_step cfg g x0 seed ξ ht) hgap hGi hUi
  have he := tuned_error_energy p L r M σ Δ ε hr hε g hg (gradient f) hG
    hgi hmean hnoise hbound hdiff hmixed x0
  have hinit : ‖gradient f x0‖ ^ 2 ≤ 2 * L * Δ := by
    have hh := HeavyTailedPL.gradient_sq_le hL hgrad hlip
      (m := f x0 - Δ) (fun y => by linarith [hgap y]) x0
    simpa only [sub_sub_cancel] using hh
  apply averaged_gradient_bound cfg.T (η := cfg.η) (L := L) (Δ := Δ)
    (G := ‖gradient f x0‖ ^ 2) (by dsimp [cfg, tunedConfig]; positivity)
    (by dsimp [cfg, tunedConfig]; field_simp)
    (integral_nonneg (fun _ => integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
    (integral_nonneg (fun _ => integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
    (sq_nonneg _) hinit (tuned_iterations_bounds hL hΔ hε hlarge).2.1 hd he

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma integrated_uniform_output_energy (p : Measure Ω)
    (cfg : Config) (g : E → Ω → E) (x0 : E) (φ : E → ℝ) (hT : 0 < cfg.T)
    (hi : ∀ (seed : RepresentativeSeed cfg) k,
      Integrable (fun ξ => φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k))
        (Measure.infinitePi fun _ : ℕ => p)) :
    (∫ seed, (∫ ξ, φ (representativeOutput (batchState cfg g x0 seed ξ cfg.tasks.length))
      ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) =
    (cfg.T : ℝ)⁻¹ * (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)
      ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let O := fun seed ξ => φ (representativeOutput (batchState cfg g x0 seed ξ cfg.tasks.length))
  let A := fun seed ξ => ∑ t ∈ Finset.range cfg.T,
    φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)
  have hO (seed : RepresentativeSeed cfg) : Integrable (O seed) P := by
    simpa only [O, representativeOutput, batchState_seed] using hi seed seed.outputIndex.val
  have hA (seed : RepresentativeSeed cfg) : Integrable (A seed) P :=
    integrable_finsetSum _ (fun k hk => hi seed k)
  have he (ξ : ℕ → Ω) : (∫ seed, O seed ξ ∂Q) = (cfg.T : ℝ)⁻¹ * ∫ seed, A seed ξ ∂Q := by
    have h := uniform_output_energy cfg g x0 ξ cfg.tasks.length φ
    simp only [max_eq_right (show (1 : ℝ) ≤ cfg.T by exact_mod_cast hT)] at h
    have hs (seed : RepresentativeSeed cfg) :
        (∑ a : Fin (max 1 cfg.T), φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs a.val)) =
          ∑ t ∈ Finset.range cfg.T, φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t) := by
      rw [Fin.sum_univ_eq_sum_range (fun t => φ ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t))]
      rw [Nat.max_eq_right (by omega : 1 ≤ cfg.T)]
    simp_rw [hs] at h
    simpa only [integral_const_mul] using h
  change (∫ seed, (∫ ξ, O seed ξ ∂P) ∂Q) = (cfg.T : ℝ)⁻¹ * ∫ seed, (∫ ξ, A seed ξ ∂P) ∂Q
  rw [← integral_uniform_measure_comm P O hO]
  dsimp only [Q] at he ⊢
  simp_rw [he]
  rw [integral_const_mul, integral_uniform_measure_comm P A hA]

omit [CompleteSpace E] in
lemma batchOutput_expected_norm (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {K : NNReal} (hG : LipschitzWith K G) (x0 : E)
    {ε : ℝ} (hε : 0 < ε) (hT : 0 < cfg.T)
    (hX : ∀ (seed : RepresentativeSeed cfg) k,
      MemLp (fun ξ => (batchState cfg g x0 seed ξ cfg.tasks.length).xs k) 2
        (Measure.infinitePi fun _ : ℕ => p))
    (henergy : (∫ seed, (∫ ξ, ∑ t ∈ Finset.range cfg.T,
      ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs t)‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => p))
      ∂(PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure) ≤ cfg.T * ε ^ 2) :
    let P := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => p)
    let F := fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
      G (representativeOutput (batchState cfg g x0 z.1 z.2 cfg.tasks.length))
    Integrable (fun z => ‖F z‖) P ∧ (∫ z, ‖F z‖ ∂P) ≤ ε := by
  dsimp only
  let P := Measure.infinitePi fun _ : ℕ => p
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let F := fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
    G (representativeOutput (batchState cfg g x0 z.1 z.2 cfg.tasks.length))
  have hFm : Measurable F := hG.continuous.measurable.comp (batchOutput_measurable cfg g hg x0 cfg.tasks.length)
  have hi (seed : RepresentativeSeed cfg) (k : ℕ) :
      Integrable (fun ξ => ‖G ((batchState cfg g x0 seed ξ cfg.tasks.length).xs k)‖ ^ 2) P := by
    have h := lipschitz_comp_memLp hG (hX seed k)
    exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq h.aestronglyMeasurable).mp h
  have hF2 : Integrable (fun z => ‖F z‖ ^ 2) (Q.prod P) := by
    apply (integrable_prod_iff (hFm.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun seed => ?_), Integrable.of_finite⟩
    simpa only [F, representativeOutput, batchState_seed] using hi seed seed.outputIndex.val
  have hF := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hFm.aestronglyMeasurable).mpr hF2
  refine ⟨(hF.integrable (by norm_num)).norm, ?_⟩
  have hs : (∫ z, ‖F z‖ ^ 2 ∂(Q.prod P)) ≤ ε ^ 2 := by
    rw [integral_prod _ hF2]
    change (∫ seed, (∫ ξ, ‖G (representativeOutput (batchState cfg g x0 seed ξ cfg.tasks.length))‖ ^ 2 ∂P) ∂Q) ≤ ε ^ 2
    rw [integrated_uniform_output_energy p cfg g x0 (fun x => ‖G x‖ ^ 2) hT hi]
    have h := mul_le_mul_of_nonneg_left henergy (show 0 ≤ (cfg.T : ℝ)⁻¹ by positivity)
    have hTr : (cfg.T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    simpa only [← mul_assoc, inv_mul_cancel₀ hTr, one_mul] using h
  calc
    _ ≤ Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂(Q.prod P)) :=
      NormalizedStorm.integral_norm_le_sqrt (μ := Q.prod P) hFm.aestronglyMeasurable hF2
    _ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hs
    _ = ε := Real.sqrt_sq hε.le

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma batchOutput_zero_iterations (cfg : Config) (g : E → Ω → E) (x0 : E)
    (hT : cfg.T = 0) (seed : RepresentativeSeed cfg) (ξ : ℕ → Ω) :
    representativeOutput (batchState cfg g x0 seed ξ cfg.tasks.length) = x0 := by
  simp [Config.tasks, Config.prefixTasks, hT, batchState, representativeOutput, multiscaleRepresentatives]

omit [CompleteSpace E] in
lemma execute_paired_output_law (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (x0 : E)
    (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) (hK : cfg.calls ≤ K) :
    let paired := P.map (fun ξ k => ξ (k / 2))
    let O : Oracle E E := { Seed := fun _ => Ω, law := paired, answer := fun _ (_, x) ω => g x ω }
    (((PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure).prod (paired : Measure _)).map
      (fun z => execute O (multiscaleRepresentatives cfg x0) (fun _ => K) z.1 z.2) =
    (((PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure).prod (P : Measure _)).map
      (fun z => representativeOutput (batchState cfg g x0 z.1 z.2 cfg.tasks.length)) := by
  dsimp only
  apply LongTails.Proofs.PairedOracleExecution.paired_stream_output_law (fun k (ξ : ℕ → Ω) => ξ k)
    (fun k => measurable_pi_apply k)
    (execute_measurable cfg g hg x0 (P.map (fun ξ k => ξ (k / 2))) K)
  intro seed ξ
  exact execute_batchState_of_le cfg g x0 _ seed _ ξ (fun _ _ => rfl) K hK

lemma tuned_output_expected_norm (p : Measure Ω) [IsProbabilityMeasure p]
    {L r M σ Δ ε : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (f : E → ℝ) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hG : LipschitzWith ⟨L, hL.le⟩ (gradient f))
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ r * ‖gradient f x‖ ^ 2 + σ ^ 2)
    (hdiff : ∀ x y, Integrable (fun ω => ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2) p)
    (hmixed : ∀ x y, ∫ ω, ‖(g x ω - gradient f x) - (g y ω - gradient f y)‖ ^ 2 ∂p ≤
      r * (‖gradient f x‖ ^ 2 + ‖gradient f y‖ ^ 2) + M ^ 2 * ‖x - y‖ ^ 2)
    (x0 : E) (hgap : ∀ y, f x0 - f y ≤ Δ) :
    let cfg := tunedConfig L r M σ Δ ε
    let P := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => p)
    let F := fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
      gradient f (representativeOutput (batchState cfg g x0 z.1 z.2 cfg.tasks.length))
    Integrable (fun z => ‖F z‖) P ∧ (∫ z, ‖F z‖ ∂P) ≤ ε := by
  dsimp only
  let cfg := tunedConfig L r M σ Δ ε
  by_cases hsmall : 2 * L * Δ ≤ ε ^ 2
  · have hT : cfg.T = 0 := by simp only [cfg, tunedConfig, hsmall, ↓reduceIte]
    have he (z : RepresentativeSeed cfg × (ℕ → Ω)) :=
      batchOutput_zero_iterations cfg g x0 hT z.1 z.2
    dsimp only [cfg] at he
    simp_rw [he]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    have hi := HeavyTailedPL.gradient_sq_le hL hgrad
      (fun x y => hG.norm_sub_le x y) (m := f x0 - Δ) (fun y => by linarith [hgap y]) x0
    have hh : ‖gradient f x0‖ ^ 2 ≤ ε ^ 2 := by
      have hh : ‖gradient f x0‖ ^ 2 ≤ 2 * L * Δ := by
        simpa only [sub_sub_cancel] using hi
      exact hh.trans hsmall
    nlinarith only [hh, norm_nonneg (gradient f x0), hε]
  · have hlarge := lt_of_not_ge hsmall
    apply batchOutput_expected_norm p cfg g hg (gradient f) hG x0 hε
      (tuned_iterations_bounds hL hΔ hε hlarge).1
      (fun seed k => (batchState_memLp p cfg g hg (gradient f) hG r σ hnoise hbound
        x0 seed cfg.tasks.length).1 k)
    exact tuned_gradient_energy p hL hr hΔ hε hlarge f hgrad hG g hg hgi hmean
      hnoise hbound hdiff hmixed x0 hgap

end OracleTemplate.MixedNoise
