import LongTails.Proofs.BatchedAdamExecution
import LongTails.Proofs.AffineAdamPath
import LongTails.Proofs.AffineAdamBatchMoments
import LongTails.Proofs.AdamHeavyTailedTrajectory

open MeasureTheory

namespace LongTails.Proofs.AffineAdamProbability

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam
open LongTails.Algorithms.AffineHeavyTailedAdam BatchedAdamExecution AffineAdamGeometry

lemma measurable_batchReply {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Point d × (Fin cfg.batchSize → Ω) => batchReply cfg g z.1 z.2) := by
  unfold batchReply
  have hm : Measurable (fun z : Point d × (Fin cfg.batchSize → Ω) => ∑ i, g z.1 (z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact hm.const_smul (cfg.batchSize : ℝ)⁻¹

lemma measurable_process {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (x0 : Point d) (k t : ℕ) :
    Measurable (fun ξ => (process cfg x0 k g ξ t).point) ∧
    Measurable (fun ξ => (process cfg x0 k g ξ t).momentum) ∧
    Measurable (fun ξ => (process cfg x0 k g ξ t).secondMoment) := by
  induction t with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ t ih =>
    have hr := (measurable_batchReply cfg hg).comp (ih.1.prodMk (measurable_pi_apply t))
    have hm := (ih.2.1.const_smul cfg.β₁).add (hr.const_smul (1 - cfg.β₁))
    have hv := (Adam.measurable_secondMomentStep (1 - cfg.β₂)).comp (ih.2.2.prodMk hr)
    refine ⟨?_, hm, hv⟩
    have hd := ((Adam.measurable_direction cfg.δ).comp
      ((hm.const_smul (1 - cfg.β₁ ^ (t + 1))⁻¹).prodMk
        (hv.const_smul (1 - cfg.β₂ ^ (t + 1))⁻¹))).const_smul cfg.η
    simp only [process, coreStep, (process_time cfg x0 k g _ t).1]
    exact ih.1.sub hd

lemma process_congr {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) {ξ ζ : ℕ → Fin cfg.batchSize → Ω} (t : ℕ)
    (he : ∀ j < t, ξ j = ζ j) : process cfg x0 k g ξ t = process cfg x0 k g ζ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [process, process, ih (fun j hj => he j (by omega)), he t (by omega)]

noncomputable def prefixPoint {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) (ω0 : Fin cfg.batchSize → Ω) (t : ℕ)
    (b : Fin t → Fin cfg.batchSize → Ω) : Point d :=
  (process cfg x0 k g (fun j => if hj : j < t then b ⟨j, hj⟩ else ω0) t).point

lemma prefixPoint_stream {d : ℕ} {Ω : Type} (cfg : Config) (x0 : Point d) (k : ℕ)
    (g : Point d → Ω → Point d) (ω0 : Fin cfg.batchSize → Ω) (t : ℕ)
    (ξ : ℕ → Fin cfg.batchSize → Ω) :
    prefixPoint cfg x0 k g ω0 t (fun i => ξ i) = (process cfg x0 k g ξ t).point := by
  unfold prefixPoint
  congr 1
  apply process_congr
  intro j hj
  simp [hj]

lemma measurable_prefixPoint {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (x0 : Point d) (k : ℕ) (ω0 : Fin cfg.batchSize → Ω) (t : ℕ) :
    Measurable (prefixPoint cfg x0 k g ω0 t) := by
  apply (measurable_process cfg hg x0 k t).1.comp
  apply Measurable.of_eval
  intro j
  by_cases hj : j < t
  · simp only [dite_eq_left hj]; exact measurable_pi_apply _
  · simp only [dite_eq_right hj]; exact measurable_const

lemma prefix_sample_law {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ n))
      (Measure.infinitePi fun _ : ℕ => P) ((Measure.pi fun _ : Fin n => P).prod P) := by
  have h := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => P)).prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0)).comp
      (StochasticGeneralized.splitStream_preserving P n)
  change MeasurePreserving (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ (n + 0))) _ _ at h
  simpa only [Nat.add_zero] using h

lemma adaptive_prefix_bound {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (q : (Fin n → Ω) → X)
    (hq : Measurable q) (F : X → Ω → ℝ) (B : X → ℝ)
    (hF : Measurable (Function.uncurry F)) (hF0 : ∀ x ω, 0 ≤ F x ω)
    (hint : ∀ x, Integrable (F x) P) (hbound : ∀ x, (∫ ω, F x ω ∂P) ≤ B x)
    (hBi : Integrable (fun b => B (q b)) (Measure.pi fun _ : Fin n => P)) :
    Integrable (fun ξ : ℕ → Ω => F (q (fun i => ξ i)) (ξ n))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ : ℕ → Ω, F (q (fun i => ξ i)) (ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ∫ b : Fin n → Ω, B (q b) ∂Measure.pi (fun _ => P) := by
  let H := fun z : (Fin n → Ω) × Ω => F (q z.1) z.2
  have hm : Measurable H := hF.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have he (b : Fin n → Ω) : (∫ ω, ‖H (b, ω)‖ ∂P) = ∫ ω, F (q b) ω ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => Real.norm_of_nonneg (hF0 _ _))
  have houter : Integrable (fun b => ∫ ω, ‖H (b, ω)‖ ∂P) (Measure.pi fun _ : Fin n => P) := by
    apply hBi.norm.mono' (hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg _)), he]
    exact (hbound _).trans (le_abs_self _)
  have hprod : Integrable H ((Measure.pi fun _ : Fin n => P).prod P) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall (fun b => hint (q b)), houter⟩
  have hp := prefix_sample_law P n
  refine ⟨hp.integrable_comp_of_integrable hprod, ?_⟩
  change (∫ ξ, H ((fun i : Fin n => ξ i), ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
  have heq := integral_map (μ := Measure.infinitePi (fun _ : ℕ => P)) hp.measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [hp.map_eq] at heq
  rw [← heq, integral_prod _ hprod]
  exact integral_mono hprod.integral_prod_left hBi (fun b => hbound (q b))

lemma batch_error_bound {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) (hB : 0 < cfg.batchSize) (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Point d → Ω → Point d} {f : Point d → ℝ} {p σ1 : ℝ} (σ0 : Fin d → ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ0 : ∀ i, 0 ≤ σ0 i) (hσ1 : 0 ≤ σ1)
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hm : ∀ x, ∫ ω, g x ω ∂P = gradient f x)
    (hpi : ∀ x i, Integrable (fun ω => |(g x ω - gradient f x) i| ^ p) P)
    (hmom : ∀ x i, (∫ ω, |(g x ω - gradient f x) i| ^ p ∂P) ≤
      σ0 i ^ p + σ1 ^ p * |gradient f x i| ^ p) (x : Point d) :
    Integrable (fun b => sumNorm (batchReply cfg g x b - gradient f x))
      (Measure.pi fun _ : Fin cfg.batchSize => P) ∧
    (∫ b, sumNorm (batchReply cfg g x b - gradient f x)
      ∂Measure.pi (fun _ : Fin cfg.batchSize => P)) ≤
      4 * (cfg.batchSize : ℝ) ^ ((1 - p) / p) * ((∑ i, σ0 i) + σ1 * sumNorm (gradient f x)) := by
  have hmean (i : Fin d) : (∫ ω, g x ω i ∂P) = gradient f x i := by
    have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integral_comp_comm (hi x)
    change (∫ ω, g x ω i ∂P) = (∫ ω, g x ω ∂P) i at h
    rw [hm x] at h
    exact h
  have hc (i : Fin d) := AffineAdamBatchMoments.scalar_batch_first_moment
    (X := fun ω => g x ω i) (g := gradient f x i) hp hp2 (hσ0 i) hσ1
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).continuous.measurable.comp
      (hg.comp measurable_prodMk_left))
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).integrable_comp (hi x))
    (hpi x i)
    (hmean i)
    (hmom x i) cfg.batchSize hB
  have he (b : Fin cfg.batchSize → Ω) (i : Fin d) :
      (batchReply cfg g x b - gradient f x) i =
        (cfg.batchSize : ℝ)⁻¹ * ∑ j, g x (b j) i - gradient f x i := by
    simp only [batchReply, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  simp only [sumNorm, he]
  refine ⟨integrable_finsetSum _ (fun i _ => (hc i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hc i).1)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hc i).2)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh ⊢
  exact hh

lemma integrable_process_gradient {d : ℕ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (Q : Measure Ξ) [IsFiniteMeasure Q] (cfg : Config)
    (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (hη : 0 ≤ cfg.η) (hδ : 0 < cfg.δ) (x0 : Point d) (k : ℕ)
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    {f : Point d → ℝ} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, L1 * maxNorm (y - x) ≤ 1 →
      sumNorm (gradient f y - gradient f x) ≤
        (L0 + L1 * sumNorm (gradient f x)) * maxNorm (y - x))
    (hstep : L1 * (80 * cfg.η) ≤ 1)
    (ξ : Ξ → ℕ → Fin cfg.batchSize → Ω) (hξ : Measurable ξ) (t : ℕ) :
    Integrable (fun ω => sumNorm (gradient f (process cfg x0 k g (ξ ω) t).point)) Q := by
  obtain ⟨C, _, hC⟩ := AffineAdamPath.finite_gradient_bound cfg hb1 hb2 hη hδ x0
    hL0 hL1 hlip hstep t
  apply Integrable.of_bound
    ((measurable_sumNorm.comp (measurable_gradient f)).comp
      ((measurable_process cfg hg x0 k t).1.comp hξ)).aestronglyMeasurable C
  filter_upwards [] with ω
  simp only [Function.comp_def]
  rw [Real.norm_of_nonneg (sumNorm_nonneg _), process_eq_trajectory]
  exact hC _ _

lemma process_error_bound {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (cfg : Config) (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (f : Point d → ℝ) (x0 : Point d) (k t : ℕ) {a b : ℝ}
    (hnoise : ∀ x, Integrable (fun ζ => sumNorm (batchReply cfg g x ζ - gradient f x))
      (Measure.pi fun _ : Fin cfg.batchSize => P) ∧
      (∫ ζ, sumNorm (batchReply cfg g x ζ - gradient f x)
        ∂Measure.pi (fun _ : Fin cfg.batchSize => P)) ≤ a + b * sumNorm (gradient f x))
    (hiG : Integrable (fun ξ => sumNorm (gradient f (process cfg x0 k g ξ t).point))
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => P)) :
    Integrable (fun ξ => sumNorm (batchReply cfg g (process cfg x0 k g ξ t).point (ξ t) -
      gradient f (process cfg x0 k g ξ t).point))
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => P) ∧
    (∫ ξ, sumNorm (batchReply cfg g (process cfg x0 k g ξ t).point (ξ t) -
      gradient f (process cfg x0 k g ξ t).point)
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => P)) ≤
      a + b * ∫ ξ, sumNorm (gradient f (process cfg x0 k g ξ t).point)
        ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => P) := by
  let Q := Measure.pi fun _ : Fin cfg.batchSize => P
  let ω0 : Fin cfg.batchSize → Ω := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  let q := prefixPoint cfg x0 k g ω0 t
  have hq : Measurable q := measurable_prefixPoint cfg hg x0 k ω0 t
  have hGm := (measurable_sumNorm.comp (measurable_gradient f)).comp hq
  have hp := StochasticGeneralized.prefix_preserving Q t
  have hiPrefix : Integrable (fun ζ => sumNorm (gradient f (q ζ))) (Measure.pi fun _ : Fin t => Q) := by
    apply (hp.integrable_comp hGm.aestronglyMeasurable).mp
    simpa only [q, Function.comp_def, prefixPoint_stream] using hiG
  have hF : Measurable (fun z : Point d × (Fin cfg.batchSize → Ω) =>
      sumNorm (batchReply cfg g z.1 z.2 - gradient f z.1)) :=
    measurable_sumNorm.comp ((measurable_batchReply cfg hg).sub ((measurable_gradient f).comp measurable_fst))
  have h := adaptive_prefix_bound Q t q hq
    (fun x ζ => sumNorm (batchReply cfg g x ζ - gradient f x))
    (fun x => a + b * sumNorm (gradient f x)) hF (fun _ _ => sumNorm_nonneg _)
    (fun x => (hnoise x).1) (fun x => (hnoise x).2)
    ((integrable_const a).add (hiPrefix.const_mul b))
  simp only [q, prefixPoint_stream] at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [integral_add (integrable_const a) (hiPrefix.const_mul b), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  have he := integral_map (μ := Measure.infinitePi (fun _ : ℕ => Q))
    hp.measurable.aemeasurable hGm.aestronglyMeasurable
  rw [hp.map_eq] at he
  simpa only [q, Function.comp_def, prefixPoint_stream] using congrArg (fun r => b * r) he

end LongTails.Proofs.AffineAdamProbability
