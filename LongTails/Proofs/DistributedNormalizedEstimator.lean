import LongTails.Proofs.DistributedNormalizedSampling
import LongTails.Proofs.DistributedCompressionIntegration
import LongTails.Proofs.DistributedNormalizedAdaptive
import LongTails.Proofs.DistributedBatchedSgd
import LongTails.Proofs.DistributedNormalizedDrift
import LongTails.Proofs.BacktrackingCompositeBudget

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedEstimator

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open LongTails.Algorithms.DistributedNormalizedCompression

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedCompression.fullReceive
  LongTails.Algorithms.DistributedRandomRounding.message

noncomputable def uplinkCodec (p : Params) (cfg : Config) (x : Point p)
    (θ : ℕ → Fin p.d × ℝ) : Point p :=
  if cfg.fullUplink then
    fullReceive p.d cfg.uplinkWidth cfg.uplinkSpacing
      (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.uplinkWidth cfg.uplinkSpacing x
        (fun j => (θ j.val).2))
  else sparseReceive cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing (fun j => (θ j.val).1)
    (sparseMessage cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing x
      (fun j => (θ j.val).1) (fun j => (θ j.val).2))

set_option maxHeartbeats 800000 in
lemma measurable_uplinkCodec (p : Params) (cfg : Config) :
    Measurable (Function.uncurry (uplinkCodec p cfg)) := by
  unfold uplinkCodec
  cases h : cfg.fullUplink
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (DistributedSparseCompression.measurable_sparse_message_joint
      cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing).comp
      (measurable_fst.prodMk (Measurable.of_eval fun (j : Fin cfg.uplinkCount) =>
        (measurable_pi_apply j.val).comp measurable_snd))
  · simp only [↓reduceIte]
    exact (DistributedSparseCompression.measurable_full_message_joint p.d cfg.uplinkWidth cfg.uplinkSpacing).comp
      (measurable_fst.prodMk (Measurable.of_eval fun (j : Fin p.d) =>
        measurable_snd.comp ((measurable_pi_apply j.val).comp measurable_snd)))

noncomputable def relativeVariance (p : Params) (cfg : Config) : ℝ :=
  if cfg.fullUplink then 0 else ((p.d : ℝ) - 1) / cfg.uplinkCount

noncomputable def gridVariance (p : Params) (cfg : Config) : ℝ :=
  if cfg.fullUplink then p.d * cfg.uplinkSpacing ^ 2 / 4
  else cfg.uplinkSpacing ^ 2 / (4 * cfg.uplinkCount)

lemma uplinkCodec_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (x : Point p) (B : ℝ) (hx : ‖x‖ ≤ B) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * B ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))
    Integrable (uplinkCodec p cfg x) P ∧ (∫ θ, uplinkCodec p cfg x θ ∂P) = x ∧
      Integrable (fun θ => ‖uplinkCodec p cfg x θ - x‖ ^ 2) P ∧
      (∫ θ, ‖uplinkCodec p cfg x θ - x‖ ^ 2 ∂P) ≤
        relativeVariance p cfg * ‖x‖ ^ 2 + gridVariance p cfg := by
  intro P
  change Integrable (fun θ => uplinkCodec p cfg x θ) P ∧ _
  cases h : cfg.fullUplink
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hcap
    have hc (j : Fin p.d) : |(p.d : ℝ) * x j| ≤ cfg.uplinkSpacing *
        (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p.d)]
      have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      exact (mul_le_mul_of_nonneg_left (hj.trans hx) (Nat.cast_nonneg p.d)).trans hcap
    obtain ⟨hi, hm, hi2, hv⟩ := DistributedNormalizedSampling.sparse_stream_moments
      p cfg.uplinkWidth cfg.uplinkCount 0 cfg.uplinkCount.pos hs x hc
    simp only [Nat.zero_add] at hi hm hi2 hv
    simp only [uplinkCodec, relativeVariance, gridVariance, h, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hi, hm, hi2, hv.trans_eq ?_⟩
    have hn : (cfg.uplinkCount : ℝ) ≠ 0 := by exact_mod_cast cfg.uplinkCount.ne_zero
    field_simp
  · simp only [h, ↓reduceIte, one_mul] at hcap
    have hc (j : Fin p.d) : |x j| ≤ cfg.uplinkSpacing *
        (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      exact hj.trans (hx.trans hcap)
    have ht := DistributedNormalizedSampling.full_stream_moments p cfg.uplinkWidth 0 hs x hc
    simpa only [uplinkCodec, relativeVariance, gridVariance, h, ↓reduceIte, Nat.zero_add,
      zero_mul, zero_add] using ht

noncomputable def finiteBatch (p : Params) (cfg : Config)
    (g : Point p → p.Ω → Point p) (x : Point p) (ξ : Fin cfg.batch → p.Ω) : Point p :=
  (cfg.batch : ℝ)⁻¹ • ∑ j, g x (ξ j)

lemma measurable_finiteBatch (p : Params) (cfg : Config)
    (g : Point p → p.Ω → Point p) (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (finiteBatch p cfg g)) := by
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro j _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

lemma finiteBatch_actual (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (i : Fin p.n) (x : Point p) :
    batchMean p cfg g samples k i x =
      finiteBatch p cfg (g i) x (fun j => samples i (k * cfg.batch + j.val)) := by
  unfold batchMean finiteBatch
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => g i x (samples i (k * cfg.batch + j))) cfg.batch).symm

lemma finiteBatch_moments (p : Params) (cfg : Config) (μ : ProbabilityMeasure p.Ω)
    (f : Point p → ℝ) (g : Point p → p.Ω → Point p)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω μ f g p.σ)
    (x : Point p) :
    let P := Measure.pi fun _ : Fin cfg.batch => (μ : Measure p.Ω)
    Integrable (finiteBatch p cfg g x) P ∧ (∫ ξ, finiteBatch p cfg g x ξ ∂P) = gradient f x ∧
      Integrable (fun ξ => ‖finiteBatch p cfg g x ξ - gradient f x‖ ^ 2) P ∧
      (∫ ξ, ‖finiteBatch p cfg g x ξ - gradient f x‖ ^ 2 ∂P) ≤ p.σ ^ 2 / cfg.batch := by
  intro P
  change Integrable (fun ξ => finiteBatch p cfg g x ξ) P ∧ _
  have hm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi, he⟩ := OracleTemplate.LightTail.finite_mean_integral (hg.integrable x) (cfg.batch : ℕ) cfg.batch.pos
  obtain ⟨h2, hv⟩ := OracleTemplate.RobustGradient.finite_mean_variance hm (hg.integrable x)
    (gradient f x) (hg.variance_integrable x) (hg.unbiased x) (cfg.batch : ℕ) cfg.batch.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P, finiteBatch, one_div] using hi
  · simpa only [P, finiteBatch, one_div] using he.trans (hg.unbiased x)
  · simpa only [P, finiteBatch, one_div] using h2
  · simpa only [P, finiteBatch, one_div] using hv.trans_le
      (div_le_div_of_nonneg_right (hg.variance x) (Nat.cast_nonneg (cfg.batch : ℕ)))

lemma relativeVariance_nonneg (p : Params) (cfg : Config) [Nonempty (Fin p.d)] :
    0 ≤ relativeVariance p cfg := by
  have hd : (1 : ℝ) ≤ p.d := by
    have h := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin p.d))
    simp only [Fintype.card_fin] at h
    exact_mod_cast (Nat.succ_le_iff.mpr h)
  unfold relativeVariance
  split_ifs
  · exact le_rfl
  · exact div_nonneg (by linarith) (by positivity)

lemma gridVariance_nonneg (p : Params) (cfg : Config) : 0 ≤ gridVariance p cfg := by
  unfold gridVariance
  split_ifs <;> positivity

lemma uplinkCodec_actual (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (v : Point p) :
    uplinkReceive p cfg D k i (uplinkMessage p cfg D k i v) =
      uplinkCodec p cfg (OracleTemplate.clip cfg.clipRadius v) (D (2 * k) i) := by
  unfold uplinkReceive uplinkMessage uplinkCodec
  cases cfg.fullUplink <;> rfl

noncomputable def workerReply (p : Params) (cfg : Config) (g : Point p → p.Ω → Point p)
    (x : Point p) (z : (Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)) : Point p :=
  uplinkCodec p cfg (OracleTemplate.clip cfg.clipRadius (finiteBatch p cfg g x z.1)) z.2

set_option maxHeartbeats 800000 in
lemma workerReply_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : ProbabilityMeasure p.Ω) (f : Point p → ℝ) (g : Point p → p.Ω → Point p)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p) p.Ω μ f g p.σ)
    (x : Point p) (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) (hx : ‖gradient f x‖ ≤ G)
    (hclip : cfg.clipRadius = G + a) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * (G + a) ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (Measure.pi fun _ : Fin cfg.batch => (μ : Measure p.Ω)).prod
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))
    Integrable (workerReply p cfg g x) P ∧
      Integrable (fun z => ‖workerReply p cfg g x z - gradient f x‖ ^ 2) P ∧
      (∫ z, ‖workerReply p cfg g x z - gradient f x‖ ^ 2 ∂P) ≤
        (1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) +
          relativeVariance p cfg * ‖gradient f x‖ ^ 2 + gridVariance p cfg ∧
      ‖(∫ z, workerReply p cfg g x z ∂P) - gradient f x‖ ≤ (p.σ ^ 2 / cfg.batch) / (4 * a) := by
  intro P
  change Integrable (fun z => workerReply p cfg g x z) P ∧ _
  obtain ⟨hBi, hBmean, hB2, hBvar⟩ := finiteBatch_moments p cfg μ f g hg x
  have hmap : Measurable (fun ξ : Fin cfg.batch → p.Ω => (x, ξ)) :=
    measurable_const.prodMk measurable_id
  have hBm : Measurable (finiteBatch p cfg g x) := (measurable_finiteBatch p cfg g hg.measurable).comp hmap
  have hω := relativeVariance_nonneg p cfg
  have ht := DistributedCompressionIntegration.compressed_clipped_batch_moments
    (Measure.pi fun _ : Fin cfg.batch => (μ : Measure p.Ω))
    (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))
    (finiteBatch p cfg g x) (uplinkCodec p cfg) (gradient f x) hG ha hω hx hBm hBi hB2 hBmean
    (measurable_uplinkCodec p cfg) (fun c hc => uplinkCodec_moments p cfg c (G + a) hc hs hcap)
  have hv := ht.2.2.1.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hBvar (by positivity : 0 ≤ 1 + relativeVariance p cfg)) le_rfl) le_rfl)
  have hb := ht.2.2.2.trans (div_le_div_of_nonneg_right hBvar (by positivity : 0 ≤ 4 * a))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P, workerReply, hclip] using ht.1
  · simpa only [P, workerReply, hclip] using ht.2.1
  · simpa only [P, workerReply, hclip] using hv
  · simpa only [P, workerReply, hclip] using hb

set_option maxHeartbeats 800000 in
lemma independent_worker_error {Z : Type*} [MeasurableSpace Z] (p : Params)
    (μ : Fin p.n → ProbabilityMeasure Z) (Y : Fin p.n → Z → Point p)
    (u : Fin p.n → Point p) (v : Fin p.n → ℝ) (b : ℝ)
    (hYm : ∀ i, Measurable (Y i)) (hYi : ∀ i, Integrable (Y i) (μ i : Measure Z))
    (hY2 : ∀ i, Integrable (fun z => ‖Y i z - u i‖ ^ 2) (μ i : Measure Z))
    (hv : ∀ i, (∫ z, ‖Y i z - u i‖ ^ 2 ∂(μ i : Measure Z)) ≤ v i)
    (hb : ∀ i, ‖(∫ z, Y i z ∂(μ i : Measure Z)) - u i‖ ≤ b) :
    let P := Measure.pi fun i => (μ i : Measure Z)
    Integrable (fun z => ‖(p.n : ℝ)⁻¹ • ∑ i, (Y i (z i) - u i)‖ ^ 2) P ∧
      (∫ z, ‖(p.n : ℝ)⁻¹ • ∑ i, (Y i (z i) - u i)‖ ^ 2 ∂P) ≤
        (p.n : ℝ)⁻¹ ^ 2 * ∑ i, v i + b ^ 2 := by
  intro P
  let X : Fin p.n → (Fin p.n → Z) → Point p := fun i z => Y i (z i) - u i
  have hXm (i : Fin p.n) : Measurable (fun z => Y i z - u i) := (hYm i).sub_const (u i)
  have heval (i : Fin p.n) := measurePreserving_eval (fun j => (μ j : Measure Z)) i
  have hl (i : Fin p.n) : ProbabilityTheory.HasLaw (fun z : Fin p.n → Z => z i)
      (μ i : Measure Z) P := ⟨(heval i).measurable.aemeasurable, (heval i).map_eq⟩
  have hXi (i : Fin p.n) : Integrable (X i) P :=
    (heval i).integrable_comp_of_integrable ((hYi i).sub (integrable_const _))
  have hX2 (i : Fin p.n) : Integrable (fun z => ‖X i z - (0 : Point p)‖ ^ 2) P := by
    simpa only [X, P, sub_zero, Function.comp_def, Function.eval] using (heval i).integrable_comp_of_integrable (hY2 i)
  have hvar (i : Fin p.n) : (∫ z, ‖X i z - (0 : Point p)‖ ^ 2 ∂P) ≤ v i := by
    have he := (hl i).integral_comp ((hXm i).norm.pow_const 2).aestronglyMeasurable
    simpa only [X, sub_zero, Function.comp_def] using he.trans_le (hv i)
  have hmean (i : Fin p.n) : ‖(∫ z, X i z ∂P) - (0 : Point p)‖ ≤ b := by
    have he := (hl i).integral_comp (hXm i).aestronglyMeasurable
    simp only [Function.comp_def] at he
    simp only [X, sub_zero]
    rw [he, integral_sub (hYi i) (integrable_const _)]
    simpa only [integral_const, probReal_univ, one_smul] using hb i
  have hind : ProbabilityTheory.iIndepFun X P :=
    ProbabilityTheory.iIndepFun_pi (μ := fun i => (μ i : Measure Z)) (fun i => (hXm i).aemeasurable)
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have hw : (∑ _i : Fin p.n, (p.n : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn
  obtain ⟨hi, hv'⟩ := DistributedBatchedSgd.independent_weighted_error (p := p.toParams)
    P X 0 (fun _ => (p.n : ℝ)⁻¹) v (fun _ => b) (fun _ => by positivity) hw hind hXi hX2 hvar hmean
  have he (z : Fin p.n → Z) : (∑ i, (p.n : ℝ)⁻¹ • X i z) - 0 =
      (p.n : ℝ)⁻¹ • ∑ i, (Y i (z i) - u i) := by
    simp only [X, sub_zero, Finset.smul_sum]
  simp_rw [he] at hi hv'
  refine ⟨hi, hv'.trans_eq ?_⟩
  rw [← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul]

attribute [local irreducible] uplinkCodec finiteBatch

lemma measurable_workerReply (p : Params) (cfg : Config)
    (g : Point p → p.Ω → Point p) (hg : Measurable (Function.uncurry g))
    (x : Point p) : Measurable (workerReply p cfg g x) := by
  have hB : Measurable (fun z : (Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ) =>
      finiteBatch p cfg g x z.1) :=
    (measurable_finiteBatch p cfg g hg).comp (measurable_const.prodMk measurable_fst)
  have hC : Measurable (fun z : (Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ) =>
      (OracleTemplate.clip cfg.clipRadius (finiteBatch p cfg g x z.1), z.2)) :=
    ((OracleTemplate.measurable_clip cfg.clipRadius).comp hB).prodMk measurable_snd
  unfold workerReply
  exact (measurable_uplinkCodec p cfg).comp hC

noncomputable def workerReplyLaw (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : ProbabilityMeasure p.Ω) :
    ProbabilityMeasure ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)) :=
  ⟨(Measure.pi fun _ : Fin cfg.batch => (μ : Measure p.Ω)).prod
    (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))), inferInstance⟩

set_option maxHeartbeats 800000 in
lemma aggregate_reply_error (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (x : Fin p.n → Point p) (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a)
    (hx : ∀ i, ‖gradient f (x i)‖ ≤ G)
    (hclip : cfg.clipRadius = G + a) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * (G + a) ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := Measure.pi fun i => (workerReplyLaw p cfg (μ i) :
      Measure ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)))
    let R := fun z => (p.n : ℝ)⁻¹ • ∑ i, (workerReply p cfg (g i) (x i) (z i) - gradient f (x i))
    Integrable (fun z => ‖R z‖ ^ 2) P ∧
      (∫ z, ‖R z‖ ^ 2 ∂P) ≤
        (1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) / p.n +
        relativeVariance p cfg / (p.n : ℝ) ^ 2 * ∑ i, ‖gradient f (x i)‖ ^ 2 +
        gridVariance p cfg / p.n + ((p.σ ^ 2 / cfg.batch) / (4 * a)) ^ 2 := by
  intro P R
  have ht (i : Fin p.n) := workerReply_moments p cfg (μ i) f (g i) (hg i) (x i)
    G a hG ha (hx i) hclip hs hcap
  obtain ⟨hi, hv⟩ := independent_worker_error p (fun i => workerReplyLaw p cfg (μ i))
    (fun i => workerReply p cfg (g i) (x i)) (fun i => gradient f (x i))
    (fun i => (1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) +
      relativeVariance p cfg * ‖gradient f (x i)‖ ^ 2 + gridVariance p cfg)
    ((p.σ ^ 2 / cfg.batch) / (4 * a))
    (fun i => measurable_workerReply p cfg (g i) (hg i).measurable (x i))
    (fun i => (ht i).1) (fun i => (ht i).2.1) (fun i => (ht i).2.2.1) (fun i => (ht i).2.2.2)
  refine ⟨hi, hv.trans_eq ?_⟩
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

lemma round_worker_pairs_preserving (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) :
    MeasurePreserving
      (fun z : DistributedNormalizedBlocks.RoundBlock p cfg => fun i => (z.1 i, z.2.1 i))
      (DistributedNormalizedBlocks.roundLaw p cfg μ : Measure (DistributedNormalizedBlocks.RoundBlock p cfg))
      (Measure.pi fun i => (workerReplyLaw p cfg (μ i) :
        Measure ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)))) := by
  let B := Measure.pi fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)
  let U := (DistributedNormalizedBlocks.workerDrawsLaw p : Measure (DistributedNormalizedBlocks.WorkerDraws p))
  have ha := (measurePreserving_prodAssoc B U U).symm MeasurableEquiv.prodAssoc
  have hf := (measurePreserving_fst (μ := B.prod U) (ν := U)).comp ha
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin cfg.batch → p.Ω)
    (ℕ → Fin p.d × ℝ) (Fin p.n)
    (fun i => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω))
    (fun _ => Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))).symm
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin cfg.batch → p.Ω) (ℕ → Fin p.d × ℝ) (Fin p.n))
  exact hp.comp hf

lemma estimator_from_workerReplies (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (ξ : ℕ → DistributedNormalizedBlocks.RoundBlock p cfg) (k : ℕ) (s : Iterate p) :
    estimator p cfg (DistributedNormalizedBlocks.assembledDraws p cfg ξ) g
      (DistributedNormalizedBlocks.assembledSamples p cfg ξ) k s =
      (p.n : ℝ)⁻¹ • ∑ i, workerReply p cfg (g i) (s.workers i) ((ξ k).1 i, (ξ k).2.1 i) := by
  unfold estimator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [uplinkCodec_actual, finiteBatch_actual]
  simp only [workerReply, DistributedNormalizedBlocks.assembled_draws_even,
    DistributedNormalizedBlocks.assembled_sample]

noncomputable def roundEstimator (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Fin p.n → Point p)
    (z : DistributedNormalizedBlocks.RoundBlock p cfg) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, workerReply p cfg (g i) (x i) (z.1 i, z.2.1 i)

lemma measurable_roundEstimator (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (x : Fin p.n → Point p) :
    Measurable (roundEstimator p cfg g x) := by
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro i _
  exact (measurable_workerReply p cfg (g i) (hg i) (x i)).comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))

set_option maxHeartbeats 800000 in
lemma round_estimator_error (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (x : Fin p.n → Point p) (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a)
    (hx : ∀ i, ‖gradient f (x i)‖ ≤ G)
    (hclip : cfg.clipRadius = G + a) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * (G + a) ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (DistributedNormalizedBlocks.roundLaw p cfg μ :
      Measure (DistributedNormalizedBlocks.RoundBlock p cfg))
    let u := (p.n : ℝ)⁻¹ • ∑ i, gradient f (x i)
    Integrable (fun z => ‖roundEstimator p cfg g x z - u‖ ^ 2) P ∧
      (∫ z, ‖roundEstimator p cfg g x z - u‖ ^ 2 ∂P) ≤
        (1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) / p.n +
        relativeVariance p cfg / (p.n : ℝ) ^ 2 * ∑ i, ‖gradient f (x i)‖ ^ 2 +
        gridVariance p cfg / p.n + ((p.σ ^ 2 / cfg.batch) / (4 * a)) ^ 2 := by
  intro P u
  have hl : ProbabilityTheory.HasLaw
      (fun z : DistributedNormalizedBlocks.RoundBlock p cfg => fun i => (z.1 i, z.2.1 i))
      (Measure.pi fun i => (workerReplyLaw p cfg (μ i) :
        Measure ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)))) P :=
    ⟨(round_worker_pairs_preserving p cfg μ).measurable.aemeasurable,
      (round_worker_pairs_preserving p cfg μ).map_eq⟩
  obtain ⟨hi, hv⟩ := aggregate_reply_error p cfg μ f g hg x G a hG ha hx hclip hs hcap
  have he (z : DistributedNormalizedBlocks.RoundBlock p cfg) :
      (p.n : ℝ)⁻¹ • ∑ i, (workerReply p cfg (g i) (x i) (z.1 i, z.2.1 i) - gradient f (x i)) =
      roundEstimator p cfg g x z - u := by
    simp only [roundEstimator, u, Finset.sum_sub_distrib, smul_sub]
  exact ⟨by simpa only [Function.comp_def, he] using hl.integrable_comp hi,
    by simpa only [Function.comp_def, he] using (hl.integral_comp hi.aestronglyMeasurable).trans_le hv⟩

lemma sqrt_compression_variance (p : Params) (G : Point p → Point p)
    (s : DistributedNormalizedAdaptive.State p) {L ω : ℝ} (hL : 0 ≤ L) (hω : 0 ≤ ω)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    Real.sqrt (ω / (p.n : ℝ) ^ 2 * ∑ i, ‖G (s.2 i)‖ ^ 2) ≤
      Real.sqrt (2 * ω / p.n) * ‖G s.1‖ +
        L * Real.sqrt (2 * ω / p.n) * Real.sqrt (DistributedNormalizedDrift.traceError p s) := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have hT : 0 ≤ DistributedNormalizedDrift.traceError p s := by
    unfold DistributedNormalizedDrift.traceError
    positivity
  have hgrad := DistributedNormalizedDrift.average_gradient_square p G s hL hlip
  have he : ω / (p.n : ℝ) ^ 2 * ∑ i, ‖G (s.2 i)‖ ^ 2 =
      (ω / p.n) * ((p.n : ℝ)⁻¹ * ∑ i, ‖G (s.2 i)‖ ^ 2) := by field_simp
  have hb : ω / (p.n : ℝ) ^ 2 * ∑ i, ‖G (s.2 i)‖ ^ 2 ≤
      (2 * ω / p.n) * ‖G s.1‖ ^ 2 +
        ((2 * ω / p.n) * L ^ 2) * DistributedNormalizedDrift.traceError p s := by
    rw [he]
    calc
      _ ≤ (ω / p.n) * (2 * ‖G s.1‖ ^ 2 + 2 * L ^ 2 * DistributedNormalizedDrift.traceError p s) :=
        mul_le_mul_of_nonneg_left hgrad (by positivity)
      _ = _ := by ring
  apply (Real.sqrt_le_sqrt hb).trans
  apply (OracleTemplate.CompositeParameterFree.sqrt_add_le (by positivity) (by positivity)).trans_eq
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * ω / (p.n : ℝ)),
    Real.sqrt_mul (by positivity : 0 ≤ (2 * ω / (p.n : ℝ)) * L ^ 2),
    Real.sqrt_mul (by positivity : 0 ≤ 2 * ω / (p.n : ℝ)),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hL]
  ring

lemma four_term_norm_bound {Z : Type*} [MeasurableSpace Z] (p : Params)
    (P : Measure Z) [IsProbabilityMeasure P] (Y : Z → Point p)
    (hY : Measurable Y) (hY2 : Integrable (fun z => ‖Y z‖ ^ 2) P)
    {A B C b : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hV : (∫ z, ‖Y z‖ ^ 2 ∂P) ≤ A + B + C + b ^ 2) :
    Integrable (fun z => ‖Y z‖) P ∧
      (∫ z, ‖Y z‖ ∂P) ≤ Real.sqrt A + Real.sqrt B + Real.sqrt C + b := by
  have hi : Integrable (fun z => ‖Y z‖) P :=
    (((memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr hY2).integrable (by norm_num)).norm
  refine ⟨hi, ?_⟩
  apply ((OracleTemplate.NormalizedStorm.integral_norm_le_sqrt hY.aestronglyMeasurable hY2).trans
    (Real.sqrt_le_sqrt hV)).trans
  have h1 := OracleTemplate.CompositeParameterFree.sqrt_add_le (add_nonneg (add_nonneg hA hB) hC) (sq_nonneg b)
  have h2 := OracleTemplate.CompositeParameterFree.sqrt_add_le (add_nonneg hA hB) hC
  have h3 := OracleTemplate.CompositeParameterFree.sqrt_add_le hA hB
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] at h1
  linarith

set_option maxHeartbeats 800000 in
lemma conditional_norm_error (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (s : DistributedNormalizedAdaptive.State p) (G a L : ℝ)
    (hG : 0 ≤ G) (ha : 0 < a) (hL : 0 ≤ L)
    (hx : ∀ i, ‖gradient f (s.2 i)‖ ≤ G)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hclip : cfg.clipRadius = G + a) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * (G + a) ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (DistributedNormalizedBlocks.roundLaw p cfg μ :
      Measure (DistributedNormalizedBlocks.RoundBlock p cfg))
    Integrable (fun z => ‖roundEstimator p cfg g s.2 z - gradient f s.1‖) P ∧
      (∫ z, ‖roundEstimator p cfg g s.2 z - gradient f s.1‖ ∂P) ≤
        Real.sqrt ((1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) / p.n) +
        Real.sqrt (2 * relativeVariance p cfg / p.n) * ‖gradient f s.1‖ +
        L * Real.sqrt (2 * relativeVariance p cfg / p.n) *
          Real.sqrt (DistributedNormalizedDrift.traceError p s) +
        Real.sqrt (gridVariance p cfg / p.n) + (p.σ ^ 2 / cfg.batch) / (4 * a) +
        ‖DistributedNormalizedDrift.disagreement p (gradient f) s‖ := by
  intro P
  let u : Point p := (p.n : ℝ)⁻¹ • ∑ i, gradient f (s.2 i)
  have hω := relativeVariance_nonneg p cfg
  have hδ := gridVariance_nonneg p cfg
  obtain ⟨h2, hv⟩ := round_estimator_error p cfg μ f g hg s.2 G a hG ha hx hclip hs hcap
  have hm : Measurable (fun z => roundEstimator p cfg g s.2 z - u) :=
    (measurable_roundEstimator p cfg g (fun i => (hg i).measurable) s.2).sub_const u
  obtain ⟨hi, hb⟩ := four_term_norm_bound p P (fun z => roundEstimator p cfg g s.2 z - u) hm h2
    (by positivity) (by positivity) (by positivity) (by positivity) hv
  have hcompress := sqrt_compression_variance p (gradient f) s hL hω hlip
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have he : u - gradient f s.1 = DistributedNormalizedDrift.disagreement p (gradient f) s := by
    unfold u DistributedNormalizedDrift.disagreement
    rw [Finset.sum_sub_distrib, smul_sub]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hpoint (z : DistributedNormalizedBlocks.RoundBlock p cfg) :
      ‖roundEstimator p cfg g s.2 z - gradient f s.1‖ ≤
        ‖roundEstimator p cfg g s.2 z - u‖ + ‖DistributedNormalizedDrift.disagreement p (gradient f) s‖ := by
    simpa only [he] using norm_sub_le_norm_sub_add_norm_sub (roundEstimator p cfg g s.2 z) u (gradient f s.1)
  have hbound : Integrable (fun z => ‖roundEstimator p cfg g s.2 z - u‖ +
      ‖DistributedNormalizedDrift.disagreement p (gradient f) s‖) P :=
    hi.add (integrable_const ‖DistributedNormalizedDrift.disagreement p (gradient f) s‖)
  have hRi : Integrable (fun z => ‖roundEstimator p cfg g s.2 z - gradient f s.1‖) P :=
    hbound.mono' ((measurable_roundEstimator p cfg g (fun i => (hg i).measurable) s.2).sub_const
      (gradient f s.1)).norm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [norm_norm] using hpoint z)
  refine ⟨hRi, ?_⟩
  have hh := integral_mono hRi hbound hpoint
  rw [integral_add hi (integrable_const _), integral_const] at hh
  simp only [probReal_univ, one_smul] at hh
  linarith

lemma measurable_workerReply_joint (p : Params) (cfg : Config)
    (g : Point p → p.Ω → Point p) (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (workerReply p cfg g)) := by
  have hB : Measurable (fun z : Point p × ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)) =>
      finiteBatch p cfg g z.1 z.2.1) :=
    (measurable_finiteBatch p cfg g hg).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hC : Measurable (fun z : Point p × ((Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ)) =>
      (OracleTemplate.clip cfg.clipRadius (finiteBatch p cfg g z.1 z.2.1), z.2.2)) :=
    ((OracleTemplate.measurable_clip cfg.clipRadius).comp hB).prodMk (measurable_snd.comp measurable_snd)
  unfold workerReply
  exact (measurable_uplinkCodec p cfg).comp hC

attribute [local irreducible] workerReply

lemma measurable_roundEstimator_joint (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (Function.uncurry (roundEstimator p cfg g)) := by
  unfold roundEstimator Function.uncurry
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro i _
  have hmap : Measurable (fun z : (Fin p.n → Point p) × DistributedNormalizedBlocks.RoundBlock p cfg =>
      (z.1 i, (z.2.1 i, z.2.2.1 i))) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  exact (measurable_workerReply_joint p cfg (g i) (hg i)).comp hmap

end LongTails.Proofs.DistributedNormalizedEstimator
