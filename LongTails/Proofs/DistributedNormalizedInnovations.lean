import LongTails.Proofs.DistributedNormalizedSampling
import LongTails.Proofs.DistributedCompressionIntegration
import LongTails.Proofs.DistributedNormalizedBlocks
import LongTails.Proofs.AdaptiveReplicaMoments

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedInnovations

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open LongTails.Algorithms.DistributedNormalizedCompression

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedCompression.fullReceive
  LongTails.Algorithms.DistributedRandomRounding.message

noncomputable def downNoise (p : Params) (cfg : Config) (k : ℕ) (x u : Point p)
    (θ : ℕ → Fin p.d × ℝ) : Point p :=
  if refresh cfg k then
    fullReceive p.d cfg.downlinkWidth cfg.refreshSpacing
      (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.downlinkWidth cfg.refreshSpacing
        (x - p.x0) (fun j => (θ j.val).2)) - (x - p.x0)
  else
    sparseReceive cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
      (fun j => (θ j.val).1) (sparseMessage cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
        u (fun j => (θ j.val).1) (fun j => (θ j.val).2)) - u

lemma downlink_error_identity (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (previous root u : Point p) :
    downlinkReceive p cfg D k i previous (downlinkMessage p cfg D k i (root + u) u) - (root + u) =
      if refresh cfg k then downNoise p cfg k (root + u) u (D (2 * k + 1) i)
      else (previous - root) + downNoise p cfg k (root + u) u (D (2 * k + 1) i) := by
  unfold downlinkReceive downlinkMessage downNoise
  cases h : refresh cfg k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> abel

lemma measurable_downNoise {Z : Type*} [MeasurableSpace Z]
    (p : Params) (cfg : Config) (k : ℕ) {x u : Z → Point p}
    {Θ : Z → ℕ → Fin p.d × ℝ} (hx : Measurable x) (hu : Measurable u)
    (hΘ : Measurable Θ) : Measurable (fun z => downNoise p cfg k (x z) (u z) (Θ z)) := by
  unfold downNoise
  cases h : refresh cfg k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ((DistributedSparseCompression.measurable_sparse_message_joint
      cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing).comp
      (hu.prodMk (Measurable.of_eval fun (q : Fin cfg.downlinkCount) =>
        (measurable_pi_apply q.val).comp hΘ))).sub hu
  · simp only [↓reduceIte]
    have hv := hx.sub_const p.x0
    exact ((DistributedSparseCompression.measurable_full_message_joint
      p.d cfg.downlinkWidth cfg.refreshSpacing).comp
      (hv.prodMk (Measurable.of_eval fun (q : Fin p.d) =>
        measurable_snd.comp ((measurable_pi_apply q.val).comp hΘ)))).sub hv

noncomputable def guardedNoise (p : Params) (cfg : Config) (k : ℕ)
    (root u : Point p) (θ : ℕ → Fin p.d × ℝ) : Point p :=
  if ‖root - p.x0‖ ≤ k * cfg.stepSize then downNoise p cfg k (root + u) u θ else 0

lemma measurable_guardedNoise {Z : Type*} [MeasurableSpace Z]
    (p : Params) (cfg : Config) (k : ℕ) {x u : Z → Point p}
    {Θ : Z → ℕ → Fin p.d × ℝ} (hx : Measurable x) (hu : Measurable u)
    (hΘ : Measurable Θ) : Measurable (fun z => guardedNoise p cfg k (x z) (u z) (Θ z)) := by
  unfold guardedNoise
  exact Measurable.ite (measurableSet_le (hx.sub_const p.x0).norm measurable_const)
    (measurable_downNoise p cfg k (hx.add hu) hu hΘ) measurable_const

lemma guardedNoise_eq (p : Params) (cfg : Config) (k : ℕ) (root u : Point p)
    (θ : ℕ → Fin p.d × ℝ) (hroot : ‖root - p.x0‖ ≤ k * cfg.stepSize) :
    guardedNoise p cfg k root u θ = downNoise p cfg k (root + u) u θ := by
  simp only [guardedNoise, hroot, ↓reduceIte]

lemma down_noise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (k : ℕ)
    (x u : Point p) (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hr : ∀ j, |(x - p.x0) j| ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hi : ∀ j, |(p.d : ℝ) * u j| ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))
    Integrable (downNoise p cfg k x u) P ∧
      (∫ θ, downNoise p cfg k x u θ ∂P) = 0 ∧
      Integrable (fun θ => ‖downNoise p cfg k x u θ‖ ^ 2) P ∧
      (∫ θ, ‖downNoise p cfg k x u θ‖ ^ 2 ∂P) ≤
        if refresh cfg k then p.d * cfg.refreshSpacing ^ 2 / 4
        else (((p.d : ℝ) - 1) * ‖u‖ ^ 2 + cfg.incrementSpacing ^ 2 / 4) / cfg.downlinkCount := by
  intro P
  change Integrable (fun θ => downNoise p cfg k x u θ) P ∧ _
  cases h : refresh cfg k
  · obtain ⟨hint, hmean, hint2, hvar⟩ := DistributedNormalizedSampling.sparse_stream_moments
      p cfg.downlinkWidth cfg.downlinkCount 0 cfg.downlinkCount.pos hsi u hi
    simp only [Nat.zero_add] at hint hmean hint2 hvar
    have hz := hint.sub (integrable_const u)
    have hm : (∫ θ, sparseReceive cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
        (fun j => (θ j.val).1) (sparseMessage cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
          u (fun j => (θ j.val).1) (fun j => (θ j.val).2)) - u ∂P) = 0 := by
      rw [integral_sub hint (integrable_const u), hmean]
      simp
    simp only [downNoise, h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hz, hm, hint2, hvar⟩
  · obtain ⟨hint, hmean, hint2, hvar⟩ := DistributedNormalizedSampling.full_stream_moments
      p cfg.downlinkWidth 0 hsr (x - p.x0) hr
    simp only [Nat.zero_add] at hint hmean hint2 hvar
    have hz := hint.sub (integrable_const (x - p.x0))
    have hm : (∫ θ, fullReceive p.d cfg.downlinkWidth cfg.refreshSpacing
        (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.downlinkWidth cfg.refreshSpacing
          (x - p.x0) (fun j => (θ j.val).2)) - (x - p.x0) ∂P) = 0 := by
      rw [integral_sub hint (integrable_const (x - p.x0)), hmean]
      simp
    simp only [downNoise, h, ↓reduceIte]
    exact ⟨hz, hm, hint2, hvar⟩

lemma down_noise_uniform_bound (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (k : ℕ) (x u : Point p) (hu : ‖u‖ ≤ cfg.stepSize)
    (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hr : ∀ j, |(x - p.x0) j| ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hi : ∀ j, |(p.d : ℝ) * u j| ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    (∫ θ, ‖downNoise p cfg k x u θ‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))) ≤
        if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount := by
  have hd : 1 ≤ (p.d : ℝ) := by
    have h := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin p.d))
    simp only [Fintype.card_fin] at h
    exact_mod_cast (Nat.succ_le_iff.mpr h)
  have hsq := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (p.d : ℝ) - 1 by linarith)
  have ht := (down_noise_moments p cfg k x u hsr hsi hr hi).2.2.2
  apply ht.trans
  cases h : refresh cfg k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg cfg.stepSize]
  · simp only [↓reduceIte]
    linarith

lemma guarded_noise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (K k : ℕ) (hk : k < K) (root u : Point p) (hη : 0 ≤ cfg.stepSize)
    (hu : ‖u‖ ≤ cfg.stepSize) (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    let P := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))
    Integrable (guardedNoise p cfg k root u) P ∧
      (∫ θ, guardedNoise p cfg k root u θ ∂P) = 0 ∧
      Integrable (fun θ => ‖guardedNoise p cfg k root u θ‖ ^ 2) P ∧
      (∫ θ, ‖guardedNoise p cfg k root u θ‖ ^ 2 ∂P) ≤
        if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount := by
  intro P
  change Integrable (fun θ => guardedNoise p cfg k root u θ) P ∧ _
  by_cases hroot : ‖root - p.x0‖ ≤ k * cfg.stepSize
  · have hnorm : ‖root + u - p.x0‖ ≤ K * cfg.stepSize := by
      have he : root + u - p.x0 = (root - p.x0) + u := by abel
      rw [he]
      have hcast : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
      calc
        _ ≤ ‖root - p.x0‖ + ‖u‖ := norm_add_le _ _
        _ ≤ k * cfg.stepSize + cfg.stepSize := add_le_add hroot hu
        _ = ((k : ℝ) + 1) * cfg.stepSize := by ring
        _ ≤ K * cfg.stepSize := mul_le_mul_of_nonneg_right hcast hη
    have hr (j : Fin p.d) : |(root + u - p.x0) j| ≤ cfg.refreshSpacing *
        (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      have hcoord : |(root + u - p.x0) j| ≤ ‖root + u - p.x0‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (root + u - p.x0) j
      exact hcoord.trans (hnorm.trans hcapr)
    have hi (j : Fin p.d) : |(p.d : ℝ) * u j| ≤ cfg.incrementSpacing *
        (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p.d)]
      have hcoord : |u j| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u j
      exact (mul_le_mul_of_nonneg_left (hcoord.trans hu) (Nat.cast_nonneg p.d)).trans hcapi
    obtain ⟨hint, h0, h2, _⟩ := down_noise_moments p cfg k (root + u) u hsr hsi hr hi
    simp only [guardedNoise, hroot, ↓reduceIte]
    exact ⟨hint, h0, h2, down_noise_uniform_bound p cfg k (root + u) u hu hsr hsi hr hi hvr hvi⟩
  · simp only [guardedNoise, hroot, ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
    refine ⟨integrable_const _, trivial, integrable_const _, ?_⟩
    split_ifs <;> positivity

lemma guarded_average_noise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (K k : ℕ) (hk : k < K) (root u : Point p) (hη : 0 ≤ cfg.stepSize)
    (hu : ‖u‖ ≤ cfg.stepSize) (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    let P := (DistributedNormalizedBlocks.workerDrawsLaw p : Measure (DistributedNormalizedBlocks.WorkerDraws p))
    let Y := fun θ : DistributedNormalizedBlocks.WorkerDraws p =>
      (p.n : ℝ)⁻¹ • ∑ i, guardedNoise p cfg k root u (θ i)
    Integrable Y P ∧ (∫ θ, Y θ ∂P) = 0 ∧
      Integrable (fun θ => ‖Y θ‖ ^ 2) P ∧
      (∫ θ, ‖Y θ‖ ^ 2 ∂P) ≤
        (if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount) / p.n := by
  intro P Y
  obtain ⟨hint, hmean, hint2, hvar⟩ := guarded_noise_moments p cfg K k hk root u hη hu hsr hsi hcapi hcapr hvr hvi
  have hm : Measurable (guardedNoise p cfg k root u) :=
    measurable_guardedNoise p cfg k measurable_const measurable_const measurable_id
  have h2 : Integrable (fun θ => ‖guardedNoise p cfg k root u θ - 0‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) := by
    simpa only [sub_zero] using hint2
  have hv : (∫ θ, ‖guardedNoise p cfg k root u θ - 0‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ)))) ≤
        if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount := by
    simpa only [sub_zero] using hvar
  have ht := AdaptiveReplicaMoments.batch_error_moments (guardedNoise p cfg k root u)
    hm hint 0 hmean h2 _ hv (p.n : ℕ) p.n.pos
  simpa only [P, Y, DistributedNormalizedBlocks.workerDrawsLaw, ProbabilityMeasure.coe_mk,
    one_div, sub_zero] using ht

lemma average_down_noise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (k : ℕ)
    (x u : Point p) (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hr : ∀ j, |(x - p.x0) j| ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hi : ∀ j, |(p.d : ℝ) * u j| ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let P := (DistributedNormalizedBlocks.workerDrawsLaw p : Measure (DistributedNormalizedBlocks.WorkerDraws p))
    let Y := fun θ : DistributedNormalizedBlocks.WorkerDraws p =>
      (p.n : ℝ)⁻¹ • ∑ i, downNoise p cfg k x u (θ i)
    Integrable Y P ∧ (∫ θ, Y θ ∂P) = 0 ∧
      Integrable (fun θ => ‖Y θ‖ ^ 2) P ∧
      (∫ θ, ‖Y θ‖ ^ 2 ∂P) ≤
        (if refresh cfg k then p.d * cfg.refreshSpacing ^ 2 / 4
        else (((p.d : ℝ) - 1) * ‖u‖ ^ 2 + cfg.incrementSpacing ^ 2 / 4) / cfg.downlinkCount) / p.n := by
  intro P Y
  obtain ⟨hint, hmean, hint2, hvar⟩ := down_noise_moments p cfg k x u hsr hsi hr hi
  have hm : Measurable (downNoise p cfg k x u) :=
    measurable_downNoise p cfg k measurable_const measurable_const measurable_id
  obtain ⟨hYi, hYm⟩ := OracleTemplate.LightTail.finite_mean_integral hint (p.n : ℕ) p.n.pos
  have h2 : Integrable (fun θ => ‖downNoise p cfg k x u θ - 0‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) := by
    simpa only [sub_zero] using hint2
  obtain ⟨hY2, hYv⟩ := OracleTemplate.RobustGradient.finite_mean_variance hm hint 0 h2 hmean (p.n : ℕ) p.n.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [P, Y, DistributedNormalizedBlocks.workerDrawsLaw, ProbabilityMeasure.coe_mk, one_div] using hYi
  · simpa only [P, Y, DistributedNormalizedBlocks.workerDrawsLaw, ProbabilityMeasure.coe_mk, one_div] using hYm.trans hmean
  · simpa only [P, Y, DistributedNormalizedBlocks.workerDrawsLaw, ProbabilityMeasure.coe_mk, one_div, sub_zero] using hY2
  · simpa only [P, Y, DistributedNormalizedBlocks.workerDrawsLaw, ProbabilityMeasure.coe_mk, one_div, sub_zero] using hYv.trans_le
      (div_le_div_of_nonneg_right (by simpa only [sub_zero] using hvar) (Nat.cast_nonneg (p.n : ℕ)))

end LongTails.Proofs.DistributedNormalizedInnovations
