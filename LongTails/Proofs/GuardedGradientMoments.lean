import LongTails.Proofs.GapStrongGrowthAccuracy
import LongTails.Proofs.HeavyTailedFreshProcess
import LongTails.Proofs.HilbertSmallMoments
import LongTails.Proofs.MultiplicativeRobustConfidence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.GuardedGradientMoments

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

lemma finite_batch_centered_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]
    {e : Ω → E} (he : Measurable e) {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable e P) (hm : (∫ ω, e ω ∂P) = 0)
    (hpi : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ κ) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ k : Fin n, e (ξ k)‖ ^ p)
      (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ : Fin n → Ω, ‖(n : ℝ)⁻¹ • ∑ k : Fin n, e (ξ k)‖ ^ p
        ∂Measure.pi (fun _ : Fin n => P)) ≤ 6 * κ / (n : ℝ) ^ (p - 1) := by
  let F := fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ k : Fin n, e (ξ k)‖ ^ p
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hprefix := OracleTemplate.StochasticGeneralized.prefix_preserving P n
  have hh := HeavyTailedFreshProcess.iid_batch_moment P he hp hp2 hi hm hpi hb n hn
  have heq (ξ : ℕ → Ω) : F (fun k => ξ k) =
      ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)‖ ^ p := by
    simp only [F, Fin.sum_univ_eq_sum_range (fun k => e (ξ k))]
  have hfi : Integrable (fun ξ : ℕ → Ω => F (fun k => ξ k))
      (Measure.infinitePi fun _ : ℕ => P) := by simpa only [heq] using hh.1
  refine ⟨(hprefix.integrable_comp hF.aestronglyMeasurable).mp hfi, ?_⟩
  change (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin n => P)) ≤ _
  rw [← hprefix.map_eq, integral_map hprefix.measurable.aemeasurable hF.aestronglyMeasurable]
  simpa only [heq] using hh.2

lemma finite_batch_accuracy {Ω : Type} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → E} (hg : Measurable g) (u : E) {p κ r : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hr : 0 ≤ r)
    (hi : Integrable g P) (hm : (∫ ω, g ω ∂P) = u)
    (hpi : Integrable (fun ω => ‖g ω - u‖ ^ p) P)
    (hb : (∫ ω, ‖g ω - u‖ ^ p ∂P) ≤ κ)
    (n : ℕ) (hn : 0 < n) (hsize : 6 * κ / (n : ℝ) ^ (p - 1) ≤ r ^ p) :
    Integrable (fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ k : Fin n, g (ξ k) - u‖)
      (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ : Fin n → Ω, ‖(n : ℝ)⁻¹ • ∑ k : Fin n, g (ξ k) - u‖
        ∂Measure.pi (fun _ : Fin n => P)) ≤ r := by
  have he : (∫ ω, g ω - u ∂P) = 0 := by
    rw [integral_sub hi (integrable_const _), hm, integral_const]
    simp
  have hh := finite_batch_centered_moment (hg.sub_const u) hp hp2
    (hi.sub (integrable_const u)) he hpi hb n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq (ξ : Fin n → Ω) :
      (n : ℝ)⁻¹ • ∑ k : Fin n, (g (ξ k) - u) = (n : ℝ)⁻¹ • ∑ k : Fin n, g (ξ k) - u := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hnR, one_smul]
  simp_rw [heq] at hh
  have hmz : Measurable (fun ξ : Fin n → Ω => (n : ℝ)⁻¹ • ∑ k : Fin n, g (ξ k) - u) := by
    fun_prop
  have hfirst : Integrable (fun ξ : Fin n → Ω => ‖(n : ℝ)⁻¹ • ∑ k : Fin n, g (ξ k) - u‖)
      (Measure.pi fun _ : Fin n => P) := by
    have h := integrable_norm_rpow_of_le hmz.aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ p) hp hh.1
    simpa using h
  exact ⟨hfirst, HilbertSmallMoments.first_power_from_moment hp hr hfirst hh.1
    (hh.2.trans hsize)⟩

lemma relative_affine_moment {σ α G M p : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hG : 0 ≤ G) (hM : 0 < M) (hp : 1 ≤ p) :
    σ ^ p + α ^ p * G ^ p ≤ (σ / M + α) ^ p * (M + G) ^ p := by
  have hlinear : σ + α * G ≤ (σ / M + α) * (M + G) := by
    have he : σ / M * M = σ := div_mul_cancel₀ _ hM.ne'
    nlinarith [mul_nonneg (div_nonneg hσ hM.le) hG, mul_nonneg hα hM.le]
  have h := (Real.add_rpow_le_rpow_add hσ (mul_nonneg hα hG) hp).trans
    (Real.rpow_le_rpow (by positivity) hlinear (by linarith : 0 ≤ p))
  simpa only [Real.mul_rpow hα hG,
    Real.mul_rpow (show 0 ≤ σ / M + α by positivity) (show 0 ≤ M + G by positivity)] using h

lemma relative_batch_size {σ α G M p : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hG : 0 ≤ G) (hM : 0 < M) (hp : 1 ≤ p)
    (n : ℕ) (hsize : 6 * (σ / M + α) ^ p / (n : ℝ) ^ (p - 1) ≤ (1 / 24576 : ℝ) ^ p) :
    6 * (σ ^ p + α ^ p * G ^ p) / (n : ℝ) ^ (p - 1) ≤ ((M + G) / 24576) ^ p := by
  have hκ := relative_affine_moment hσ hα hG hM hp
  have h₁ := mul_le_mul_of_nonneg_left hκ (show 0 ≤ 6 / (n : ℝ) ^ (p - 1) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (by positivity : 0 ≤ M + G) p)
  have he : ((M + G) / 24576) ^ p = (1 / 24576 : ℝ) ^ p * (M + G) ^ p := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 24576) (by positivity)]
    congr 1
    ring
  rw [he]
  calc
    _ ≤ (6 * (σ / M + α) ^ p / (n : ℝ) ^ (p - 1)) * (M + G) ^ p := by
      convert h₁ using 1 <;> ring
    _ ≤ _ := h₂

lemma guard_batch_size_suffices {r p : ℝ} (hr : 0 ≤ r) (hp : 1 < p)
    (B : ℕ) (hB : 0 < B) (hsize : (1048576 * r) ^ (p / (p - 1)) ≤ (B : ℝ)) :
    6 * r ^ p / (B : ℝ) ^ (p - 1) ≤ (1 / 24576 : ℝ) ^ p := by
  have hp' : 0 < p - 1 := by linarith
  have hBp : 0 < (B : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (by exact_mod_cast hB) _
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _)
    hsize hp'.le
  rw [← Real.rpow_mul (by positivity : 0 ≤ 1048576 * r),
    div_mul_cancel₀ p hp'.ne'] at hpow
  have hc : (6 : ℝ) ≤ (1048576 / 24576 : ℝ) ^ p :=
    (by norm_num : (6 : ℝ) ≤ 1048576 / 24576).trans
      (Real.self_le_rpow_of_one_le (by norm_num) hp.le)
  have hmul := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr p)
  have he : (1048576 / 24576 : ℝ) ^ p * r ^ p =
      (1 / 24576 : ℝ) ^ p * (1048576 * r) ^ p := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1048576 / 24576) hr,
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 24576) (by positivity)]
    congr 1
    ring
  rw [he] at hmul
  apply (div_le_iff₀ hBp).mpr
  exact hmul.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

lemma shifted_block_tail {E : Type*} [NormedAddCommGroup E]
    {P : Measure Ω} {X : Ω → E} (u : E) {M : ℝ} (hM : 0 < M)
    (hi : Integrable (fun ω => ‖X ω - u‖) P)
    (hm : (∫ ω, ‖X ω - u‖ ∂P) ≤ (M + ‖u‖) / 24576) :
    P.real {ω | (M + ‖u‖) / 96 < ‖X ω - u‖} ≤ 1 / 256 := by
  have hr : 0 < (M + ‖u‖) / 96 := by positivity
  have h := (hi.div_const ((M + ‖u‖) / 96)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (norm_nonneg _) hr.le))
    (s := {ω | (M + ‖u‖) / 96 < ‖X ω - u‖})
    (fun ω hω => (one_le_div hr).mpr hω.le)
  have hb : P {ω | (M + ‖u‖) / 96 < ‖X ω - u‖} ≤
      ENNReal.ofReal (1 / 256 : ℝ) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    apply (div_le_iff₀ hr).mpr
    linarith
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (by norm_num : (0 : ℝ) ≤ 1 / 256)] using ht

lemma shifted_medoid_failure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E}
    (hX : Measurable X) (u : E) {M : ℝ} (hM : 0 < M)
    (hi : Integrable (fun ω => ‖X ω - u‖) P)
    (hm : (∫ ω, ‖X ω - u‖ ∂P) ≤ (M + ‖u‖) / 24576) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | (M + ‖u‖) / 16 <
        ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have h := OracleTemplate.MultiplicativeRobustEstimator.medoid_failure_probability
    hX u (by positivity : 0 ≤ (M + ‖u‖) / 96)
    (shifted_block_tail u hM hi hm) n
  simpa only [show 6 * ((M + ‖u‖) / 96) = (M + ‖u‖) / 16 by ring] using h

lemma batched_medoid_failure {Ω : Type} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (u : E) {p σ α M : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M)
    (hi : Integrable g P) (hm : (∫ ω, g ω ∂P) = u)
    (hpi : Integrable (fun ω => ‖g ω - u‖ ^ p) P)
    (hb : (∫ ω, ‖g ω - u‖ ^ p ∂P) ≤ σ ^ p + α ^ p * ‖u‖ ^ p)
    (B : ℕ) (hB : 0 < B)
    (hsize : 6 * (σ / M + α) ^ p / (B : ℝ) ^ (p - 1) ≤ (1 / 24576 : ℝ) ^ p)
    (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin B => P)
      {ξ | (M + ‖u‖) / 16 <
        ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
          (fun j => (B : ℝ)⁻¹ • ∑ k : Fin B, g (ξ j k)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hh := finite_batch_accuracy hg u hp hp2
    (by positivity : 0 ≤ (M + ‖u‖) / 24576) hi hm hpi hb B hB
    (relative_batch_size hσ hα (norm_nonneg _) hM hp B hsize)
  exact shifted_medoid_failure (by fun_prop) u hM hh.1 hh.2 n

lemma stream_medoid_failure {Ω : Type} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    {g : Ω → E} (hg : Measurable g) (u : E) {p σ α M : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M)
    (hi : Integrable g P) (hm : (∫ ω, g ω ∂P) = u)
    (hpi : Integrable (fun ω => ‖g ω - u‖ ^ p) P)
    (hb : (∫ ω, ‖g ω - u‖ ^ p ∂P) ≤ σ ^ p + α ^ p * ‖u‖ ^ p)
    (B : ℕ) (hB : 0 < B)
    (hsize : 6 * (σ / M + α) ^ p / (B : ℝ) ^ (p - 1) ≤ (1 / 24576 : ℝ) ^ p)
    (n : ℕ) :
    Q {ξ | (M + ‖u‖) / 16 <
        ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
          (fun j : Fin (n + 1) => (B : ℝ)⁻¹ •
            ∑ k ∈ Finset.range B, g (ξ (j.val * B + k))) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  have hblocks := OracleTemplate.GapStrongGrowth.iid_groups_law P Q hIID (n + 1) B
  have hbound := batched_medoid_failure hg u hp hp2 hσ hα hM hi hm hpi hb B hB hsize n
  have hset : MeasurableSet {ξ : Fin (n + 1) → Fin B → Ω |
      (M + ‖u‖) / 16 < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j => (B : ℝ)⁻¹ • ∑ k : Fin B, g (ξ j k)) - u‖} := by
    apply measurableSet_lt measurable_const
    exact ((OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
      (by fun_prop)).sub_const u).norm
  rw [← hblocks.measure_preimage hset.nullMeasurableSet] at hbound
  have heq (ξ : ℕ → Ω) (j : Fin (n + 1)) :
      (∑ k : Fin B, g (ξ (j.val * B + k.val))) =
        ∑ k ∈ Finset.range B, g (ξ (j.val * B + k)) :=
    Fin.sum_univ_eq_sum_range (fun k => g (ξ (j.val * B + k))) B
  simpa only [Set.preimage_ofPred_eq, heq] using hbound

lemma guard_accept_of_accurate {E : Type*} [NormedAddCommGroup E]
    {u z : E} {M : ℝ} (hu : ‖u‖ ≤ M)
    (he : ‖z - u‖ ≤ (M + ‖u‖) / 16) : ‖z‖ ≤ 3 * M / 2 := by
  have ht := norm_le_norm_sub_add z u
  nlinarith [norm_nonneg u]

lemma guard_reject_of_accurate {E : Type*} [NormedAddCommGroup E]
    {u z : E} {M : ℝ} (hM : 0 ≤ M) (hu : 2 * M < ‖u‖)
    (he : ‖z - u‖ ≤ (M + ‖u‖) / 16) : 3 * M / 2 < ‖z‖ := by
  have ht := norm_le_norm_sub_add u z
  rw [norm_sub_rev u z] at ht
  linarith

lemma guard_probability_bounds {E : Type*} [NormedAddCommGroup E]
    {P : Measure Ω} {X : Ω → E} (u : E) {M : ℝ} (hM : 0 ≤ M)
    {δ : ENNReal}
    (herr : P {ω | (M + ‖u‖) / 16 < ‖X ω - u‖} ≤ δ) :
    (‖u‖ ≤ M → P {ω | 3 * M / 2 < ‖X ω‖} ≤ δ) ∧
      (2 * M < ‖u‖ → P {ω | ‖X ω‖ ≤ 3 * M / 2} ≤ δ) := by
  constructor
  · intro hu
    apply (measure_mono ?_).trans herr
    intro ω hω
    by_contra hn
    exact (not_le_of_gt hω) (guard_accept_of_accurate hu (le_of_not_gt hn))
  · intro hu
    apply (measure_mono ?_).trans herr
    intro ω hω
    by_contra hn
    exact (not_lt_of_ge hω) (guard_reject_of_accurate hM hu (le_of_not_gt hn))

lemma guard_second_moment {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {G U M : ℝ}
    (hG : 0 ≤ G) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hgrowth : U ≤ 2 * max G M)
    (hmiss : 2 * M < U → P.real A ≤ 1 / 16) :
    (∫ ω, A.indicator (fun _ => U ^ 2) ω ∂P) ≤ G ^ 2 / 2 + 4 * M ^ 2 := by
  rw [integral_indicator_const _ hA, smul_eq_mul]
  by_cases hsmall : U ≤ 2 * M
  · have hprob : P.real A ≤ 1 := measureReal_le_one
    have hmul := mul_le_mul_of_nonneg_right hprob (sq_nonneg U)
    nlinarith [sq_nonneg G]
  · have hprob := hmiss (lt_of_not_ge hsmall)
    have hmul := mul_le_mul_of_nonneg_right hprob (sq_nonneg U)
    rcases le_total G M with h | h
    · rw [max_eq_right h] at hgrowth
      nlinarith
    · rw [max_eq_left h] at hgrowth
      nlinarith [sq_nonneg M]

lemma stream_guard_second_moment {Ω : Type} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    {g : Ω → E} (hg : Measurable g) (u : E) {p σ α M G : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hM : 0 < M)
    (hi : Integrable g P) (hm : (∫ ω, g ω ∂P) = u)
    (hpi : Integrable (fun ω => ‖g ω - u‖ ^ p) P)
    (hb : (∫ ω, ‖g ω - u‖ ^ p ∂P) ≤ σ ^ p + α ^ p * ‖u‖ ^ p)
    (B : ℕ) (hB : 0 < B)
    (hsize : 6 * (σ / M + α) ^ p / (B : ℝ) ^ (p - 1) ≤ (1 / 24576 : ℝ) ^ p)
    (n : ℕ) (hgroups : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 16)
    (hG : 0 ≤ G) (hgrowth : ‖u‖ ≤ 2 * max G M) :
    let accepted := fun ξ : ℕ → Ω =>
      ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j : Fin (n + 1) => (B : ℝ)⁻¹ •
          ∑ k ∈ Finset.range B, g (ξ (j.val * B + k)))‖ ≤ 3 * M / 2
    Integrable (fun ξ => if accepted ξ then ‖u‖ ^ 2 else 0) Q ∧
      (∫ ξ, if accepted ξ then ‖u‖ ^ 2 else 0 ∂Q) ≤ G ^ 2 / 2 + 4 * M ^ 2 := by
  let X := fun ξ : ℕ → Ω => OracleTemplate.MultiplicativeRobustEstimator.medoid
    (fun j : Fin (n + 1) => (B : ℝ)⁻¹ •
      ∑ k ∈ Finset.range B, g (ξ (j.val * B + k)))
  have hX : Measurable X :=
    OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp (by fun_prop)
  have hA : MeasurableSet {ξ | ‖X ξ‖ ≤ 3 * M / 2} :=
    measurableSet_le hX.norm measurable_const
  have he := stream_medoid_failure Q hIID hg u hp hp2 hσ hα hM hi hm hpi hb B hB hsize n
  have hmiss (hu : 2 * M < ‖u‖) : Q.real {ξ | ‖X ξ‖ ≤ 3 * M / 2} ≤ 1 / 16 := by
    have hh := (guard_probability_bounds u hM.le he).2 hu
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hh.trans (ENNReal.ofReal_le_ofReal hgroups))
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16)] using ht
  have hbound := guard_second_moment hA hG (norm_nonneg u) hM.le hgrowth hmiss
  have hint := (integrable_const (‖u‖ ^ 2) : Integrable (fun _ : ℕ → Ω => ‖u‖ ^ 2) Q).indicator hA
  have heq : ({ξ | ‖X ξ‖ ≤ 3 * M / 2}.indicator (fun _ => ‖u‖ ^ 2)) =
      (fun ξ => if ‖X ξ‖ ≤ 3 * M / 2 then ‖u‖ ^ 2 else 0) := by
    funext ξ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq] at hint hbound
  exact ⟨hint, hbound⟩

lemma uniform_second_moment {a : ℕ → ℝ} {M : ℝ}
    (hinit : a 0 ≤ 8 * M ^ 2)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2 + 4 * M ^ 2) (n : ℕ) :
    a n ≤ 8 * M ^ 2 := by
  induction n with
  | zero => exact hinit
  | succ n ih => linarith [hstep n]

lemma integrated_guard_transition {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {G U : S → ℝ} {M : ℝ} (hU : Measurable U)
    (hGi : Integrable (fun s => G s ^ 2) μ)
    (hG : ∀ s, 0 ≤ G s) (hUn : ∀ s, 0 ≤ U s) (hM : 0 ≤ M)
    (A : S → Set Ω) (hA : MeasurableSet {w : S × Ω | w.2 ∈ A w.1})
    (hgrowth : ∀ s, U s ≤ 2 * max (G s) M)
    (hmiss : ∀ s, 2 * M < U s → P.real (A s) ≤ 1 / 16) :
    Integrable (fun w : S × Ω => (A w.1).indicator (fun _ => U w.1 ^ 2) w.2)
      (μ.prod P) ∧
    (∫ w : S × Ω, (A w.1).indicator (fun _ => U w.1 ^ 2) w.2 ∂μ.prod P) ≤
      (∫ s, G s ^ 2 ∂μ) / 2 + 4 * M ^ 2 := by
  classical
  let F : S × Ω → ℝ := fun w => (A w.1).indicator (fun _ => U w.1 ^ 2) w.2
  have hFm : Measurable F := by
    change Measurable ({w : S × Ω | w.2 ∈ A w.1}.indicator
      (fun w => U w.1 ^ 2))
    exact ((hU.comp measurable_fst).pow_const 2).indicator hA
  have hbound (w : S × Ω) : ‖F w‖ ≤ 4 * G w.1 ^ 2 + 4 * M ^ 2 := by
    dsimp [F]
    by_cases ha : w.2 ∈ A w.1
    · rw [Set.indicator_of_mem ha, abs_of_nonneg (sq_nonneg _)]
      have hg := hgrowth w.1
      rcases le_total (G w.1) M with h | h
      · rw [max_eq_right h] at hg
        nlinarith [hUn w.1, sq_nonneg (G w.1)]
      · rw [max_eq_left h] at hg
        nlinarith [hUn w.1, hG w.1, sq_nonneg M]
    · rw [Set.indicator_of_notMem ha, abs_zero]
      positivity
  have hFi : Integrable F (μ.prod P) :=
    (((hGi.const_mul 4).add (integrable_const (4 * M ^ 2))).comp_fst P).mono'
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨hFi, ?_⟩
  change (∫ w, F w ∂μ.prod P) ≤ _
  rw [integral_prod _ hFi]
  have hb := integral_mono hFi.integral_prod_left
    ((hGi.div_const 2).add (integrable_const (4 * M ^ 2))) (fun s =>
      guard_second_moment (hA.preimage measurable_prodMk_left)
        (hG s) (hUn s) hM (hgrowth s) (hmiss s))
  simpa only [Pi.add_apply, integral_add (hGi.div_const 2) (integrable_const _),
    integral_div, integral_const, probReal_univ, one_smul] using hb

lemma selected_norm_le {E : Type*} [NormedAddCommGroup E] {ι : Type*}
    (g estimate : ι → E) (chosen comparator : ι)
    (hchoice : ‖estimate chosen‖ ≤ ‖estimate comparator‖) :
    ‖g chosen‖ ≤ ‖g comparator‖ + ‖estimate comparator - g comparator‖ +
      ‖estimate chosen - g chosen‖ := by
  have h₁ := norm_le_norm_add_norm_sub (estimate chosen) (g chosen)
  have h₂ := norm_le_norm_add_norm_sub (g comparator) (estimate comparator)
  rw [norm_sub_rev (g comparator) (estimate comparator)] at h₂
  linarith

end LongTails.Proofs.GuardedGradientMoments
