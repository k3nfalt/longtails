import LongTails.Proofs.AffineAdamProbability
import LongTails.Proofs.AffineAdamParameters
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory

namespace LongTails.Proofs.AffineAdamRate

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam LongTails.Algorithms.BatchedAdam
open AffineAdamProbability AffineAdamParameters AffineAdamGeometry BatchedAdamExecution

lemma block_gradient_sum (q : Params) (hq : spec.valid q)
    (P : Measure q.Ω) [IsProbabilityMeasure P]
    {g : Point q.d → q.Ω → Point q.d} {f : Point q.d → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, q.L1 * maxNorm (y - x) ≤ 1 →
      sumNorm (gradient f y - gradient f x) ≤
        (q.L0 + q.L1 * sumNorm (gradient f x)) * maxNorm (y - x))
    (hgap : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hi : ∀ x, Integrable (g x) P) (hm : ∀ x, ∫ ω, g x ω ∂P = gradient f x)
    (hpi : ∀ x i, Integrable (fun ω => |(g x ω - gradient f x) i| ^ q.p) P)
    (hmom : ∀ x i, (∫ ω, |(g x ω - gradient f x) i| ^ q.p ∂P) ≤
      q.σ0 i ^ q.p + q.σ1 ^ q.p * |gradient f x i| ^ q.p) :
    (∑ t ∈ Finset.range ((config q).lastIndex + 1),
      ∫ ξ, sumNorm (gradient f (process (config q) q.x0 0 g ξ t).point)
        ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (config q).batchSize => P)) ≤
      (((config q).lastIndex + 1 : ℕ) : ℝ) * q.ε := by
  let cfg := config q
  let Q := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => P
  let G := fun t ξ => sumNorm (gradient f (process cfg q.x0 0 g ξ t).point)
  let N := fun t ξ => sumNorm (batchReply cfg g (process cfg q.x0 0 g ξ t).point (ξ t) -
    gradient f (process cfg q.x0 0 g ξ t).point)
  let c := 4 * (cfg.batchSize : ℝ) ^ ((1 - q.p) / q.p)
  let a := c * ∑ i, q.σ0 i
  let b := c * q.σ1
  have hη := (tuning_pos q hq).1
  have hδ := (tuning_pos q hq).2.1
  have hB := (tuning_pos q hq).2.2
  have hGi (t) : Integrable (G t) Q :=
    integrable_process_gradient Q cfg rfl rfl hη.le hδ q.x0 0 hg hq.1 hq.2.1 hlip
      (local_step q hq) id measurable_id t
  have hnoise (x : Point q.d) :
      Integrable (fun ζ => sumNorm (batchReply cfg g x ζ - gradient f x))
        (Measure.pi fun _ : Fin cfg.batchSize => P) ∧
      (∫ ζ, sumNorm (batchReply cfg g x ζ - gradient f x)
        ∂Measure.pi (fun _ : Fin cfg.batchSize => P)) ≤ a + b * sumNorm (gradient f x) := by
    have h := batch_error_bound cfg hB P q.σ0 hq.2.2.2.2.2.1 hq.2.2.2.2.2.2.1
      hq.2.2.2.1 hq.2.2.2.2.1 hg hi hm hpi hmom x
    refine ⟨h.1, h.2.trans_eq ?_⟩
    dsimp [a, b, c]
    ring
  have hN (t) : Integrable (N t) Q ∧ (∫ ξ, N t ξ ∂Q) ≤ a + b * ∫ ξ, G t ξ ∂Q :=
    process_error_bound cfg P hg f q.x0 0 t hnoise (hGi t)
  have hp := AffineAdamDescent.integrated_bound Q G N (cfg.lastIndex + 1) q.d hGi
    (fun t => (hN t).1) (fun t => (hN t).2) (η := cfg.η) (Δ := q.Δ) (δ := cfg.δ)
    (L0 := q.L0) (L1 := q.L1) (fun ξ => by
      let z := fun t => batchReply cfg g (process cfg q.x0 0 g ξ t).point (ξ t)
      have ht (t) : trajectory cfg q.x0 0 z t = process cfg q.x0 0 g ξ t :=
        (process_eq_trajectory cfg q.x0 0 g ξ t).symm
      have h := AffineAdamPath.deterministic_bound cfg rfl rfl hη.le hδ q.x0 0 z
        hq.1 hq.2.1 hgrad hlip (local_step q hq) hη hgap (cfg.lastIndex + 1)
      dsimp only at h
      simp only [ht, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul] at h
      exact h)
  apply accuracy_from_bound q hq
    (Finset.sum_nonneg (fun t _ => integral_nonneg (fun ξ => sumNorm_nonneg _)))
  exact hp

set_option maxHeartbeats 200000 in
lemma output_accuracy (q : Params) (hq : spec.valid q)
    (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure q.Ω) (P : Measure (ℕ → q.Ω)))
    {g : Point q.d → q.Ω → Point q.d} {f : Point q.d → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, q.L1 * maxNorm (y - x) ≤ 1 →
      sumNorm (gradient f y - gradient f x) ≤
        (q.L0 + q.L1 * sumNorm (gradient f x)) * maxNorm (y - x))
    (hgap : ∀ x, f q.x0 - f x ≤ q.Δ)
    (hi : ∀ x, Integrable (g x) p) (hm : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hpi : ∀ x i, Integrable (fun ω => |(g x ω - gradient f x) i| ^ q.p) p)
    (hmom : ∀ x i, (∫ ω, |(g x ω - gradient f x) i| ^ q.p ∂p) ≤
      q.σ0 i ^ q.p + q.σ1 ^ q.p * |gradient f x i| ^ q.p) :
    let O : Oracle (Point q.d) (Point q.d) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ z ω => g z.2 ω }
    let out := fun z : Fin ((config q).lastIndex + 1) × (ℕ → q.Ω) => output q O z.1 z.2
    let Q := (PMF.uniformOfFintype (Fin ((config q).lastIndex + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))
    Measurable out ∧ Integrable (fun z => sumNorm (gradient f (out z))) Q ∧
      (∫ z, sumNorm (gradient f (out z)) ∂Q) ≤ q.ε := by
  let cfg := config q
  let R := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.batchSize => (p : Measure q.Ω)
  let μ := (PMF.uniformOfFintype (Fin (cfg.lastIndex + 1))).toMeasure
  let selected := fun z : Fin (cfg.lastIndex + 1) × (ℕ → Fin cfg.batchSize → q.Ω) =>
    (process cfg q.x0 0 g z.2 z.1.val).point
  have hη := (tuning_pos q hq).1
  have hδ := (tuning_pos q hq).2.1
  have hB := (tuning_pos q hq).2.2
  have hsm : Measurable selected := measurable_from_prod_countable_right
    (fun i => (measurable_process cfg hg q.x0 0 i.val).1)
  have hGi (t) : Integrable (fun ξ => sumNorm (gradient f (process cfg q.x0 0 g ξ t).point)) R :=
    integrable_process_gradient R cfg rfl rfl hη.le hδ q.x0 0 hg hq.1 hq.2.1 hlip
      (local_step q hq) id measurable_id t
  have hfm := (measurable_sumNorm.comp (measurable_gradient f)).comp hsm
  have hsi : Integrable (fun z => sumNorm (gradient f (selected z))) (μ.prod R) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun i => hGi i.val), Integrable.of_finite⟩
  have hacc : (∫ z, sumNorm (gradient f (selected z)) ∂μ.prod R) ≤ q.ε := by
    rw [integral_prod _ hsi]
    change (∫ i : Fin (cfg.lastIndex + 1), ∫ ξ, sumNorm (gradient f (process cfg q.x0 0 g ξ i.val).point)
      ∂R ∂μ) ≤ q.ε
    rw [MixedNoise.integral_uniform_finite, Fintype.card_fin]
    rw [show (∑ i : Fin (cfg.lastIndex + 1), ∫ ξ, sumNorm (gradient f
      (process cfg q.x0 0 g ξ i.val).point) ∂R) =
      ∑ t ∈ Finset.range (cfg.lastIndex + 1), ∫ ξ, sumNorm (gradient f
      (process cfg q.x0 0 g ξ t).point) ∂R from
        Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, sumNorm (gradient f
          (process cfg q.x0 0 g ξ t).point) ∂R) (cfg.lastIndex + 1)]
    have h := block_gradient_sum q hq (p : Measure q.Ω) hg hgrad hlip hgap hi hm hpi hmom
    have hT : (0 : ℝ) < (cfg.lastIndex + 1 : ℕ) := by positivity
    rw [← div_eq_inv_mul, div_le_iff₀ hT]
    simpa only [mul_comm q.ε] using h
  have hb := FiniteVariance.infinite_block_law (p : Measure q.Ω) (P : Measure (ℕ → q.Ω))
    h_samples.independent h_samples.marginal cfg.batchSize
  have hmap := (MeasurePreserving.id μ).prod hb
  let O : Oracle (Point q.d) (Point q.d) :=
    { Seed := fun _ => q.Ω, law := P, answer := fun _ z ω => g z.2 ω }
  have hout (k : Fin (cfg.lastIndex + 1)) (ξ : ℕ → q.Ω) :
      output q O k ξ = selected (k, fun t i => ξ (t * cfg.batchSize + i.val)) := by
    unfold output
    rw [Nat.mul_comm cfg.batchSize (cfg.lastIndex + 1), execute_process cfg hB,
      process_saved, ite_eq_left k.isLt]
  dsimp only
  dsimp only [O] at hout
  simp_rw [hout]
  refine ⟨hsm.comp hmap.measurable, hmap.integrable_comp_of_integrable hsi, ?_⟩
  have he := integral_map (μ := μ.prod (P : Measure (ℕ → q.Ω))) hmap.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hmap.map_eq] at he
  exact he.symm.trans_le hacc

end LongTails.Proofs.AffineAdamRate
