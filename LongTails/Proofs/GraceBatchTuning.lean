import LongTails.Algorithms.GraceBatch
import LongTails.Proofs.GraceBatchAllocation
import LongTails.Proofs.DistributedBatchedSgd

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.GraceBatchTuning

open LongTails.Algorithms.GraceBatch
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

lemma batches_spec {p : Params} {S : Finset (Fin p.n)} (hS : S.Nonempty)
    (hh : ∀ i, 0 < p.h i) :
    (∀ i, batches p S i ≤ ⌊(LongTails.Algorithms.GraceBatch.batchTime p S : ℝ) / (p.h i : ℝ)⌋₊) ∧
    (∀ i ∉ S, batches p S i = 0) ∧ ∑ i ∈ S, batches p S i = B p := by
  classical
  have hc := GraceBatchAllocation.batch_capacity S hS (fun i => (p.h i : ℝ))
    (fun i _ => by exact_mod_cast hh i) (B p)
  have he := GraceBatchAllocation.trim_batch S _ (B p) hc
  have htime : (LongTails.Algorithms.GraceBatch.batchTime p S : ℝ) =
      (B p + (S.card : ℝ)) / ∑ i ∈ S, (p.h i : ℝ)⁻¹ := by
    simp [LongTails.Algorithms.GraceBatch.batchTime]
  simp only [batches, htime, dite_eq_left he]
  exact he.choose_spec

lemma total_and_worker_time {p : Params} {S : Finset (Fin p.n)} (hS : S.Nonempty)
    (hh : ∀ i, 0 < p.h i) :
    totalBatch (statistical p) (tuning p S) = B p ∧
      ∀ i, (batches p S i : DistributedTemplate.Time) * p.h i ≤ LongTails.Algorithms.GraceBatch.batchTime p S := by
  classical
  obtain ⟨hle, hout, hsum⟩ := batches_spec hS hh
  constructor
  · change ∑ i, batches p S i = B p
    rw [← hsum]
    exact Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S)
      (fun i hi => hout i (Finset.mem_sdiff.mp hi).2) (fun _ _ => rfl) |>.symm
  · intro i
    have hhi : 0 < (p.h i : ℝ) := by exact_mod_cast hh i
    have hn : 0 ≤ (LongTails.Algorithms.GraceBatch.batchTime p S : ℝ) / (p.h i : ℝ) := by positivity
    have hc := (Nat.cast_le.mpr (hle i) : (batches p S i : ℝ) ≤ _).trans (Nat.floor_le hn)
    exact_mod_cast (le_div_iff₀ hhi).mp hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma quantized_output_accuracy {p : Params} {S : Finset (Fin p.n)}
    (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (P : ProbabilityMeasure (Samples p)) (μ : ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (s : Samples p) => s i k) (μ : Measure _) (P : Measure _))
    (g : Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ : Measure _) f g p.σ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x₀ - lower ≤ p.Δ) :
    let cfg := tuning p S
    let out := output (statistical p) cfg (fun _ => g)
    let Q := (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod (P : Measure _)
    Measurable out ∧ Integrable (fun s => ‖gradient f (out s)‖ ^ 2) Q ∧
      (∫ s, ‖gradient f (out s)‖ ^ 2 ∂Q) ≤ p.ε := by
  have he := (total_and_worker_time (p := p) hS hh).1
  have hl : targetBatch (statistical p) ≤ totalBatch (statistical p) (tuning p S) := he.ge
  have hL' : 0 < (statistical p).L := mul_pos two_pos hL
  have hlip' (x y : Point p) : ‖gradient f x - gradient f y‖ ≤ (statistical p).L * ‖x - y‖ :=
    (hlip x y).trans (mul_le_mul_of_nonneg_right (by change p.L ≤ 2 * p.L; linarith) (norm_nonneg _))
  let model := statistical p
  let cfg := tuning p S
  have hK : cfg.iterations = iterations model := rfl
  have hw : cfg.width = (config model).width := rfl
  have accuracy := DistributedBatchedSgd.output_accuracy_of_batch (p := model) cfg (P : Measure _)
  have forOracle := accuracy (fun _ => μ) hworkers hIID (fun _ => g) f (fun _ => hsg)
  exact forOracle hK hw hl hL' hΔ hε hg hlip' lower hlower hgap

end LongTails.Proofs.GraceBatchTuning
