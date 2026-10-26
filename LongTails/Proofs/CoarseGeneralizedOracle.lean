import LongTails.Proofs.CoarseGeneralizedMeasurability
import LongTails.Proofs.CoarseGeneralizedTuning
import LongTails.Proofs.RobustSampleBlocks

open MeasureTheory

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
open RobustGradient

@[fun_prop] lemma measurable_warmEstimate (p : Params) : Measurable (warmEstimate p) := by
  unfold warmEstimate
  have hm : Measurable (fun v : ℕ → p.E => fun i : Fin (warmGroups p) =>
      RobustGeneralized.meanBlock (i * 576) 576 v) :=
    Measurable.of_eval (fun i => RobustGeneralized.measurable_meanBlock (i * 576) 576)
  exact (measurable_pilotCenter (warmGroups p)).comp (measurable_const.prodMk hm)

noncomputable def warmSplit (p : Params) (ξ : Fin (warmBatch p) → p.Ω) :
    Fin (warmGroups p) → Fin 576 → p.Ω := fun i j => ξ ⟨i * 576 + j, by
  have hi := Nat.mul_le_mul_right 576 (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  have hj := j.isLt
  unfold warmBatch
  omega⟩

lemma warmSplit_preserving (p : Params) (μ : Measure p.Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (warmSplit p) (Measure.pi fun _ : Fin (warmBatch p) => μ)
      (Measure.pi fun _ : Fin (warmGroups p) => Measure.pi fun _ : Fin 576 => μ) :=
  finite_groups_preserving μ (warmGroups p) 576

set_option maxRecDepth 4000 in
lemma warmEstimate_samples (p : Params) (oracle : p.E → p.Ω → p.E) (x : p.E)
    (ξ : Fin (warmBatch p) → p.Ω) :
    warmEstimate p (RobustGeneralized.sampleReplies oracle x ξ) =
      pilotCenter (2 * coarseTolerance p) (fun i => (1 / (576 : ℝ)) •
        ∑ j, oracle x (warmSplit p ξ i j)) := by
  unfold warmEstimate RobustGeneralized.meanBlock
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hi := Nat.mul_le_mul_right 576 (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  have hj := j.isLt
  have hb : (i : ℕ) * 576 + (j : ℕ) < warmBatch p := by unfold warmBatch; omega
  simp only [RobustGeneralized.sampleReplies, hb, ↓reduceDIte, warmSplit]

lemma warmEstimate_failure (p : Params) (hp : spec.valid p) (μ : Measure p.Ω)
    [IsProbabilityMeasure μ] {f : p.E → ℝ} {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (x : p.E) :
    (Measure.pi fun _ : Fin (warmBatch p) => μ)
      {ξ | coarseTolerance p < ‖warmEstimate p (RobustGeneralized.sampleReplies oracle x ξ) - gradient f x‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ warmGroups p) := by
  let C : (Fin (warmGroups p) → Fin 576 → p.Ω) → p.E :=
    fun ξ => pilotCenter (2 * coarseTolerance p) (fun i => (1 / (576 : ℝ)) • ∑ j, oracle x (ξ i j))
  have hox : Measurable (oracle x) := hg.measurable.comp measurable_prodMk_left
  have hC : Measurable C := (measurable_pilotCenter (warmGroups p)).comp
    (measurable_const.prodMk (by fun_prop))
  have hB : 0 < 2 * coarseTolerance p := by have hh := coarseTolerance_pos p hp; positivity
  have hh := pilot_means_failure_probability hox (hg.integrable x) (gradient f x)
    (hg.unbiased x) (hg.variance_integrable x) (hg.variance x) hB
    (warmGroups p) 576 (by norm_num) (warm_mean_variance p hp)
  have hset : MeasurableSet {w | 2 * coarseTolerance p / 2 < ‖C w - gradient f x‖} :=
    measurableSet_lt measurable_const (hC.sub measurable_const).norm
  have hm := (warmSplit_preserving p μ).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (warmGroups p) => Measure.pi fun _ : Fin 576 => μ)
    {w | 2 * coarseTolerance p / 2 < ‖C w - gradient f x‖} ≤ _ at hh
  rw [← hm] at hh
  simpa only [Set.preimage_ofPred_eq, Function.comp_apply, warmEstimate_samples, C,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh

end OracleTemplate.CoarseGeneralized
