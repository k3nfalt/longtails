import LongTails.Algorithms.DistributedNormalizedTraining
import LongTails.Proofs.DistributedBatchedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedNormalizedZeroDim

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTraining

lemma point_unique (p : Params) (hd : p.d = 0) (x y : Point p) : x = y := by
  ext i
  have hi := i.isLt
  omega

lemma successful (p : Params) (hd : p.d = 0) (hε : 0 ≤ p.ε) (f : Point p → ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (output : Ω → Point p) :
    spec.successful p f output P := by
  have he : output = fun _ => p.x0 := funext fun _ => point_unique p hd _ _
  have hg : gradient f p.x0 = 0 := point_unique p hd _ _
  change Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure Ω) ∧
    (∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure Ω)) ≤ p.ε
  rw [he]
  refine ⟨measurable_const, ?_, ?_⟩
  · simp only [hg, norm_zero]
    exact integrable_const 0
  · simpa only [hg, norm_zero, integral_zero] using hε

lemma finiteEvents (p : Params) (T : Time)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    (seed : Fin (zeroConfig p T).iterations)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
    FiniteEvents (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
      (LongTails.Algorithms.DistributedBatchedSgd.algorithm p.toParams (zeroConfig p T)) T (seed, samples) := by
  have ha : (LongTails.Algorithms.DistributedBatchedSgd.active p.toParams (zeroConfig p T)).Nonempty := by
    refine ⟨0, ?_⟩
    simp [LongTails.Algorithms.DistributedBatchedSgd.active, zeroConfig]
  have hf := DistributedBatchedExecution.finiteEvents (zeroConfig p T) g P ha seed samples
  have hT : T ≤ LongTails.Algorithms.DistributedBatchedSgd.timeBudget p.toParams (zeroConfig p T) := by
    change T ≤ _ + T
    exact le_add_of_nonneg_left (by positivity)
  intro deadline hd
  exact hf deadline (hd.trans hT)

end LongTails.Proofs.DistributedNormalizedZeroDim
