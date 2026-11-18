import LongTails.Proofs.DashaCompression
import LongTails.Proofs.DashaScalingParameters
import LongTails.Proofs.DashaTracking

namespace LongTails.Proofs.DashaScalingMoments

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

lemma local_tracking (c : Choice p) (hε : 0 < p.ε) (g h hnext : Fin p.n → Point p)
    (i : Fin p.n) :
    let u := fun j => hnext j - h j - momentum p c • (g j - h j)
    let C := fun j (seed : Sample p) =>
      LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c) (u j) (seed j)
    Integrable (fun seed => ‖g i + C i seed - hnext i‖ ^ 2) (sampleLaw p : Measure _) ∧
      (∫ seed, ‖g i + C i seed - hnext i‖ ^ 2 ∂(sampleLaw p : Measure _)) ≤
        (1 - momentum p c) * ‖g i - h i‖ ^ 2 +
          2 * variance p c * ‖hnext i - h i‖ ^ 2 +
          2 * (c.block.val + 1) * spacing p c ^ 2 := by
  simp only [sampleLaw, ProbabilityMeasure.coe_mk]
  let u := fun j => hnext j - h j - momentum p c • (g j - h j)
  let C := fun j (seed : Sample p) =>
    LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c) (u j) (seed j)
  have hm := DashaCompression.replicated_error_moments c.block c.precision (spacing p c) u
    (DashaScalingParameters.spacing_pos c hε).ne' i
  have hI := AdaptiveReplicaMoments.shifted_second_moment_integrable
    ((1 - momentum p c) • (g i - h i)) hm.1 hm.2.2.1
  have hB := DashaTracking.tracking_second_moment_le (g i) (h i) (hnext i)
    (momentum p c) (variance p c) (2 * (c.block.val + 1) * spacing p c ^ 2)
    (DashaScalingParameters.variance_nonneg c) (C i) hm.1 hm.2.2.1 hm.2.1 hm.2.2.2
  have ha : 2 * momentum p c ^ 2 * variance p c + (1 - momentum p c) ^ 2 =
      1 - momentum p c :=
    DashaTracking.momentum_contraction (variance p c) (DashaScalingParameters.variance_nonneg c)
  refine ⟨?_, ?_⟩
  · dsimp only [u] at hI
    simpa only [← DashaTracking.tracking_identity] using hI
  · rw [ha] at hB
    dsimp only [C, u] at hB
    linarith only [hB]

lemma aggregate_tracking (c : Choice p) (hε : 0 < p.ε) (g h hnext : Fin p.n → Point p) :
    let u := fun j => hnext j - h j - momentum p c • (g j - h j)
    let C := fun j (seed : Sample p) =>
      LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c) (u j) (seed j)
    (∫ seed, ‖(1 / (p.n : ℝ)) • ∑ i, (g i + C i seed - hnext i)‖ ^ 2
      ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) ^ 2 * ‖(1 / (p.n : ℝ)) • ∑ i, (g i - h i)‖ ^ 2 +
        (1 / (p.n : ℝ)) ^ 2 * ∑ i,
          (2 * variance p c * ‖hnext i - h i‖ ^ 2 +
            2 * momentum p c ^ 2 * variance p c * ‖g i - h i‖ ^ 2 +
            2 * (c.block.val + 1) * spacing p c ^ 2) := by
  simp only [sampleLaw, ProbabilityMeasure.coe_mk]
  let u := fun j => hnext j - h j - momentum p c • (g j - h j)
  have hm := DashaCompression.replicated_error_moments c.block c.precision (spacing p c) u
    (DashaScalingParameters.spacing_pos c hε).ne'
  exact DashaTracking.aggregate_tracking_bound
    (P := Measure.pi fun _ : Fin p.n => (LongTails.Algorithms.DashaCyclic.law p.d : Measure _))
    (E := Point p) (Ω := Sample p) g h hnext (momentum p c) (variance p c)
    (2 * (c.block.val + 1) * spacing p c ^ 2) (DashaScalingParameters.variance_nonneg c)
    (fun j seed => LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c) (u j) (seed j))
    (DashaCompression.independent_compression_errors c.block c.precision (spacing p c) u)
    (fun i => (hm i).1) (fun i => (hm i).2.2.1) (fun i => (hm i).2.1) (fun i => (hm i).2.2.2)

end LongTails.Proofs.DashaScalingMoments
