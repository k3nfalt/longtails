import LongTails.Algorithms.ClippedTwoPoint
import LongTails.Algorithms.AcceleratedTwoPointZerothOrderConvex
import LongTails.Setups.AdaptivePairedZerothOrder
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory

namespace LongTails.Algorithms.AdaptivePairedZerothOrder

open LongTails.Setups.AdaptivePairedZerothOrder
open LongTails.Algorithms.ClippedTwoPoint

abbrev Direction (p : Public) := Metric.sphere (0 : Point p.d) 1

noncomputable def directionLaw (p : Public) : ProbabilityMeasure (ℕ → Direction p) := by
  letI : NeZero p.d := ⟨p.dimension_pos.ne'⟩
  exact ⟨Measure.infinitePi (fun _ : ℕ =>
    (OracleTemplate.ZerothOrder.sphereLaw (Point p.d) : Measure (Direction p))), inferInstance⟩

noncomputable def weightTotal (p : Public) : ℝ := (p.N : ℝ) * (p.N + 1) / 2

noncomputable def scale (p : Public) : ℝ :=
  p.ε * Real.sqrt p.T / (16777216 * p.D * Real.sqrt (p.d + p.ell))

noncomputable def clipRadius (p : Public) : ℝ := scale p * Real.sqrt (p.T / ((p.d : ℝ) * p.ell))

noncomputable def regularization (p : Public) : ℝ := p.ε * weightTotal p / (64 * p.D ^ 2)

noncomputable def validationClip (p : Public) : ℝ := scale p * p.D * Real.sqrt (p.T / p.ell)

noncomputable def batch (p : Public) (t : ℕ) : ℕ := batchSize p.T (weightTotal p) (t + 1)

noncomputable def firstDirections (p : Public) (seed : ℕ → Direction p)
    (t : ℕ) (i : Fin (batch p t)) : Point p.d :=
  seed (2 * (∑ j ∈ Finset.range t, batch p j) + i)

noncomputable def secondDirections (p : Public) (seed : ℕ → Direction p)
    (t : ℕ) (i : Fin (batch p t)) : Point p.d :=
  seed (2 * (∑ j ∈ Finset.range t, batch p j) + batch p t + i)

noncomputable def output {Ω : Type*} (p : Public) (seed : ℕ → Direction p)
    (g : Point p.d → Ω → ℝ) (ξ : ℕ → Ω) : Point p.d :=
  adaptiveOutput p.d (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
    (firstDirections p seed) (secondDirections p seed) g ξ 0 p.N p.T

noncomputable def algorithm (p : Public) : OracleTemplate.Algorithm (Point p.d) ℝ (Point p.d) :=
  adaptiveAlgorithm (directionLaw p) p.d (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) (validationClip p)
    p.project (p.x0, p.x0) (batch p) (firstDirections p) (secondDirections p) p.N p.T

end LongTails.Algorithms.AdaptivePairedZerothOrder
