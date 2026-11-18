import LongTails.Algorithms.DistributedQuantization
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace LongTails.Algorithms.DistributedRandomRounding

noncomputable def lower (spacing x : ℝ) : ℝ := spacing * ⌊x / spacing⌋

noncomputable def upper (spacing x : ℝ) : ℝ := lower spacing x + spacing

noncomputable def threshold (spacing x : ℝ) : ℝ := Int.fract (x / spacing)

noncomputable def scalar (spacing x u : ℝ) : ℝ :=
  if u < threshold spacing x then upper spacing x else lower spacing x

noncomputable def gridIndex (width : ℕ) (spacing x u : ℝ) : Fin (2 ^ width) :=
  let t := x / spacing + ((2 ^ width - 1 : ℕ) : ℝ) / 2
  ⟨min (⌊t⌋₊ + if u < Int.fract t then 1 else 0) (2 ^ width - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

noncomputable def grid (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) :
    DistributedQuantization.Grid d width :=
  fun i => gridIndex width spacing (x i) (u i)

noncomputable def message (d width : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) : List Bool :=
  DistributedQuantization.encode (grid d width spacing x u)

noncomputable def uniform : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Ico 0 1), by constructor; simp⟩

end LongTails.Algorithms.DistributedRandomRounding
