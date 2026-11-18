import LongTails.Algorithms.DashaFloat
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.DashaCyclic

def selected {d : ℕ+} (k shift coordinate : Fin d) : Prop := (coordinate - shift).val < k.val + 1

instance {d : ℕ+} (k shift coordinate : Fin d) : Decidable (selected k shift coordinate) :=
  inferInstanceAs (Decidable ((coordinate - shift).val < k.val + 1))

def coordinate {d : ℕ+} (k shift : Fin d) (index : Fin (k.val + 1)) : Fin d :=
  shift + Fin.castLE (Nat.succ_le_of_lt k.isLt) index

noncomputable def multiplier {d : ℕ+} (k : Fin d) : ℝ := (d : ℝ) / (k.val + 1)

noncomputable def compressedIndex {d : ℕ+} (k shift : Fin d) (precision : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) (j : Fin d) : ℤ :=
  if selected k shift j then DashaFloat.scalarIndex precision (multiplier k * x j / spacing) (u j) else 0

abbrev Seed (d : ℕ+) := Fin d × (Fin d → ℝ)

noncomputable def law (d : ℕ+) : MeasureTheory.ProbabilityMeasure (Seed d) :=
  ⟨(PMF.uniformOfFintype (Fin d)).toMeasure.prod
    (MeasureTheory.Measure.pi (fun _ : Fin d =>
      (DashaQuantization.unitLaw : MeasureTheory.Measure ℝ))), inferInstance⟩

noncomputable def compress {d : ℕ+} (k : Fin d) (precision : ℕ) (spacing : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (seed : Seed d) : EuclideanSpace ℝ (Fin d) :=
  DashaQuantization.reconstruct spacing (compressedIndex k seed.1 precision spacing x seed.2)

end LongTails.Algorithms.DashaCyclic
