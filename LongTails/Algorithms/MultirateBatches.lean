import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

namespace LongTails.Algorithms.MultirateBatches

variable {ι : Type*} [Fintype ι]

noncomputable def share (a b : ι → ℝ) (i : ι) : ℝ :=
  (a i ^ 2 / (∑ j, a j ^ 2) + a i * b i / (∑ j, a j * b j)) / 2

noncomputable def duration (a b : ι → ℝ) (i : ι) : ℝ := a i ^ 2 / share a b i

noncomputable def count (h a b : ι → ℝ) (i : ι) : ℕ+ :=
  ⟨max 1 ⌈duration a b i / h i⌉₊, by omega⟩

end LongTails.Algorithms.MultirateBatches
