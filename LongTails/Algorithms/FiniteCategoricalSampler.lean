import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LongTails.Algorithms.FiniteCategoricalSampler

variable (ι : Type*) [Fintype ι]

def Weights := {w : ι → ℝ≥0∞ // ∑ i, w i = 1}

instance : MeasurableSpace (Weights ι) := inferInstanceAs (MeasurableSpace {w : ι → ℝ≥0∞ // ∑ i, w i = 1})

def law (w : Weights ι) : PMF ι := PMF.ofFintype w.val w.property

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def kernel : Kernel (Weights ι) ι where
  toFun w := (law ι w).toMeasure
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_sum
    intro i hi
    by_cases h : i ∈ s
    · simp only [Set.indicator_of_mem h, law, PMF.ofFintype_apply]
      exact (measurable_pi_apply i).comp measurable_subtype_coe
    · simp only [Set.indicator_of_notMem h]
      exact measurable_const

instance : IsMarkovKernel (kernel ι) where
  isProbabilityMeasure w := inferInstanceAs (IsProbabilityMeasure (law ι w).toMeasure)

variable [Nonempty ι] [StandardBorelSpace ι]

noncomputable def draw (w : Weights ι) (u : unitInterval) : ι :=
  Classical.choose (Kernel.exists_measurable_map_eq_unitInterval (kernel ι)) w u

end LongTails.Algorithms.FiniteCategoricalSampler
