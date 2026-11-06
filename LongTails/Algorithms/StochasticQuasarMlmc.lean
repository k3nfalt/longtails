import LongTails.Algorithms.StochasticQuasarInner
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped BigOperators ENNReal

namespace OracleTemplate.StochasticQuasar

noncomputable def mlmcWeight (m : ℕ) (j : Fin (m + 1)) : ℝ :=
  (1 / 4 : ℝ) ^ j.val / ∑ i : Fin (m + 1), (1 / 4 : ℝ) ^ i.val

noncomputable def mlmcLevelPMF (m : ℕ) : PMF (Fin (m + 1)) :=
  PMF.normalize (fun j => ENNReal.ofReal ((1 / 4 : ℝ) ^ j.val))
    (by
      rw [tsum_fintype]
      have h : (1 : ℝ≥0∞) ≤ ∑ j : Fin (m + 1), ENNReal.ofReal ((1 / 4 : ℝ) ^ j.val) := by
        calc
          1 = ENNReal.ofReal ((1 / 4 : ℝ) ^ (0 : Fin (m + 1)).val) := by simp
          _ ≤ _ := Finset.single_le_sum
            (f := fun j : Fin (m + 1) => ENNReal.ofReal ((1 / 4 : ℝ) ^ j.val))
            (fun _ _ => by positivity) (Finset.mem_univ (0 : Fin (m + 1)))
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h))
    (by simp [tsum_fintype])

noncomputable def mlmcLevelLaw (m : ℕ) : ProbabilityMeasure (Fin (m + 1)) :=
  ⟨(mlmcLevelPMF m).toMeasure, inferInstance⟩

noncomputable def mlmcRadius (r : ℝ) (j : ℕ) : ℝ := r / (2 : ℝ) ^ j

noncomputable def mlmcCalls (L σ D r : ℝ) (j : ℕ) : ℕ :=
  (innerCalls L σ D (innerStageCount D (mlmcRadius r j)) +
    innerCalls L σ D (innerStageCount D (mlmcRadius r (j + 1)))) +
      innerCalls L σ D (innerStageCount D r)

noncomputable def estimatorDepth (v β : ℝ) : ℕ := Nat.clog 2 ⌈1 + v / β⌉₊

noncomputable def estimatorRadius (L v β : ℝ) : ℝ :=
  v / (2 * L * Real.sqrt (10 * (estimatorDepth v β + 1 : ℝ)))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def mlmcPlan (L σ D r : ℝ) (c x0 : E) (m : ℕ) (j : Fin (m + 1)) :
    QueryPlan (Fin 2 × E) E E (mlmcCalls L σ D r j.val) :=
  (approximationPlan L σ D r c x0).bind fun base =>
    (approximationPlan L σ D (mlmcRadius r (j.val + 1)) c x0).bind fun upper =>
      (approximationPlan L σ D (mlmcRadius r j.val) c x0).map fun lower =>
        base + (mlmcWeight m j)⁻¹ • (upper - lower)

noncomputable def envelopeEstimatePlan (L σ D r : ℝ) (c x0 : E) (m : ℕ) (j : Fin (m + 1)) :
    QueryPlan (Fin 2 × E) E E (mlmcCalls L σ D r j.val) :=
  (mlmcPlan L σ D r c x0 m j).map fun y => (2 * L) • (c - y)

noncomputable def tunedEnvelopePlan (L σ D v β : ℝ) (c x0 : E)
    (j : Fin (estimatorDepth v β + 1)) :
    QueryPlan (Fin 2 × E) E E (mlmcCalls L σ D (estimatorRadius L v β) j.val) :=
  envelopeEstimatePlan L σ D (estimatorRadius L v β) c x0 (estimatorDepth v β) j

end OracleTemplate.StochasticQuasar
