import LongTails.Algorithms.AffineSoftmaxBudget

namespace LongTails.Algorithms.AffineSoftmaxAmplification

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

noncomputable def maximumValue {ι : Type*} (v : ι → ℝ) : ℝ := sSup (Set.range v)

noncomputable def maximumScorePlan {E : Type*}
    (m : ℕ) (x : E) : Program (Fin m × E) (ℝ × E) ℝ :=
  (LongTails.Algorithms.AffineSoftmaxQueries.cachePlan m x).map fun s => maximumValue s.value

noncomputable def scoredPlan {E : Type*}
    (m : ℕ) (trial : Program (Fin m × E) (ℝ × E) E) : Program (Fin m × E) (ℝ × E) (E × ℝ) :=
  trial.bind fun x => (maximumScorePlan m x).map fun score => (x, score)

noncomputable def repeatedPlan {E : Type*}
    (m : ℕ) (trial : ℕ → Program (Fin m × E) (ℝ × E) E) (n : ℕ) :
    Program (Fin m × E) (ℝ × E) E :=
  (scoredPlan m (trial 0)).bind fun initial =>
    (selectTrialsPlan (fun j => scoredPlan m (trial (j + 1))) initial n).map Prod.fst

noncomputable def amplifiedOuterPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L G r D ε floor cap : ℝ)
    (H b N J K : ℕ) (seeds : ℕ → ℕ → LongTails.Algorithms.AffineSoftmaxOuter.OuterSeed) :
    Program (Fin m × E) (ℝ × E) E :=
  repeatedPlan m (fun j => LongTails.Algorithms.AffineSoftmaxBudget.budgetedOuterPlan
    m X initial τ L G r D ε floor cap H b N J K (seeds j)) 5

end LongTails.Algorithms.AffineSoftmaxAmplification
