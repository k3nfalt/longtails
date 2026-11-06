import LongTails.Algorithms.AffineSoftmaxOuter
import LongTails.Proofs.ComponentEnvelopeExecution

namespace LongTails.Algorithms.AffineSoftmaxBudget

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxSearch
open LongTails.Algorithms.AffineSoftmaxOuter

noncomputable def referenceFinalCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H J : ℕ) (seed : FinalSeed) : ℕ :=
  let s : Snapshot (Fin m) E := ⟨initial, (fun _ => 0), (fun _ => 0)⟩
  let reply := fun _ : Fin m × E => ((0 : ℝ), (0 : E))
  let project := fun _ : E => initial
  m + Program.cost reply (cachedProxPlan s τ L G r floor (floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)) project seed.1) +
    Program.cost reply (multilevelPlan s τ L G r floor
      (floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) project J seed.2)

noncomputable def referenceOuterCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H b J : ℕ) (seed : OuterSeed) : ℕ :=
  (∑ i ∈ Finset.range (2 * H + 9), Program.cost (fun _ : Fin m × E => ((0 : ℝ), (0 : E)))
    (probePlan m initial τ L G r floor (fun _ => initial) (seed.1 i) b)) +
    referenceFinalCost m initial τ L G r floor H J seed.2

noncomputable def referenceRunCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H b N J : ℕ) (seeds : ℕ → OuterSeed) : ℕ :=
  ∑ k ∈ Finset.range N, referenceOuterCost m initial τ L G r floor H b J (seeds k)

noncomputable def budgetedOuterPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L G r D ε floor cap : ℝ)
    (H b N J K : ℕ) (seeds : ℕ → OuterSeed) : Program (Fin m × E) (ℝ × E) E :=
  if referenceRunCost m initial τ L G r floor H b N J seeds ≤ K then
    outerOutputPlan m X initial τ L G r D ε floor cap H b N seeds else .done initial

end LongTails.Algorithms.AffineSoftmaxBudget
