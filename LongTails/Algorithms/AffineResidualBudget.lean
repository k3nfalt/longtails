import LongTails.Algorithms.AffineResidualOuter

namespace LongTails.Algorithms.AffineResidualBudget

open OracleTemplate.ComponentEnvelope
open AffineResidualSaddle (localSteps)
open AffineResidualProx
open AffineResidualOuter

noncomputable def referenceMultilevelCost (m : ℕ) (τ μ L r δ : ℝ) (J : ℕ) (seed : MultilevelSeed) : ℕ :=
  2 * localSteps m τ μ L r δ + if seed.1 + 1 ≤ J then
    2 * localSteps m τ μ L r (δ / 2 ^ (seed.1 + 1)) +
      2 * localSteps m τ μ L r (δ / 2 ^ seed.1) else 0

noncomputable def referenceFinalCost (m : ℕ) (τ L r floor : ℝ) (H J : ℕ) (seed : FinalSeed) : ℕ :=
  m + 2 * localSteps m τ floor L r (floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)) +
    referenceMultilevelCost m τ floor L r
      (floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))) J seed.2

noncomputable def referenceProbeCost (m : ℕ) (τ L r floor : ℝ) (b : ℕ) : ℕ :=
  m + b * (2 * localSteps m τ floor L r (floor * r ^ 2 / 32768) + m)

noncomputable def referenceOuterCost (m : ℕ) (τ L r floor : ℝ) (H b J : ℕ) (seed : OuterSeed) : ℕ :=
  (2 * H + 9) * referenceProbeCost m τ L r floor b + referenceFinalCost m τ L r floor H J seed.2

noncomputable def referenceRunCost (m : ℕ) (τ L r floor : ℝ) (H b N J : ℕ) (seeds : ℕ → OuterSeed) : ℕ :=
  ∑ k ∈ Finset.range N, referenceOuterCost m τ L r floor H b J (seeds k)

noncomputable def budgetedOuterPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (X : Set E) (initial : E) (τ L r D ε floor cap : ℝ)
    (H b N J K : ℕ) (seeds : ℕ → OuterSeed) : Program (Fin m × E) (ℝ × E) E :=
  if referenceRunCost m τ L r floor H b N J seeds ≤ K then
    outerOutputPlan m X initial τ L r D ε floor cap H b N seeds else .done initial

end LongTails.Algorithms.AffineResidualBudget
