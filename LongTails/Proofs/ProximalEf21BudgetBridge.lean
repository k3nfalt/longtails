import LongTails.Setups.StochasticProximalEf21
import LongTails.Proofs.ProximalEf21CountedBudget

noncomputable section

namespace LongTails.Proofs.ProximalEf21BudgetBridge

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21CountedBudget

noncomputable def budget : (let S := LongTails.Setups.StochasticProximalEf21.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 3 then 0 else if i = 0 then ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2 + (1 / p.δ + p.σ ^ 2 / (p.L ^ 2 * p.R ^ 2)) * Real.log (2 + p.H / (p.L * p.R ^ 2)))⌉₊ else ⌈1152921504606846976 * (p.L * p.R ^ 2 / (p.δ * p.ε) + Real.log (2 + p.H / (p.L * p.R ^ 2)) / p.δ)⌉₊

lemma executionStep_eq (p : Params) : executionStep p = gamma p.L p.δ := rfl
lemma regularization_eq (p : Params) (s : ℕ) : regularization p s = mu p.L s := rfl
lemma finalStage_eq (p : Params) : finalStage p = lastStage p.L p.R p.ε := rfl
lemma batchSize_eq (p : Params) (s : ℕ) : batchSize p s = batches p.L p.R p.σ p.δ s := rfl
lemma stageLength_eq (p : Params) (s : ℕ) : stageLength p s = ProximalEf21CountedBudget.length p.L p.R p.δ p.H s := rfl
lemma iterationCount_eq (p : Params) : iterationCount p = rounds p.L p.R p.δ p.H p.ε := rfl
lemma samplesPerWorker_eq (p : Params) : samplesPerWorker p = samples p.L p.R p.σ p.δ p.H p.ε := rfl

lemma oracle_budget_sufficient (p : Params)
    (hp : LongTails.Setups.StochasticProximalEf21.spec.valid p) :
    samplesPerWorker p ≤ budget p 0 ∧
    iterationCount p ≤ budget p 1 ∧
    iterationCount p ≤ budget p 2 ∧
    budget p 3 = 0 := by
  rcases hp with ⟨hn, hL, hR, hσ, hδ, hδ1, hε, hεL, hH⟩
  have hs := counted_sample_budget (σ := p.σ) hL hR hδ hδ1 hH hε hεL
  have ht := counted_round_budget hL hR hδ hδ1 hH hε hεL
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [samplesPerWorker_eq, budget, sampleBudget] using hs
  · simpa [iterationCount_eq, budget, roundBudget] using ht
  · simpa [iterationCount_eq, budget, roundBudget] using ht
  · simp [budget]

lemma all_worker_costs (p : Params)
    (hp : LongTails.Setups.StochasticProximalEf21.spec.valid p) :
    allWorkerSamples p ≤ p.workers * budget p 0 ∧
    allWorkerMessages p ≤ p.workers * budget p 1 := by
  obtain ⟨hs, ht, _, _⟩ := oracle_budget_sufficient p hp
  exact ⟨Nat.mul_le_mul_left p.workers hs, Nat.mul_le_mul_left p.workers ht⟩

end LongTails.Proofs.ProximalEf21BudgetBridge
