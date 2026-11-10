import LongTails.Proofs.ProximalEf21StateMachine
import LongTails.Proofs.ProximalEf21BudgetBridge

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21ProtocolBudget

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21ConstructedTrajectory
open LongTails.Proofs.ProximalEf21StateMachine
open LongTails.Proofs.ProximalEf21BudgetBridge

variable {p : Params}
variable (O : Oracle (Query p) (Reply p) 4)

noncomputable def callsUsed (s : State p) (i : Fin 4) : ℕ :=
  if i = 0 then s.samples else if i = 1 then s.rounds else if i = 2 then s.proxCalls else 0

lemma sample_prefix_le {s : ℕ} (hs : s ≤ finalStage p) :
    sampleOffset p s + batchSize p s * stageLength p s ≤ samplesPerWorker p := by
  have hsum : (∑ j ∈ Finset.range (s + 1), batchSize p j * stageLength p j) ≤
      ∑ j ∈ Finset.range (finalStage p + 1), batchSize p j * stageLength p j := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ hs)
  simpa only [Finset.sum_range_succ, sampleOffset, samplesPerWorker] using hsum

lemma round_prefix_le {s : ℕ} (hs : s ≤ finalStage p) :
    roundOffset p s + stageLength p s ≤ iterationCount p := by
  have hsum : (∑ j ∈ Finset.range (s + 1), stageLength p j) ≤
      ∑ j ∈ Finset.range (finalStage p + 1), stageLength p j := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ hs)
  simpa only [Finset.sum_range_succ, roundOffset, iterationCount] using hsum

lemma proximal_call_available (hp : spec.valid p) (s t : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s) (ω : Randomness p O) :
    callsUsed (stateAt O s t ω) (methodQuery p (stateAt O s t ω)).1 <
      budget p (methodQuery p (stateAt O s t ω)).1 := by
  have hq : (methodQuery p (stateAt O s t ω)).1 = 2 := by
    simp [methodQuery, stateAt, not_lt.mpr hs]
  rw [hq]
  have hcost := round_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).2.2.1
  change roundOffset p s + t < budget p 2
  omega

lemma sample_call_available (hp : spec.valid p) (s t j : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s)
    (hj : j < batchSize p s) (ω : Randomness p O) :
    callsUsed (batchState O s t j ω) (methodQuery p (batchState O s t j ω)).1 <
      budget p (methodQuery p (batchState O s t j ω)).1 := by
  have hq : (methodQuery p (batchState O s t j ω)).1 = 0 := by
    simp [methodQuery, batchState, stateAt, hj, not_lt.mpr hs]
  rw [hq]
  have hcost := sample_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).1
  have hprod : (t + 1) * batchSize p s ≤ stageLength p s * batchSize p s :=
    Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr ht)
  simp only [Nat.add_mul, one_mul] at hprod
  simp only [callsUsed, batchState, hj, if_true, stateAt]
  have hcomm : batchSize p s * stageLength p s = stageLength p s * batchSize p s :=
    Nat.mul_comm _ _
  omega

lemma compression_call_available (hp : spec.valid p) (s t : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s) (ω : Randomness p O) :
    callsUsed (batchState O s t (batchSize p s) ω)
        (methodQuery p (batchState O s t (batchSize p s) ω)).1 <
      budget p (methodQuery p (batchState O s t (batchSize p s) ω)).1 := by
  have hq : (methodQuery p (batchState O s t (batchSize p s) ω)).1 = 1 := by
    simp [methodQuery, batchState, stateAt, not_lt.mpr hs]
  rw [hq]
  have hcost := round_prefix_le (p := p) hs
  have hbudget := (oracle_budget_sufficient p hp).2.1
  simp only [callsUsed, batchState, lt_irrefl, if_false, stateAt]
  norm_num only [show (1 : Fin 4) ≠ 0 by decide, if_false, if_true]
  omega

lemma terminal_call_unavailable (ω : Randomness p O) :
    budget p (methodQuery p (stateAt O (finalStage p + 1) 0 ω)).1 = 0 := by
  rw [terminal_channel]
  simp only [budget, if_pos rfl]

lemma trace_success_and_cost (hp : spec.valid p) {I : Instance p}
    (hg : ProblemAssumptions p I) (ho : OracleAssumptions p I O) :
    spec.successful p I (traceOutput O) ((p.initialLaw).prod O.law) ∧
    samplesPerWorker p ≤ budget p 0 ∧
    iterationCount p ≤ budget p 1 ∧
    iterationCount p ≤ budget p 2 ∧
    budget p 3 = 0 := by
  exact ⟨trace_success O hp hg ho, oracle_budget_sufficient p hp⟩

end LongTails.Proofs.ProximalEf21ProtocolBudget
