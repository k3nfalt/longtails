import LongTails.Template
import LongTails.Algorithms.ProximalEf21Homotopy
import LongTails.Proofs.ProximalEf21ProtocolBudget

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.ProximalEf21Execution

open OracleTemplate
open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21OracleTrace
open LongTails.Proofs.ProximalEf21ConstructedTrajectory
open LongTails.Proofs.ProximalEf21StateMachine
open LongTails.Proofs.ProximalEf21BudgetBridge
open LongTails.Proofs.ProximalEf21ProtocolBudget

universe uQ uR uO

def runWithBudget
    {Q : Type uQ} {R : Type uR} {Out : Type uO} {n : ℕ}
    (answer : List ((Fin n × Q) × R) → (Fin n × Q) → R)
    (A : Algorithm Q R Out n) :
    ℕ → List ((Fin n × Q) × R) → (Fin n → ℕ) → A.State →
      Out × List ((Fin n × Q) × R)
  | 0, history, _, state => (A.output state, history)
  | k + 1, history, remaining, state =>
      let query := A.query state
      if remaining query.1 = 0 then (A.output state, history)
      else
        let reply := answer history query
        let remaining := Function.update remaining query.1 (remaining query.1 - 1)
        runWithBudget answer A k (history ++ [(query, reply)]) remaining (A.update state reply)

lemma executeWithTrace_eq_runWithBudget
    {Q : Type uQ} {R : Type uR} {Out : Type uO} {n : ℕ}
    (O : Oracle Q R n) (A : Algorithm Q R Out n)
    (b : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) :
    executeWithTrace O A b seed ξ =
      runWithBudget (fun h q => O.answer h q (ξ h.length))
        A (∑ i, b i) [] b (A.initial seed) := by
  rfl

variable {p : Params}
variable (O : Oracle (Query p) (Reply p) 4)

noncomputable def replay (ω : Randomness p O) (k : ℕ) : Machine p :=
  advance O ω.2 (initialState p ω.1, []) k

lemma replay_zero (ω : Randomness p O) :
    replay O ω 0 = (initialState p ω.1, []) := rfl

lemma replay_succ (ω : Randomness p O) (k : ℕ) :
    replay O ω (k + 1) = microStep O ω.2 (replay O ω k) := rfl

lemma initial_calls_used (seed : InitialMemories p) :
    callsUsed (initialState p seed) = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [callsUsed, initialState]

lemma calls_used_update (s : State p) (a : Reply p)
    (hs : s.stage ≤ finalStage p) :
    callsUsed (methodUpdate p s a) =
      Function.update (callsUsed s) (methodQuery p s).1
        (callsUsed s (methodQuery p s).1 + 1) := by
  classical
  have hstop : ¬s.stage > finalStage p := not_lt.mpr hs
  by_cases hphase0 : s.phase = 0
  · funext i
    fin_cases i <;>
      simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0]
  · by_cases hphase1 : s.phase = 1
    · by_cases hbatch : s.batchDraws + 1 < batchSize p s.stage
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hbatch]
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hbatch]
    · by_cases hiteration : s.iteration + 1 < stageLength p s.stage
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hiteration]
      · funext i
        fin_cases i <;>
          simp [callsUsed, methodQuery, methodUpdate, hstop, hphase0, hphase1, hiteration]

lemma remaining_update (s : State p) (a : Reply p) (b : Fin 4 → ℕ)
    (hs : s.stage ≤ finalStage p) :
    Function.update (fun i => b i - callsUsed s i) (methodQuery p s).1
        ((b (methodQuery p s).1 - callsUsed s (methodQuery p s).1) - 1) =
      (fun i => b i - callsUsed (methodUpdate p s a) i) := by
  classical
  rw [calls_used_update s a hs]
  funext i
  by_cases hi : i = (methodQuery p s).1
  · subst i
    simp [Nat.sub_sub]
  · simp [Function.update, hi, Ne.symm hi]

lemma iteration_prefix_available (hp : spec.valid p) (s t j : ℕ)
    (hs : s ≤ finalStage p) (ht : t < stageLength p s)
    (hj : j < batchSize p s + 2) (ω : Randomness p O) :
    let a := advance O ω.2 (machineAt O s t ω) j
    a.1.stage ≤ finalStage p ∧
      callsUsed a.1 (methodQuery p a.1).1 < budget p (methodQuery p a.1).1 := by
  dsimp only
  by_cases hjzero : j = 0
  · subst j
    change s ≤ finalStage p ∧
      callsUsed (stateAt O s t ω) (methodQuery p (stateAt O s t ω)).1 <
        budget p (methodQuery p (stateAt O s t ω)).1
    exact ⟨hs, proximal_call_available O hp s t hs ht ω⟩
  · have hrewrite : j = 1 + (j - 1) := by omega
    have hle : j - 1 ≤ batchSize p s := by omega
    rw [hrewrite, batch_execution O s t hs ω (j - 1) hle]
    by_cases hsample : j - 1 < batchSize p s
    · refine ⟨?_, ?_⟩
      · simpa only [batchMachine, batchState, if_pos hsample, stateAt] using hs
      · exact sample_call_available O hp s t (j - 1) hs ht hsample ω
    · have hlast : j - 1 = batchSize p s := by omega
      rw [hlast]
      refine ⟨?_, compression_call_available O hp s t hs ht ω⟩
      simpa only [batchMachine, batchState, lt_irrefl, if_false, stateAt] using hs

lemma stage_prefix_available (hp : spec.valid p) (s k : ℕ)
    (hs : s ≤ finalStage p)
    (hk : k < stageLength p s * (batchSize p s + 2))
    (ω : Randomness p O) :
    let a := advance O ω.2 (machineAt O s 0 ω) k
    a.1.stage ≤ finalStage p ∧
      callsUsed a.1 (methodQuery p a.1).1 < budget p (methodQuery p a.1).1 := by
  dsimp only
  let t := k / (batchSize p s + 2)
  let j := k % (batchSize p s + 2)
  have hj : j < batchSize p s + 2 := Nat.mod_lt _ (by omega)
  have ht : t < stageLength p s := by
    have hdiv : t * (batchSize p s + 2) ≤ k := Nat.div_mul_le_self _ _
    by_contra hnot
    have hle : stageLength p s ≤ t := by omega
    have hmul := Nat.mul_le_mul_right (batchSize p s + 2) hle
    omega
  have hdecomp : k = t * (batchSize p s + 2) + j := by
    dsimp [t, j]
    have h := Nat.mod_add_div k (batchSize p s + 2)
    simpa only [Nat.mul_comm, Nat.add_comm] using h.symm
  rw [hdecomp, advance_add,
    stage_execution_prefix O hp s hs ω t (Nat.le_of_lt ht), if_pos ht]
  exact iteration_prefix_available O hp s t j hs ht hj ω

lemma whole_prefix_available (hp : spec.valid p) (ω : Randomness p O)
    (s : ℕ) (hs : s ≤ finalStage p + 1) :
    ∀ k < stageOffset p s,
      (replay O ω k).1.stage ≤ finalStage p ∧
        callsUsed (replay O ω k).1 (methodQuery p (replay O ω k).1).1 <
          budget p (methodQuery p (replay O ω k).1).1 := by
  revert hs
  induction s with
  | zero =>
      intro hs k hk
      have : stageOffset p 0 = 0 := by simp [stageOffset]
      omega
  | succ s ih =>
      intro hs k hk
      have hs0 : s ≤ finalStage p := by omega
      by_cases hprevious : k < stageOffset p s
      · exact ih (by omega) k hprevious
      · have hoffset : stageOffset p s ≤ k := by omega
        have hlocal : k - stageOffset p s < stageLength p s * (batchSize p s + 2) := by
          rw [stage_offset_succ] at hk
          omega
        have hdecomp : k = stageOffset p s + (k - stageOffset p s) := by omega
        unfold replay
        rw [hdecomp, advance_add, whole_execution_prefix O hp ω s (by omega)]
        exact stage_prefix_available O hp s (k - stageOffset p s) hs0 hlocal ω

lemma replay_terminal (hp : spec.valid p) (ω : Randomness p O) :
    replay O ω (stageOffset p (finalStage p + 1)) =
      machineAt O (finalStage p + 1) 0 ω := by
  exact whole_execution_prefix O hp ω (finalStage p + 1) le_rfl

lemma replay_terminal_budget (hp : spec.valid p) (ω : Randomness p O) :
    budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 = 0 := by
  rw [replay_terminal O hp ω]
  exact terminal_call_unavailable O ω

lemma total_fuel_sufficient (hp : spec.valid p) :
    stageOffset p (finalStage p + 1) ≤ ∑ i : Fin 4, budget p i := by
  obtain ⟨hsamples, hrounds, hprox, hstop⟩ := oracle_budget_sufficient p hp
  have hsum : (∑ i : Fin 4, budget p i) =
      budget p 0 + budget p 1 + budget p 2 + budget p 3 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  rw [call_count_identity, hsum]
  omega

lemma run_from_prefix (hp : spec.valid p) (ω : Randomness p O)
    (steps : ℕ) :
    ∀ (t fuel : ℕ), t + steps = stageOffset p (finalStage p + 1) → steps ≤ fuel →
      runWithBudget (fun h q => response O h q ω.2) (method p) fuel
        (replay O ω t).2
        (fun i => budget p i - callsUsed (replay O ω t).1 i)
        (replay O ω t).1 =
      (traceOutput O ω, (replay O ω (stageOffset p (finalStage p + 1))).2) := by
  induction steps with
  | zero =>
      intro t fuel hfinish hfuel
      have ht : t = stageOffset p (finalStage p + 1) := by omega
      subst t
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have hstop :
              (budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 -
                callsUsed (replay O ω (stageOffset p (finalStage p + 1))).1
                  (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1) = 0 := by
            rw [replay_terminal_budget O hp ω]
            exact Nat.zero_sub _
          change (if (budget p (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1 -
                callsUsed (replay O ω (stageOffset p (finalStage p + 1))).1
                  (methodQuery p (replay O ω (stageOffset p (finalStage p + 1))).1).1) = 0
              then (methodOutput (replay O ω (stageOffset p (finalStage p + 1))).1,
                (replay O ω (stageOffset p (finalStage p + 1))).2)
              else _) = _
          rw [if_pos hstop]
          rfl
  | succ steps ih =>
      intro t fuel hfinish hfuel
      cases fuel with
      | zero => omega
      | succ fuel =>
          have ht : t < stageOffset p (finalStage p + 1) := by omega
          obtain ⟨hstage, havailable⟩ :=
            whole_prefix_available O hp ω (finalStage p + 1) le_rfl t ht
          have hnonzero :
              budget p (methodQuery p (replay O ω t).1).1 -
                callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1 ≠ 0 := by
            omega
          have hremain := remaining_update (replay O ω t).1
            (response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2)
            (budget p) hstage
          change (if budget p (methodQuery p (replay O ω t).1).1 -
                callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1 = 0
              then (methodOutput (replay O ω t).1, (replay O ω t).2)
              else runWithBudget (fun h q => response O h q ω.2) (method p) fuel
                ((replay O ω t).2 ++ [(methodQuery p (replay O ω t).1,
                  response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2)])
                (Function.update (fun i => budget p i - callsUsed (replay O ω t).1 i)
                  (methodQuery p (replay O ω t).1).1
                  ((budget p (methodQuery p (replay O ω t).1).1 -
                    callsUsed (replay O ω t).1 (methodQuery p (replay O ω t).1).1) - 1))
                (methodUpdate p (replay O ω t).1
                  (response O (replay O ω t).2 (methodQuery p (replay O ω t).1) ω.2))) = _
          rw [if_neg hnonzero, hremain]
          change runWithBudget (fun h q => response O h q ω.2) (method p) fuel
            (replay O ω (t + 1)).2
            (fun i => budget p i - callsUsed (replay O ω (t + 1)).1 i)
            (replay O ω (t + 1)).1 = _
          exact ih (t + 1) fuel (by omega) (by omega)

lemma executeWithTrace_eq_replay (hp : spec.valid p) (ω : Randomness p O) :
    executeWithTrace O (method p) (budget p) ω.1 ω.2 =
      (traceOutput O ω, (replay O ω (stageOffset p (finalStage p + 1))).2) := by
  rw [executeWithTrace_eq_runWithBudget]
  have hrun := run_from_prefix O hp ω (stageOffset p (finalStage p + 1))
    0 (∑ i : Fin 4, budget p i) (by omega) (total_fuel_sufficient (p := p) hp)
  have hremaining :
      (fun i => budget p i - callsUsed (replay O ω 0).1 i) = budget p := by
    rw [replay_zero, initial_calls_used]
    funext i
    simp
  rw [hremaining] at hrun
  exact hrun

lemma execute_eq_traceOutput (hp : spec.valid p) (ω : Randomness p O) :
    execute O (method p) (budget p) ω.1 ω.2 = traceOutput O ω := by
  exact congrArg Prod.fst (executeWithTrace_eq_replay O hp ω)

lemma outputWithCounts_eq_traceOutput (hp : spec.valid p) (ω : Randomness p O) :
    LongTails.Algorithms.ProximalEf21Homotopy.outputWithCounts
      p O (budget p) ω.1 ω.2 = traceOutput O ω := by
  exact execute_eq_traceOutput O hp ω

lemma execute_success (hp : spec.valid p) {I : Instance p}
    (hg : ProblemAssumptions p I) (ho : OracleAssumptions p I O) :
    spec.successful p I
      (fun ω : Randomness p O =>
        LongTails.Algorithms.ProximalEf21Homotopy.outputWithCounts
          p O (budget p) ω.1 ω.2)
      ((p.initialLaw).prod O.law) := by
  have houtput :
      (fun ω : Randomness p O =>
        LongTails.Algorithms.ProximalEf21Homotopy.outputWithCounts
          p O (budget p) ω.1 ω.2) = traceOutput O := by
    funext ω
    exact outputWithCounts_eq_traceOutput O hp ω
  rw [houtput]
  exact trace_success O hp hg ho

end LongTails.Proofs.ProximalEf21Execution
