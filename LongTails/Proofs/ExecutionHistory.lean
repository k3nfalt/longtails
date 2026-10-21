import LongTails.Proofs.SgdExecution

namespace OracleTemplate

open private _run from LongTails.Template

def executeIndexedState {Query Reply Output : Type*} {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles)
    (A : Algorithm Query Reply Output numOracles) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) : ℕ → A.State × List ((Fin numOracles × Query) × Reply)
  | 0 => (A.initial seed, [])
  | n + 1 =>
      let (state, history) := executeIndexedState oracle A seed ξ n
      let query := A.query state
      let reply := oracle.answer history query (ξ history.length)
      (A.update state reply, history ++ [(query, reply)])

lemma executeIndexedState_length {Query Reply Output : Type*} {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) (n : ℕ) :
    (executeIndexedState oracle A seed ξ n).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [executeIndexedState, ih]

lemma executeIndexedState_eq_iterate {Query Reply Output : Type*} {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) (n : ℕ) :
    executeIndexedState oracle A seed ξ n =
      ((fun sc : A.State × List ((Fin numOracles × Query) × Reply) =>
        let query := A.query sc.1
        let reply := oracle.answer sc.2 query (ξ sc.2.length)
        (A.update sc.1 reply, sc.2 ++ [(query, reply)]))^[n] (A.initial seed, [])) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let step : A.State × List ((Fin numOracles × Query) × Reply) →
          A.State × List ((Fin numOracles × Query) × Reply) := fun sc =>
        let query := A.query sc.1
        let reply := oracle.answer sc.2 query (ξ sc.2.length)
        (A.update sc.1 reply, sc.2 ++ [(query, reply)])
      rw [executeIndexedState, Function.iterate_succ_apply']
      exact congrArg step ih

lemma executeWithTrace_eq_executeIndexedState {Query Reply Output : Type*}
    (oracle : Oracle Query Reply) (A : Algorithm Query Reply Output) (K : ℕ)
    (seed : A.Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    executeWithTrace oracle A (fun _ => K) seed ξ =
      (A.output (executeIndexedState oracle A seed ξ K).1,
        (executeIndexedState oracle A seed ξ K).2) := by
  rw [executeWithTrace_indexed, executeIndexedState_eq_iterate]

def executeAnswerAt {Query Reply Output : Type*} {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles)
    (A : Algorithm Query Reply Output numOracles) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) (k : ℕ) (query : Fin numOracles × Query) : Reply :=
    oracle.answer (executeIndexedState oracle A seed ξ k).2 query
      (ξ (executeIndexedState oracle A seed ξ k).2.length)

lemma executeIndexedState_eq_executeAnswerAt {Query Reply Output : Type*} {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) (n : ℕ) :
    (executeIndexedState oracle A seed ξ n).1 =
      ((fun sc : A.State × ℕ =>
        (A.update sc.1 (executeAnswerAt oracle A seed ξ sc.2 (A.query sc.1)), sc.2 + 1))^[n]
        (A.initial seed, 0)).1 := by
  let clockStep : A.State × ℕ → A.State × ℕ := fun sc =>
    (A.update sc.1 (executeAnswerAt oracle A seed ξ sc.2 (A.query sc.1)), sc.2 + 1)
  change (executeIndexedState oracle A seed ξ n).1 = (clockStep^[n] (A.initial seed, 0)).1
  have hclock (n : ℕ) : (clockStep^[n] (A.initial seed, 0)).2 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply']; simp [clockStep, ih]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [executeIndexedState, Function.iterate_succ_apply']
      cases hrun : executeIndexedState oracle A seed ξ n with
      | mk state history =>
          simp only [hrun] at ih ⊢
          rw [ih]
          simp only [clockStep, hclock]
          congr 1
          unfold executeAnswerAt
          rw [hrun]


lemma execute_eq_of_history_safe_prefix {Query Reply Output : Type*} {n : ℕ}
    (O : Oracle Query Reply n) (A : Algorithm Query Reply Output n)
    (budget : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (remaining : ℕ → Fin n → ℕ) (T : ℕ) (output : Output)
    (hremaining : remaining 0 = budget)
    (hconsume : ∀ k, remaining (k + 1) = Function.update (remaining k)
      (A.query (executeIndexedState O A seed ξ k).1).1
      (remaining k (A.query (executeIndexedState O A seed ξ k).1).1 - 1))
    (hsafe : ∀ k, k < T → 0 < remaining k (A.query (executeIndexedState O A seed ξ k).1).1)
    (houtput : ∀ k, T ≤ k → A.output (executeIndexedState O A seed ξ k).1 = output)
    (hT : T ≤ ∑ i, budget i) : execute O A budget seed ξ = output := by
  have run : ∀ fuel k, T ≤ k + fuel →
      (_run (fun history query => O.answer history query (ξ history.length)) A fuel
        (executeIndexedState O A seed ξ k).2 (remaining k)
        (executeIndexedState O A seed ξ k).1).1 = output := by
    intro fuel
    induction fuel with
    | zero => intro k hk; exact houtput k (by omega)
    | succ fuel ih =>
      intro k hk
      unfold _run
      dsimp only
      split_ifs with hz
      · exact houtput k (by by_contra h; have := hsafe k (by omega); omega)
      · simpa only [executeIndexedState, hconsume] using ih (k + 1) (by omega)
  simpa only [execute, executeWithTrace, executeIndexedState, hremaining] using
    run (∑ i, budget i) 0 (by omega)

lemma execute_advance_history {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O A (fun _ => K) seed ξ =
      A.output (StochasticGradient.advance
        (fun k state => A.update state (executeAnswerAt O A seed ξ k (A.query state)))
        K 0 (A.initial seed)) := by
  unfold execute
  rw [executeWithTrace_eq_executeIndexedState]
  dsimp only
  rw [executeIndexedState_eq_executeAnswerAt]
  congr 1
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction K generalizing state call with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ _

end OracleTemplate
