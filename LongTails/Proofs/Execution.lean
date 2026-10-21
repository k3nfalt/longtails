import LongTails.Template
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

open MeasureTheory

namespace OracleTemplate

lemma execute_eq_of_answer_eq {Query Reply Output : Type*}
    (oracle : Oracle Query Reply 1) (g : Query → Reply)
    (h : ∀ k query seed, oracle.answer k (0, query) seed = g query)
    (A : Algorithm Query Reply Output 1) (K : ℕ) (seed : A.Seed) (oracleSeed : (k : ℕ) → oracle.Seed k) :
    execute oracle A (fun _ => K) seed oracleSeed =
      execute { answer := fun _ query _ => g query.2 } A (fun _ => K) seed := by
  unfold execute executeWithTrace
  congr 2
  funext k query
  obtain ⟨i, query⟩ := query
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact h k query (oracleSeed k.length)

lemma executeWithTrace_indexed {Query Reply Output : Type*} (oracle : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) :
    executeWithTrace oracle A (fun _ => K) seed ξ =
      let sc := ((fun sc : A.State × List ((Fin 1 × Query) × Reply) =>
          let query := A.query sc.1
          let reply := oracle.answer sc.2 query (ξ sc.2.length)
          (A.update sc.1 reply, sc.2 ++ [(query, reply)]))^[K]
          (A.initial seed, []))
      (A.output sc.1, sc.2) := by
  let step := fun sc : A.State × List ((Fin 1 × Query) × Reply) =>
    let query := A.query sc.1
    let reply := oracle.answer sc.2 query (ξ sc.2.length)
    (A.update sc.1 reply, sc.2 ++ [(query, reply)])
  change executeWithTrace oracle A (fun _ => K) seed ξ =
    (A.output (step^[K] (A.initial seed, [])).1, (step^[K] (A.initial seed, [])).2)
  unfold executeWithTrace
  simp only [Fin.sum_univ_one]
  generalize A.initial seed = state
  generalize ([] : List ((Fin 1 × Query) × Reply)) = history
  induction K generalizing state history with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      change (if k + 1 = 0 then (A.output state, history) else _) = _
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      have hr : Function.update (fun _ : Fin 1 => k + 1) (A.query state).1 k = fun _ => k := by
        funext i
        have hi : i = (A.query state).1 := Subsingleton.elim _ _
        subst i
        simp
      simp only [Nat.add_sub_cancel]
      rw [hr]
      exact ih _ _

lemma execute_indexed {Query Reply Output : Type*} (oracle : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) :
    execute oracle A (fun _ => K) seed ξ =
      A.output ((fun sc : A.State × List ((Fin 1 × Query) × Reply) =>
          let query := A.query sc.1
          let reply := oracle.answer sc.2 query (ξ sc.2.length)
          (A.update sc.1 reply, sc.2 ++ [(query, reply)]))^[K]
          (A.initial seed, [])).1 := by
  exact congrArg Prod.fst (executeWithTrace_indexed oracle A K seed ξ)

lemma execute_indexed_of_answer {Query Reply Output : Type*} (oracle : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k)
    (response : ℕ → (Fin 1 × Query) → Reply)
    (h : ∀ history query, oracle.answer history query (ξ history.length) = response history.length query) :
    execute oracle A (fun _ => K) seed ξ =
      A.output ((fun sc : A.State × ℕ =>
          (A.update sc.1 (response sc.2 (A.query sc.1)), sc.2 + 1))^[K]
          (A.initial seed, 0)).1 := by
  let step := fun sc : A.State × ℕ =>
    (A.update sc.1 (response sc.2 (A.query sc.1)), sc.2 + 1)
  change execute oracle A (fun _ => K) seed ξ =
    A.output (step^[K] (A.initial seed, ([] : List ((Fin 1 × Query) × Reply)).length)).1
  unfold execute executeWithTrace
  simp only [Fin.sum_univ_one]
  generalize A.initial seed = state
  generalize ([] : List ((Fin 1 × Query) × Reply)) = history
  induction K generalizing state history with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      change (if k + 1 = 0 then (A.output state, history) else _).1 = _
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      have hr : Function.update (fun _ : Fin 1 => k + 1) (A.query state).1 k = fun _ => k := by
        funext i
        have hi : i = (A.query state).1 := Subsingleton.elim _ _
        subst i
        simp
      simp only [Nat.add_sub_cancel]
      rw [hr, ih]
      simp only [List.length_append, List.length_singleton, h, step]

lemma execute_iterate {Query Reply Output : Type*} (oracle : Query → Reply)
    (A : Algorithm Query Reply Output 1) (K : ℕ) (seed : A.Seed) :
    execute { answer := fun _ query _ => oracle query.2 } A (fun _ => K) seed =
      A.output ((fun s => A.update s (oracle (A.query s).2))^[K] (A.initial seed)) := by
  rw [execute_indexed]
  let step := fun sc : A.State × List ((Fin 1 × Query) × Reply) =>
    (A.update sc.1 (oracle (A.query sc.1).2), sc.2 ++ [(A.query sc.1, oracle (A.query sc.1).2)])
  change A.output (step^[K] (A.initial seed, [])).1 = _
  congr 1
  generalize A.initial seed = state
  generalize ([] : List ((Fin 1 × Query) × Reply)) = history
  induction K generalizing state history with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _

lemma execute_eq_of_safe_prefix {Query Reply Output : Type*} {n : ℕ}
    (O : Oracle Query Reply n) (A : Algorithm Query Reply Output n)
    (budget : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (state : ℕ → A.State) (remaining : ℕ → Fin n → ℕ) (T : ℕ) (output : Output)
    (hstate : state 0 = A.initial seed)
    (hstep : ∀ history, state (history.length + 1) =
      A.update (state history.length) (O.answer history (A.query (state history.length)) (ξ history.length)))
    (hremaining : remaining 0 = budget)
    (hconsume : ∀ k, remaining (k + 1) = Function.update (remaining k)
      (A.query (state k)).1 (remaining k (A.query (state k)).1 - 1))
    (hsafe : ∀ k, k < T → 0 < remaining k (A.query (state k)).1)
    (houtput : ∀ k, T ≤ k → A.output (state k) = output)
    (hT : T ≤ ∑ i, budget i) : execute O A budget seed ξ = output := by
  unfold execute executeWithTrace
  generalize hf : (∑ i, budget i) = fuel
  have hbound : T ≤ fuel := hf ▸ hT
  rw [← hstate, ← hremaining]
  generalize hc : ([] : List ((Fin n × Query) × Reply)) = history
  have hlen : history.length = 0 := by rw [← hc]; rfl
  conv_lhs => rw [← hlen]
  have hb : T ≤ history.length + fuel := by omega
  clear hf hbound hT hc hlen
  induction fuel generalizing history with
  | zero => exact houtput history.length (by omega)
  | succ fuel ih =>
      change (if remaining history.length (A.query (state history.length)).1 = 0 then
        (A.output (state history.length), history) else _).1 = output
      split_ifs with hz
      · exact houtput history.length (by by_contra h; have := hsafe history.length (by omega); omega)
      · dsimp only
        rw [← hstep, ← hconsume]
        simpa only [List.length_append, List.length_singleton] using
          ih (history ++ [(A.query (state history.length),
            O.answer history (A.query (state history.length)) (ξ history.length))]) (by simp; omega)

lemma convergence_of_public_budget {S : Setup} (B : S.Public → ℕ)
    (h : ∃ make : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
      (∀ p, S.valid p → ∀ I O, S.admissible p I O →
        let A := make (S.publicInput p)
        S.successful p I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => B (S.publicInput p)) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩) ∧
      ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (make (S.publicInput p))) :
    Convergence S (fun p _ => B (S.publicInput p)) := h

lemma convergence_of_call_budget {S : Setup} (budget : S.Params → ℕ)
    (h : ∃ make : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
      (∀ p, S.valid p → ∀ K, budget p ≤ K → ∀ I O, S.admissible p I O →
        let A := make (S.publicInput p)
        S.successful p I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => K) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩) ∧
      ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (make (S.publicInput p))) :
    Convergence S (fun p _ => budget p) := by
  obtain ⟨make, correct, allowed⟩ := h
  exact ⟨make, fun p hp => correct p hp (budget p) le_rfl, allowed⟩

lemma convergence_of_block_budget {S : Setup} (B : S.Params → ℕ) (m : S.Public → ℕ)
    (h : ∃ make : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
      (∀ p, S.valid p → ∀ N, B p ≤ N → ∀ I O, S.admissible p I O →
        let A := make (S.publicInput p)
        S.successful p I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
            execute O A (fun _ => m (S.publicInput p) * N) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩) ∧
      ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (make (S.publicInput p))) :
    Convergence S (fun p _ => m (S.publicInput p) * B p) := by
  obtain ⟨make, correct, allowed⟩ := h
  exact ⟨make, fun p hp => correct p hp (B p) le_rfl, allowed⟩

end OracleTemplate
