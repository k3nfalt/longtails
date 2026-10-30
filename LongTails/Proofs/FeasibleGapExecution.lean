import LongTails.Algorithms.QueryPlan

namespace LongTails.Proofs.FeasibleGapExecution

open OracleTemplate

variable {Q R U V : Type*}

def Supported (g : Q → R) (allowed : Q → Prop) : {k : ℕ} → QueryPlan Q R U k → Prop
  | _, .done _ => True
  | _, .ask q next => allowed q ∧ Supported g allowed (next (g q))

lemma supported_bind (g : Q → R) (allowed : Q → Prop) {k m : ℕ}
    (plan : QueryPlan Q R U k) (next : U → QueryPlan Q R V m)
    (hp : Supported g allowed plan)
    (hn : Supported g allowed (next (QueryPlan.eval g plan))) :
    Supported g allowed (plan.bind next) := by
  induction plan with
  | done value => exact hn
  | ask q rest ih => exact ⟨hp.1, ih (g q) hp.2 hn⟩

noncomputable def step (O : Oracle Q R) (q0 : Q) (ξ : (k : ℕ) → O.Seed k)
    (sc : (Σ k, QueryPlan Q R U k) × List ((Fin 1 × Q) × R)) :=
  let q := (0, QueryPlan.query q0 sc.1)
  let r := O.answer sc.2 q (ξ sc.2.length)
  (QueryPlan.update sc.1 r, sc.2 ++ [(q, r)])

lemma supported_advance (O : Oracle Q R) (g : Q → R) (allowed : Q → Prop)
    (hans : ∀ history q seed, allowed q → O.answer history (0, q) seed = g q)
    (q0 : Q) (ξ : (k : ℕ) → O.Seed k) {k K : ℕ} (plan : QueryPlan Q R U k)
    (hp : Supported g allowed plan) (hK : k ≤ K)
    (history : List ((Fin 1 × Q) × R)) :
    ((step O q0 ξ)^[K] (⟨k, plan⟩, history)).1 = ⟨0, .done (QueryPlan.eval g plan)⟩ := by
  induction plan generalizing K history with
  | done value =>
    induction K generalizing history with
    | zero => rfl
    | succ K ih =>
      rw [Function.iterate_succ_apply]
      exact ih (Nat.zero_le K) _
  | @ask k q rest ih =>
    cases K with
    | zero => omega
    | succ K =>
      rw [Function.iterate_succ_apply]
      simp only [step, QueryPlan.query, QueryPlan.update, hans _ q _ hp.1]
      exact ih (g q) hp.2 (by omega) _

lemma execute_supported {S : Type} [MeasurableSpace S]
    (O : Oracle Q R) (g : Q → R) (allowed : Q → Prop)
    (hans : ∀ history q seed, allowed q → O.answer history (0, q) seed = g q)
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k) (seed : S)
    (hp : Supported g allowed (plan seed)) (hK : k ≤ K) (ξ : (n : ℕ) → O.Seed n) :
    execute O (QueryPlan.algorithm law q0 u0 k plan) (fun _ => K) seed ξ =
      QueryPlan.eval g (plan seed) := by
  erw [execute_indexed]
  change QueryPlan.output u0 (((step O q0 ξ)^[K]) (⟨k, plan seed⟩, [])).1 = _
  rw [supported_advance O g allowed hans q0 ξ (plan seed) hp hK []]
  rfl

end LongTails.Proofs.FeasibleGapExecution
