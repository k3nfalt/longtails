import LongTails.Algorithms.QueryPlan

namespace LongTails.Algorithms.QueryLayers

open OracleTemplate

variable {Q R U : Type}

inductive FixedQueries : {k : ℕ} → QueryPlan Q R U k → List Q → Prop
  | done (value : U) : FixedQueries (.done value) []
  | ask {k : ℕ} (q : Q) (next : R → QueryPlan Q R U k) (qs : List Q)
      (tail : ∀ r, FixedQueries (next r) qs) : FixedQueries (.ask q next) (q :: qs)

inductive Layers {Q R : Type} : {U : Type} → {k : ℕ} → QueryPlan Q R U k → ℕ → Prop
  | done {U : Type} (value : U) : Layers (.done value : QueryPlan Q R U 0) 0
  | fixed {U : Type} {k : ℕ} (plan : QueryPlan Q R U k) (qs : List Q)
      (fixedQueries : FixedQueries plan qs) : Layers plan 1
  | bind {U V : Type} {k m n l : ℕ} (plan : QueryPlan Q R U k)
      (next : U → QueryPlan Q R V m) (first : Layers plan n)
      (rest : ∀ value, Layers (next value) l) : Layers (plan.bind next) (n + l)

def queryTrace (reply : ℕ → Q → R) : {k : ℕ} → QueryPlan Q R U k → ℕ → List Q
  | _, .done _, _ => []
  | _, .ask q next, call => q :: queryTrace reply (next (reply call q)) (call + 1)

def paddingPlan (q0 : Q) (value : U) : (n : ℕ) → QueryPlan Q R U n
  | 0 => .done value
  | n + 1 => .ask q0 (fun _ => paddingPlan q0 value n)

def paddedPlan {k : ℕ} (q0 : Q) (plan : QueryPlan Q R U k) (n : ℕ) :
    QueryPlan Q R U (n + k) := plan.bind (fun value => paddingPlan q0 value n)

def executionTrace (q0 : Q) (reply : ℕ → Q → R) :
    ℕ → ℕ → (Σ k, QueryPlan Q R U k) → List Q
  | 0, _, _ => []
  | n + 1, call, state =>
    let q := QueryPlan.query q0 state
    q :: executionTrace q0 reply n (call + 1) (QueryPlan.update state (reply call q))

end LongTails.Algorithms.QueryLayers
