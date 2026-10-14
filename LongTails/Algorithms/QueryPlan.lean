import LongTails.Template

namespace OracleTemplate

inductive QueryPlan (Q R U : Type*) : ℕ → Type _
  | done (value : U) : QueryPlan Q R U 0
  | ask {k : ℕ} (query : Q) (next : R → QueryPlan Q R U k) : QueryPlan Q R U (k + 1)

namespace QueryPlan

variable {Q R U V : Type*}

def eval (g : Q → R) : {k : ℕ} → QueryPlan Q R U k → U
  | _, .done value => value
  | _, .ask query next => eval g (next (g query))

def bind {m : ℕ} : {k : ℕ} → QueryPlan Q R U k →
    (U → QueryPlan Q R V m) → QueryPlan Q R V (m + k)
  | _, .done value, next => next value
  | _, .ask query rest, next => .ask query (fun reply => bind (rest reply) next)

def map (f : U → V) : {k : ℕ} → QueryPlan Q R U k → QueryPlan Q R V k
  | _, .done value => .done (f value)
  | _, .ask q rest => .ask q (fun reply => map f (rest reply))

def traverse {c : ℕ} : (k : ℕ) → (Fin k → QueryPlan Q R U c) →
    QueryPlan Q R (List U) (c * k)
  | 0, _ => .done []
  | k + 1, plans => bind (plans 0)
      (fun value => map (value :: ·) (traverse k (fun i => plans i.succ)))

def query (fallback : Q) : (Σ k, QueryPlan Q R U k) → Q
  | ⟨_, .done _⟩ => fallback
  | ⟨_, .ask q _⟩ => q

def update : (Σ k, QueryPlan Q R U k) → R → (Σ k, QueryPlan Q R U k)
  | ⟨_, .done value⟩, _ => ⟨0, .done value⟩
  | ⟨_, .ask _ next⟩, reply => ⟨_, next reply⟩

def output (fallback : U) : (Σ k, QueryPlan Q R U k) → U
  | ⟨_, .done value⟩ => value
  | ⟨_, .ask _ _⟩ => fallback

noncomputable def algorithm {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (K : ℕ) (plan : S → QueryPlan Q R U K) : Algorithm Q R U where
  Seed := S
  law := law
  State := Σ k, QueryPlan Q R U k
  initial seed := ⟨K, plan seed⟩
  query := fun s => (0, (query q0) s)
  update := update
  output := output u0

end QueryPlan
end OracleTemplate
