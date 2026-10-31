import LongTails.Template
import LongTails.Proofs.Execution
import LongTails.Proofs.SgdExecution

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

namespace OracleTemplate.QueryPlan

variable {Q R U V : Type*}

lemma eval_bind (g : Q → R) {k m : ℕ} (plan : QueryPlan Q R U k)
    (next : U → QueryPlan Q R V m) :
    eval g (bind plan next) = eval g (next (eval g plan)) := by
  induction plan with
  | done value => rfl
  | ask q rest ih => exact ih (g q)

lemma eval_map (g : Q → R) (f : U → V) {k : ℕ} (plan : QueryPlan Q R U k) :
    eval g (map f plan) = f (eval g plan) := by
  induction plan with
  | done value => rfl
  | ask q rest ih => exact ih (g q)

lemma eval_traverse (g : Q → R) {c : ℕ} (k : ℕ)
    (plans : Fin k → QueryPlan Q R U c) :
    eval g (traverse k plans) = List.ofFn (fun i => eval g (plans i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [traverse, eval_bind, eval_map, ih, List.ofFn_succ]

lemma advance_plan (g : Q → R) (q0 : Q) {k : ℕ} (plan : QueryPlan Q R U k)
    (call : ℕ) :
    StochasticGradient.advance (fun _ s => update s (g (query q0 s))) k call ⟨k, plan⟩ =
      ⟨0, done (eval g plan)⟩ := by
  induction plan generalizing call with
  | done value => rfl
  | ask q rest ih => exact ih (g q) (call + 1)

lemma execute_plan {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (K : ℕ) (plan : S → QueryPlan Q R U K) (g : Q → R) (seed : S) :
    execute { answer := fun _ (_, q) _ => g q } (algorithm law q0 u0 K plan) (fun _ => K) seed =
      eval g (plan seed) := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun _ q => g q.2) (fun _ _ => rfl)]
  change output u0 (StochasticGradient.advance
    (fun _ s => update s (g (query q0 s))) K 0 ⟨K, plan seed⟩) = _
  rw [advance_plan]
  rfl

lemma advance_plan_of_le (g : Q → R) (q0 : Q) {k K : ℕ}
    (plan : QueryPlan Q R U k) (h : k ≤ K) (call : ℕ) :
    StochasticGradient.advance (fun _ s => update s (g (query q0 s))) K call ⟨k, plan⟩ =
      ⟨0, done (eval g plan)⟩ := by
  induction plan generalizing K call with
  | done value =>
      induction K generalizing call with
      | zero => rfl
      | succ K ih => exact ih (Nat.zero_le K) (call + 1)
  | @ask k q rest ih =>
      cases K with
      | zero => omega
      | succ K => exact ih (g q) (by omega) (call + 1)

lemma execute_plan_of_le {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (k K : ℕ) (plan : S → QueryPlan Q R U k) (g : Q → R) (seed : S) (h : k ≤ K) :
    execute { answer := fun _ (_, q) _ => g q } (algorithm law q0 u0 k plan) (fun _ => K) seed =
      eval g (plan seed) := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun _ q => g q.2) (fun _ _ => rfl)]
  change output u0 (StochasticGradient.advance
    (fun _ s => update s (g (query q0 s))) K 0 ⟨k, plan seed⟩) = _
  rw [advance_plan_of_le g q0 _ h]
  rfl

end OracleTemplate.QueryPlan
