import LongTails.Algorithms.ComponentEnvelope
import LongTails.Proofs.Execution

namespace OracleTemplate.ComponentEnvelope

namespace Program

variable {Q R U V : Type*}

def eval (g : Q → R) : Program Q R U → U
  | .done u => u
  | .ask q next => eval g (next (g q))

def cost (g : Q → R) : Program Q R U → ℕ
  | .done _ => 0
  | .ask q next => cost g (next (g q)) + 1

lemma eval_bind (g : Q → R) (p : Program Q R U) (next : U → Program Q R V) :
    eval g (p.bind next) = eval g (next (eval g p)) := by
  induction p with
  | done u => rfl
  | ask q rest ih => exact ih (g q)

lemma cost_bind (g : Q → R) (p : Program Q R U) (next : U → Program Q R V) :
    cost g (p.bind next) = cost g p + cost g (next (eval g p)) := by
  induction p with
  | done u => simp [bind, cost, eval]
  | ask q rest ih =>
      simp only [bind, cost, eval, ih (g q)]
      omega

lemma eval_map (g : Q → R) (p : Program Q R U) (f : U → V) :
    eval g (p.map f) = f (eval g p) := by
  rw [map, eval_bind]
  rfl

lemma cost_map (g : Q → R) (p : Program Q R U) (f : U → V) :
    cost g (p.map f) = cost g p := by
  rw [map, cost_bind]
  rfl

lemma iterate_done (g : Q → R) (fallback : Q) (u : U) (K : ℕ) :
    (fun p : Program Q R U => p.update (g (p.query fallback)))^[K] (.done u) = .done u := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply]
      exact ih

lemma iterate_of_cost_le (g : Q → R) (fallback : Q) (K : ℕ) (p : Program Q R U)
    (h : cost g p ≤ K) :
    (fun p : Program Q R U => p.update (g (p.query fallback)))^[K] p = .done (eval g p) := by
  induction K generalizing p with
  | zero =>
      cases p with
      | done u => rfl
      | ask q next => simp [cost] at h
  | succ K ih =>
      cases p with
      | done u => exact iterate_done g fallback u (K + 1)
      | ask q next =>
          rw [Function.iterate_succ_apply]
          exact ih (next (g q)) (by simpa [cost] using h)

end Program

open LongTails.Setups.InterpolatedGeneralizedFiniteSum

lemma execute_of_cost_le (p : Params) (g : Fin p.n → p.E → p.E)
    (oracle : Oracle (Fin p.n × p.E) p.E)
    (hg : ∀ history query seed, oracle.answer history (0, query) seed = g query.1 query.2)
    (K : ℕ) (seed : Seeds p) (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hcost : Program.cost (fun q => g q.1 q.2) (plan p seed) ≤ K) :
    output p oracle K seed oracleSeed = Program.eval (fun q => g q.1 q.2) (plan p seed) := by
  unfold output
  erw [execute_eq_of_answer_eq oracle (fun q => g q.1 q.2) hg,
    execute_iterate (fun q : Fin p.n × p.E => g q.1 q.2) (algorithm p) K seed]
  change Program.output p.x0
    ((fun state : Program (Fin p.n × p.E) p.E p.E =>
      state.update (g (state.query (0, p.x0)).1 (state.query (0, p.x0)).2))^[K]
        (plan p seed)) = _
  rw [Program.iterate_of_cost_le (fun q => g q.1 q.2) (0, p.x0) K _ hcost]
  rfl

lemma snapshot_eval (p : Params) (g : Fin p.n × p.E → p.E) (x : p.E)
    (k : ℕ) (indices : Fin k → Fin p.n) :
    Program.eval g (snapshotPlan p x k indices) = fun j => Program.eval g (componentPlan p (indices j) x) := by
  induction k with
  | zero => funext j; exact Fin.elim0 j
  | succ k ih =>
      simp only [snapshotPlan, Program.eval_bind, Program.eval_map, ih]
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> rfl

lemma snapshot_cost (p : Params) (g : Fin p.n × p.E → p.E) (x : p.E)
    (k : ℕ) (indices : Fin k → Fin p.n) :
    Program.cost g (snapshotPlan p x k indices) = ∑ j, Program.cost g (componentPlan p (indices j) x) := by
  induction k with
  | zero => simp [snapshotPlan, Program.cost]
  | succ k ih => simp [snapshotPlan, Program.cost_bind, Program.cost_map, ih, Fin.sum_univ_succ]


lemma epochs_eval_succ (p : Params) (g : Fin p.n × p.E → p.E)
    (k : ℕ) (samples : Fin (k + 1) → Fin p.n → Fin p.n) (s : ℕ) (snapshot y z : p.E) :
    Program.eval g (epochsPlan p (k + 1) samples s snapshot y z) =
      let cache := fun i => Program.eval g (componentPlan p i snapshot)
      let state := Program.eval g (epochPlan p s snapshot cache p.n (samples 0) ⟨y, z, 0⟩)
      Program.eval g (epochsPlan p k (fun j => samples j.succ) (s + 1)
        ((p.n : ℝ)⁻¹ • state.total) state.y state.z) := by
  simp only [epochsPlan, Program.eval_bind, snapshot_eval, id_eq]

lemma epochs_cost_succ (p : Params) (g : Fin p.n × p.E → p.E)
    (k : ℕ) (samples : Fin (k + 1) → Fin p.n → Fin p.n) (s : ℕ) (snapshot y z : p.E) :
    Program.cost g (epochsPlan p (k + 1) samples s snapshot y z) =
      let cache := fun i => Program.eval g (componentPlan p i snapshot)
      let state := Program.eval g (epochPlan p s snapshot cache p.n (samples 0) ⟨y, z, 0⟩)
      (∑ i, Program.cost g (componentPlan p i snapshot)) +
        Program.cost g (epochPlan p s snapshot cache p.n (samples 0) ⟨y, z, 0⟩) +
        Program.cost g (epochsPlan p k (fun j => samples j.succ) (s + 1)
          ((p.n : ℝ)⁻¹ • state.total) state.y state.z) := by
  simp only [epochsPlan, Program.cost_bind, snapshot_eval, snapshot_cost, id_eq]
  omega


end OracleTemplate.ComponentEnvelope
