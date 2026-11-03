import LongTails.Algorithms.FiniteSumNondualProx
import LongTails.Proofs.ComponentEnvelopeExecution

namespace LongTails.Proofs.FiniteSumNondualProxExecution

open LongTails.Algorithms.FiniteSumNondualProx
open OracleTemplate.ComponentEnvelope (Program)
open OracleTemplate.FiniteSum (estimator fullGradient)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma snapshot_eval (g : Fin n × E → E) (x : E) (m : ℕ) (indices : Fin m → Fin n) :
    Program.eval g (snapshot x m indices) = fun j => g (indices j, x) := by
  induction m with
  | zero => funext j; exact Fin.elim0 j
  | succ m ih =>
    simp only [snapshot, Program.eval, Program.eval_map, ih]
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma snapshot_cost (g : Fin n × E → E) (x : E) (m : ℕ) (indices : Fin m → Fin n) :
    Program.cost g (snapshot x m indices) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [snapshot, Program.cost, Program.cost_map, ih]

lemma innerPlan_eval (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c z x : E)
    (seed : List (Fin n)) :
    Program.eval g (innerPlan C μ η c (fun i => g (i, z)) x seed) = innerRun g C μ η c z x seed := by
  induction seed generalizing x with
  | nil => rfl
  | cons i tail ih =>
    simp only [innerPlan, Program.eval, Program.eval_map, ih, innerRun, estimator,
      fullGradient, cacheMean]

lemma innerPlan_cost (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c : E)
    (cache : Fin n → E) (x : E) (seed : List (Fin n)) :
    Program.cost g (innerPlan C μ η c cache x seed) = seed.length := by
  induction seed generalizing x with
  | nil => rfl
  | cons i tail ih => simp only [innerPlan, Program.cost, Program.cost_map, ih, List.length_cons]

lemma epochPlan_eval (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c z : E)
    (seed : List (Fin n)) : Program.eval g (epochPlan C μ η c z seed) = epoch g C μ η c z seed := by
  simp only [epochPlan, Program.eval_bind, snapshot_eval, id_eq, Program.eval_map, innerPlan_eval, epoch]

lemma epochPlan_cost (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c z : E)
    (seed : List (Fin n)) : Program.cost g (epochPlan C μ η c z seed) = n + seed.length := by
  simp only [epochPlan, Program.cost_bind, snapshot_cost, Program.cost_map, innerPlan_cost]

lemma epochsPlan_eval {m : ℕ} (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c : E)
    (s : ℕ) (z : E) (seed : Fin s → Fin m → Fin n) :
    Program.eval g (epochsPlan C μ η c s z seed) = epochRun g C μ η c s z seed := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih => simp only [epochsPlan, Program.eval_bind, epochPlan_eval, ih, epochRun]

lemma epochsPlan_cost {m : ℕ} (g : Fin n × E → E) (C : Set E) (μ η : ℝ) (c : E)
    (s : ℕ) (z : E) (seed : Fin s → Fin m → Fin n) :
    Program.cost g (epochsPlan C μ η c s z seed) = s * (n + m) := by
  induction s generalizing z with
  | zero => simp [epochsPlan, Program.cost]
  | succ s ih =>
    simp only [epochsPlan, Program.cost_bind, epochPlan_cost, List.length_ofFn, ih]
    ring

lemma solvePlan_cost (g : Fin n × E → E) (C : Set E) (L μ : ℝ) (c : E)
    (s : ℕ) (seed : Fin s → Fin (144 * n) → Fin n) :
    Program.cost g (solvePlan C L μ c s seed) = (145 * s + 3) * n := by
  simp only [solvePlan, Program.cost_bind, snapshot_cost, epochsPlan_cost, Program.cost_map]
  ring

lemma solvePlan_eval (g : Fin n × E → E) (C : Set E) (L μ : ℝ) (c : E)
    (s : ℕ) (seed : Fin s → Fin (144 * n) → Fin n) :
    Program.eval g (solvePlan C L μ c s seed) =
      let initial := step C μ (1 / L) c c (fullGradient g c)
      let x := epochRun g C μ (1 / (12 * L)) c s initial seed
      let w := step C μ (1 / L) c x (fullGradient g x)
      ⟨w, fullGradient g w,
        LongTails.Algorithms.FiniteSumNondualProx.residual (1 / L) x w (fullGradient g x) (fullGradient g w)⟩ := by
  simp only [solvePlan, Program.eval_bind, snapshot_eval, id_eq, epochsPlan_eval, Program.eval_map,
    cacheMean, fullGradient]

end LongTails.Proofs.FiniteSumNondualProxExecution
