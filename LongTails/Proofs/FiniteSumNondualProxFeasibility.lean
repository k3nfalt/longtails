import LongTails.Proofs.FiniteSumNondualProxEpoch
import LongTails.Proofs.FiniteSumNondualProxExecution

namespace LongTails.Proofs.FiniteSumNondualProxFeasibility

open LongTails.Algorithms.FiniteSumNondualProx
open OracleTemplate.ComponentEnvelope (Program)
open FiniteSumNondualProxStep FiniteSumNondualProxEpoch

def Checked {Q Reply U : Type*} (goodQuery : Q → Prop) (goodOutput : U → Prop) :
    Program Q Reply U → Prop
  | .done u => goodOutput u
  | .ask q next => goodQuery q ∧ ∀ reply, Checked goodQuery goodOutput (next reply)

lemma checked_bind {Q Reply U V : Type*} {pq : Q → Prop} {pu : U → Prop} {pv : V → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program) (next : U → Program Q Reply V)
    (hn : ∀ u, pu u → Checked pq pv (next u)) : Checked pq pv (program.bind next) := by
  induction program with
  | done u => exact hn u hp
  | ask q rest ih => exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

lemma checked_map {Q Reply U V : Type*} {pq : Q → Prop} {pu : U → Prop} {pv : V → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program) (f : U → V)
    (hf : ∀ u, pu u → pv (f u)) : Checked pq pv (program.map f) :=
  checked_bind hp (fun u => .done (f u)) hf

lemma checked_eval {Q Reply U : Type*} {pq : Q → Prop} {pu : U → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program) (g : Q → Reply) :
    pu (Program.eval g program) := by
  induction program with
  | done u => exact hp
  | ask q rest ih => exact ih (g q) (hp.2 (g q))

lemma mapQueries_eval {Q Q' Reply U : Type*} {pq : Q → Prop} {pu : U → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program)
    (transform : Q → Q') (g : Q → Reply) (g' : Q' → Reply)
    (hg : ∀ q, pq q → g' (transform q) = g q) :
    Program.eval g' (mapQueries transform program) = Program.eval g program := by
  induction program with
  | done u => rfl
  | ask q rest ih =>
    simp only [mapQueries, Program.eval, hg q hp.1]
    exact ih (g q) (hp.2 (g q))

lemma mapQueries_cost {Q Q' Reply U : Type*} {pq : Q → Prop} {pu : U → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program)
    (transform : Q → Q') (g : Q → Reply) (g' : Q' → Reply)
    (hg : ∀ q, pq q → g' (transform q) = g q) :
    Program.cost g' (mapQueries transform program) = Program.cost g program := by
  induction program with
  | done u => rfl
  | ask q rest ih =>
    simp only [mapQueries, Program.cost, hg q hp.1, ih (g q) (hp.2 (g q))]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma snapshot_checked (C : Set E) (x : E) (hx : x ∈ C) (m : ℕ) (indices : Fin m → Fin n) :
    Checked (fun q : Fin n × E => q.2 ∈ C) (fun _ : Fin m → E => True) (snapshot x m indices) := by
  induction m with
  | zero => trivial
  | succ m ih =>
    refine ⟨hx, fun (reply : E) => ?_⟩
    exact checked_map (pv := fun _ : Fin (m + 1) → E => True)
      (ih _) (fun rest : Fin m → E => Fin.cons reply rest) (fun _ _ => trivial)

lemma innerPlan_checked {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (μ η : ℝ) (c : E) (cache : Fin n → E) (x : E) (hx : x ∈ C) (seed : List (Fin n)) :
    Checked (fun q : Fin n × E => q.2 ∈ C)
      (fun r : E × List E => r.1 ∈ C ∧ (∀ y ∈ r.2, y ∈ C) ∧ r.2.length = seed.length)
      (innerPlan C μ η c cache x seed) := by
  induction seed generalizing x with
  | nil => exact ⟨hx, by simp, rfl⟩
  | cons i tail ih =>
    refine ⟨hx, fun (reply : E) => ?_⟩
    let w := step C μ η c x (reply - cache i + cacheMean cache)
    have hw : w ∈ C := step_mem hne hco hcv _ _ _ _ _
    apply checked_map (ih w hw)
    intro r hr
    exact ⟨hr.1, by simpa only [List.mem_cons, forall_eq_or_imp] using ⟨hw, hr.2.1⟩,
      by simpa only [List.length_cons] using congrArg Nat.succ hr.2.2⟩

lemma epochPlan_checked {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (μ η : ℝ) (c z : E) (hz : z ∈ C) (seed : List (Fin n)) (hseed : seed.length ≠ 0) :
    Checked (fun q : Fin n × E => q.2 ∈ C) (fun x => x ∈ C) (epochPlan C μ η c z seed) := by
  apply checked_bind (snapshot_checked C z hz n id)
  intro cache _
  apply checked_map (innerPlan_checked hne hco hcv μ η c cache z hz seed)
  intro r hr
  have hh := list_average_mem hcv r.2 (by omega) hr.2.1
  simpa only [hr.2.2] using hh

lemma epochsPlan_checked {C : Set E} (hne : C.Nonempty) (hco : IsCompact C) (hcv : Convex ℝ C)
    (μ η : ℝ) (c : E) {m : ℕ} (hm : 0 < m) (s : ℕ) (z : E) (hz : z ∈ C)
    (seed : Fin s → Fin m → Fin n) :
    Checked (fun q : Fin n × E => q.2 ∈ C) (fun x => x ∈ C) (epochsPlan C μ η c s z seed) := by
  induction s generalizing z with
  | zero => exact hz
  | succ s ih =>
    apply checked_bind (epochPlan_checked hne hco hcv μ η c z hz (List.ofFn (seed 0)) (by simpa using hm.ne'))
    intro next hnext
    exact ih next hnext _

lemma solvePlan_checked [NeZero n] {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) (L μ : ℝ) (c : E) (hc : c ∈ C) (s : ℕ)
    (seed : Fin s → Fin (144 * n) → Fin n) :
    Checked (fun q : Fin n × E => q.2 ∈ C) (fun out : Certificate E => out.point ∈ C)
      (solvePlan C L μ c s seed) := by
  apply checked_bind (snapshot_checked C c hc n id)
  intro initialCache _
  apply checked_bind (epochsPlan_checked hne hco hcv μ (1 / (12 * L)) c
    (Nat.mul_pos (by decide : 0 < 144) (NeZero.pos n)) s _ (step_mem hne hco hcv _ _ _ _ _) seed)
  intro x hx
  apply checked_bind (snapshot_checked C x hx n id)
  intro currentCache _
  have hw := step_mem hne hco hcv μ (1 / L) c x (cacheMean currentCache)
  apply checked_map (snapshot_checked C _ hw n id)
  intro finalCache _
  exact hw

end LongTails.Proofs.FiniteSumNondualProxFeasibility
