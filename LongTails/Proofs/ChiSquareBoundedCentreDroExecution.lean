import LongTails.Algorithms.ChiSquareBoundedCentreDro
import LongTails.Proofs.Execution

open MeasureTheory
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ComponentEnvelope (Program)
open LongTails.Setups.ChiSquareConstrainedDro

variable {E R U V : Type*}

inductive Depth : ℕ → Program E R U → Prop where
  | done (u : U) : Depth 0 (.done u)
  | ask {n : ℕ} (x : E) (next : R → Program E R U) (h : ∀ y, Depth n (next y)) :
      Depth (n+1) (.ask x next)

def interpret (response : ℕ → E → R) : Program E R U → ℕ → U
  | .done v, _ => v
  | .ask x next, t => interpret response (next (response t x)) (t+1)

lemma depth_bind {n m : ℕ} {s : Program E R U} (h : Depth n s) (f : U → Program E R V)
    (hf : ∀ u, Depth m (f u)) : Depth (n+m) (s.bind f) := by
  induction h with
  | done => simpa [Program.bind] using hf _
  | ask x next _ ih => rw [Nat.succ_add]; exact .ask _ _ ih

lemma interpret_bind (response : ℕ → E → R) {n : ℕ} {s : Program E R U} (h : Depth n s)
    (f : U → Program E R V) (t : ℕ) :
    interpret response (s.bind f) t = interpret response (f (interpret response s t)) (t+n) := by
  induction h generalizing t with
  | done => simp [interpret, Program.bind]
  | ask x next _ ih =>
    simpa [interpret, Program.bind, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (response t x) (t+1)

lemma depth_map {n : ℕ} {s : Program E R U} (h : Depth n s) (f : U → V) :
    Depth n (s.map f) := by simpa [Program.map] using depth_bind h (fun v => .done (f v)) (fun _ => .done _)

variable (q : Params)

lemma depth_collect {α : Type*} (jobs : ℕ → Plan q α) {m : ℕ} (h : ∀ i, Depth m (jobs i)) (n : ℕ) :
    Depth (n*m) (collect jobs n) := by
  induction n with
  | zero => rw [Nat.zero_mul]; exact .done _
  | succ n ih =>
    rw [Nat.succ_mul]; exact depth_bind ih _ fun _ => depth_map (h n) _

lemma depth_training (d : ℝ) (n : ℕ) (z : Triple q.E) (w : Candidate q.E) :
    Depth n (training q d n z w) := by
  induction n generalizing z w with
  | zero => exact .done _
  | succ n ih => exact .ask _ _ fun _ => ih _ _

lemma depth_score (w : Candidate q.E) (m n : ℕ) (acc : ℝ) : Depth n (score q w m n acc) := by
  induction n generalizing acc with
  | zero => exact .done _
  | succ n ih => exact .ask _ _ fun _ => ih _

lemma depth_match (r : ℕ) (x y : Candidate q.E) :
    Depth (batchSize q r + batchSize q r) (matchPair q r x y) :=
  depth_bind (depth_score q _ _ _ _) _ fun _ => depth_map (depth_score q _ _ _ _) _

noncomputable def tournamentCost (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => 2^(h+1)*batchSize q r + tournamentCost (r+1) h

lemma depth_tournament (r h : ℕ) (xs : ℕ → Candidate q.E) :
    Depth (tournamentCost q r h) (tournament q r h xs) := by
  induction h generalizing r xs with
  | zero => exact .done _
  | succ h ih =>
    unfold tournamentCost
    rw [show 2^(h+1)*batchSize q r = 2^h*(batchSize q r + batchSize q r) by ring]
    exact depth_bind (depth_collect q _ (fun _ => depth_match q _ _ _) _) _ fun _ => ih _ _

noncomputable def usedCalls :=
  if min q.B (q.G*q.R) ≤ q.ε then 0 else bracketCount q * trainingCount q + tournamentCost q 0 (rounds q)

lemma depth_plan : Depth (usedCalls q) (plan q) := by
  unfold usedCalls plan
  split
  · exact .done _
  · exact depth_bind (depth_collect q _ (fun i => depth_training q _ _ _ _) _) _
      fun _ => depth_tournament q _ _ _

lemma execution_eq (I : Instance q) (proj : q.E → q.E) (P : ProbabilityMeasure (ℕ → q.Ξ))
    (ξ : ℕ → q.Ξ) {K : ℕ} (hK : usedCalls q ≤ K) :
    let response := fun t x => (proj x, I.loss (proj x) (ξ t), I.sub (proj x) (ξ t))
    execute (sampleOracle I proj P) (algorithm q) (fun _ => K) () ξ = interpret response (plan q) 0 := by
  intro resp
  refine (execute_indexed_of_answer (sampleOracle I proj P) (algorithm q) K () ξ (fun t x => resp t x.2) (fun _ _ => rfl)).trans ?_
  let step := fun s : Plan q q.E × ℕ => (s.1.update (resp s.2 (s.1.query q.x0)), s.2+1)
  change ((step^[K] (plan q, 0)).1.output q.x0) = _
  suffices H : ∀ {n} {s : Plan q q.E}, Depth n s → ∀ t k, n ≤ k →
      ((step^[k] (s,t)).1.output q.x0) = interpret resp s t by
    exact H (depth_plan q) 0 K hK
  intro n s hs
  induction hs with
  | done u =>
    intro t k _
    induction k generalizing t with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply]; exact ih (t+1) (Nat.zero_le _)
  | ask x next _ ih =>
    intro t k hk
    cases k with
    | zero => omega
    | succ k => rw [Function.iterate_succ_apply]; exact ih (resp t x) (t+1) k (by omega)

end OracleTemplate.ChiSquareBoundedCentreDro
