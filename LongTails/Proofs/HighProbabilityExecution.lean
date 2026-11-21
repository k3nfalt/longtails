import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Proofs.SampledQueryPlan
import LongTails.Proofs.HighProbabilityAdapted

namespace LongTails.Proofs.HighProbabilityExecution

open OracleTemplate QueryPlan LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Algorithms.StochasticEnvelopeProgram LongTails.Proofs.HighProbabilityAdapted

section Generic

variable {Q R U V Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)

lemma sampledEval_castPlan {k l : ℕ} (h : k = l) (plan : QueryPlan Q R U k) (call : ℕ) :
    sampledEval g ξ (castPlan h plan) call = sampledEval g ξ plan call := by
  subst l
  rfl

lemma sampledEval_collectPlans {c : ℕ} (n : ℕ) (plans : Fin n → QueryPlan Q R U c) (call : ℕ) :
    sampledEval g ξ (collectPlans n plans) call =
      fun i => sampledEval g ξ (plans i) (call + c * i.val) := by
  induction n generalizing call with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [collectPlans, sampledEval_bind, sampledEval_map, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cases_succ, Fin.val_succ]
      congr 1
      ring

def stepIter {S : Type*} {c : ℕ} (body : S → QueryPlan Q R S c) : ℕ → S → ℕ → S
  | 0, s, _ => s
  | n + 1, s, call => stepIter body n (sampledEval g ξ (body s) call) (call + c)

lemma sampledEval_stepRepeat {S : Type*} {c : ℕ} (body : S → QueryPlan Q R S c) (n : ℕ)
    (s : S) (call : ℕ) :
    sampledEval g ξ (stepRepeat n body s) call = stepIter g ξ body n s call := by
  induction n generalizing s call with
  | zero => rfl
  | succ n ih =>
    simp only [stepRepeat, sampledEval_bind, stepIter]
    exact ih _ _

lemma stepIter_succ {S : Type*} {c : ℕ} (body : S → QueryPlan Q R S c) (n : ℕ) (s : S)
    (call : ℕ) :
    stepIter g ξ body (n + 1) s call =
      sampledEval g ξ (body (stepIter g ξ body n s call)) (call + c * n) := by
  induction n generalizing s call with
  | zero => simp [stepIter]
  | succ n ih =>
    rw [stepIter, ih, stepIter]
    congr 1
    ring

end Generic

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma sampledEval_samplePlan (g : E → Ω → E) (ξ : ℕ → Ω) (x : E) (n call : ℕ) :
    sampledEval g ξ (samplePlan x n) call = fun i => g x (ξ (call + i.val)) := by
  unfold samplePlan
  rw [sampledEval_castPlan, sampledEval_collectPlans]
  funext i
  simp [sampledEval]

noncomputable def stepMap (B η : ℝ) (K mp mc : ℕ) (g : E → Ω → E) (x : E)
    (z : Fin (mp + mc) → Ω) : E :=
  normalizedStep η x (clipEstimate B K mp mc (fun i => g x (z i)))

def blocks (n : ℕ) (ξ : ℕ → Ω) : ℕ → Fin n → Ω := fun t i => ξ (t * n + i.val)

lemma phaseOne_eval (B η : ℝ) (K mp mc T : ℕ) (x0 : E) (g : E → Ω → E) (ξ : ℕ → Ω) :
    (sampledEval g ξ (phaseOne B η K mp mc T x0) 0).point =
        traj (stepMap B η K mp mc g) x0 (blocks (mp + mc) ξ) T ∧
      (sampledEval g ξ (phaseOne B η K mp mc T x0) 0).time = T ∧
      ∀ t < T, (sampledEval g ξ (phaseOne B η K mp mc T x0) 0).path t =
        traj (stepMap B η K mp mc g) x0 (blocks (mp + mc) ξ) t := by
  unfold phaseOne
  rw [sampledEval_stepRepeat]
  set body := fun s : Trajectory E =>
    (samplePlan s.point (mp + mc)).map (trajectoryStep B η K mp mc s)
  have hbody (s : Trajectory E) (call : ℕ) : sampledEval g ξ (body s) call =
      trajectoryStep B η K mp mc s (fun i => g s.point (ξ (call + i.val))) := by
    simp only [body, sampledEval_map, sampledEval_samplePlan]
  induction T with
  | zero =>
    refine ⟨rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | succ T ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [stepIter_succ, hbody]
    refine ⟨?_, ?_, ?_⟩
    · have hidx : ∀ i : Fin (mp + mc), 0 + (mp + mc) * T + i.val = T * (mp + mc) + i.val := by
        intro i; ring
      simp only [trajectoryStep, traj, h1, stepMap, blocks, hidx]
    · simp only [trajectoryStep, h2]
    · intro t ht
      simp only [trajectoryStep]
      rw [h2]
      by_cases htT : t = T
      · subst htT
        rw [Function.update_self]
        exact h1
      · rw [Function.update_of_ne htT]
        exact h3 t (by omega)

end LongTails.Proofs.HighProbabilityExecution
