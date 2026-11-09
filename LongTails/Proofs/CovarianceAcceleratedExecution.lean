import LongTails.Algorithms.CovarianceAccelerated
import LongTails.Proofs.ExecutionHistory

open MeasureTheory Convexity OracleTemplate
open LongTails.Algorithms.CovarianceAccelerated

namespace LongTails.Proofs.CovarianceAcceleratedExecution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  {n : ℕ} (c : Config E n)

lemma advance_clock (s : State c) (g : E) : (advance c s g).1 = s.1 + 1 := by
  unfold advance
  split <;> rfl

lemma trajectory_clock {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (N : ℕ) :
    (trajectory c g ξ N).1 = N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [trajectory, advance_clock, ih]

lemma indexedState_trajectory {Ω : Type} [MeasurableSpace Ω] (g : E → Ω → E)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (N : ℕ) :
    let O : Oracle E E :=
      { Seed := fun _ => Ω
        law := P
        answer := fun _ (_, x) ω => g x ω }
    (executeIndexedState O (method c) () ξ N).1 = trajectory c g ξ N := by
  let O : Oracle E E :=
    { Seed := fun _ => Ω
      law := P
      answer := fun _ (_, x) ω => g x ω }
  change (executeIndexedState O (method c) () ξ N).1 = trajectory c g ξ N
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [executeIndexedState, trajectory]
    change advance c (executeIndexedState O (method c) () ξ N).1
      (g (query c (executeIndexedState O (method c) () ξ N).1)
        (ξ (executeIndexedState O (method c) () ξ N).2.length)) = _
    erw [executeIndexedState_length, ih]

lemma execute_output {Ω : Type} [MeasurableSpace Ω] (g : E → Ω → E)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (N : ℕ) :
    let O : Oracle E E :=
      { Seed := fun _ => Ω
        law := P
        answer := fun _ (_, x) ω => g x ω }
    execute O (method c) (fun _ => N) () ξ = output c g ξ N := by
  let O : Oracle E E :=
    { Seed := fun _ => Ω
      law := P
      answer := fun _ (_, x) ω => g x ω }
  change (executeWithTrace O (method c) (fun _ => N) () ξ).1 = output c g ξ N
  erw [executeWithTrace_eq_executeIndexedState]
  exact congrArg (fun s : State c => s.2.1) (indexedState_trajectory c g P ξ N)

lemma execute_calls {Ω : Type} [MeasurableSpace Ω] (g : E → Ω → E)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (N : ℕ) :
    let O : Oracle E E :=
      { Seed := fun _ => Ω
        law := P
        answer := fun _ (_, x) ω => g x ω }
    (executeWithTrace O (method c) (fun _ => N) () ξ).2.length = N := by
  dsimp only
  erw [executeWithTrace_eq_executeIndexedState]
  exact executeIndexedState_length _ _ _ _ _

lemma advance_history (s : State c) (g : E) :
    (advance c s g).2.2.2 = push s.2.2.2 g := by
  unfold advance
  split <;> rfl

lemma warmup_query {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) {N : ℕ}
    (hN : N < c.window + 1) : query c (trajectory c g ξ N) = c.x0 := by
  simp [query, trajectory_clock, hN]

lemma warmup_state {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) {N : ℕ}
    (hN : N ≤ c.window + 1) :
    (trajectory c g ξ N).2.1 = c.x0 ∧
      (trajectory c g ξ N).2.2.1 = StdSimplex.single c.initialIndex := by
  induction N with
  | zero => exact ⟨rfl, rfl⟩
  | succ N ih =>
    have hlt : N < c.window + 1 := by omega
    have hprev := ih (by omega)
    simpa [trajectory, advance, trajectory_clock, hlt] using hprev

lemma trajectory_history {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (N : ℕ)
    (j : Fin (c.window + 1)) :
    (trajectory c g ξ N).2.2.2 j =
      if j.val < N then g (query c (trajectory c g ξ (N - 1 - j.val))) (ξ (N - 1 - j.val))
      else 0 := by
  induction N generalizing j with
  | zero => simp [trajectory, initial]
  | succ N ih =>
    rw [trajectory, advance_history]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [push]
    · rw [show push (trajectory c g ξ N).2.2.2
        (g (query c (trajectory c g ξ N)) (ξ N)) j.succ =
        (trajectory c g ξ N).2.2.2 j.castSucc by rfl, ih]
      have ht : N + 1 - 1 - (j.val + 1) = N - 1 - j.val := by omega
      have hb : j.val + 1 < N + 1 ↔ j.val < N := by omega
      simp only [Fin.val_castSucc, Fin.val_succ, ht, hb]

lemma history_after_warmup {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) {N : ℕ}
    (hN : c.window + 1 ≤ N) (j : Fin (c.window + 1)) :
    (trajectory c g ξ N).2.2.2 j =
      g (query c (trajectory c g ξ (N - 1 - j.val))) (ξ (N - 1 - j.val)) := by
  rw [trajectory_history]
  exact ite_eq_left (lt_of_lt_of_le j.isLt hN)

end LongTails.Proofs.CovarianceAcceleratedExecution
