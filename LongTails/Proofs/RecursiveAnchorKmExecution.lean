import LongTails.Algorithms.RecursiveAnchorKm
import LongTails.Proofs.RecursiveAnchorKmStochastic
import LongTails.Proofs.SgdExecution

namespace OracleTemplate.RecursiveAnchorKm

open OracleTemplate.StochasticGradient (advance execute_advance)

lemma advance_add {State : Type*} (step : ℕ → State → State) :
    ∀ a b call s, advance step (a + b) call s = advance step b (call + a) (advance step a call s) := by
  intro a
  induction a with
  | zero => intro b call s; simp [advance]
  | succ a ih =>
    intro b call s
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [advance]
    rw [ih, show call + 1 + a = call + (a + 1) by omega]

lemma advance_succ {State : Type*} (step : ℕ → State → State) (a call : ℕ) (s : State) :
    advance step (a + 1) call s = step (call + a) (advance step a call s) := by
  rw [advance_add]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ξ : Type*}

section

variable (S : ℕ) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (G : Ξ → E → E) (ξ : ℕ → Ξ)

lemma advance_inner {u : ℕ} (hu : u ≤ S) (y A : E) :
    ∀ k, k < N u → advance (fun k (s : ℕ × ℕ × E × E) =>
        anchorKmUpdate S lam Λ α N s (G (ξ k) s.2.2.1)) k (start N u) (u, 0, y, A) =
      (u, k, kmRun G (α u) (α u / (1 + Λ u)) A (start N u) ξ y k, A) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [advance_succ, ih (by omega)]
    have h1 : ¬ S < u := by omega
    simp only [anchorKmUpdate, h1, ite_false, hk, ite_true, kmRun]

lemma advance_stage {u : ℕ} (hu : u ≤ S) (hN : 0 < N u) (d : E × E) :
    advance (fun k (s : ℕ × ℕ × E × E) =>
        anchorKmUpdate S lam Λ α N s (G (ξ k) s.2.2.1)) (N u) (start N u) (u, 0, d.1, d.2) =
      (u + 1, 0, (nextStage G lam Λ α N u ξ d).1, (nextStage G lam Λ α N u ξ d).2) := by
  obtain ⟨n, hn⟩ : ∃ n, N u = n + 1 := ⟨N u - 1, by omega⟩
  rw [hn, advance_succ, advance_inner S lam Λ α N G ξ hu d.1 d.2 n (by omega)]
  have h1 : ¬ S < u := by omega
  simp only [anchorKmUpdate, h1, ite_false, nextStage, hn, kmRun, lt_self_iff_false]

lemma advance_stages (x0 : E) (hN : ∀ u, u ≤ S → 0 < N u) :
    ∀ u, u ≤ S + 1 → advance (fun k (s : ℕ × ℕ × E × E) =>
        anchorKmUpdate S lam Λ α N s (G (ξ k) s.2.2.1)) (start N u) 0 (0, 0, x0, lam 0 • x0) =
      (u, 0, (stage G lam Λ α N x0 ξ u).1, (stage G lam Λ α N x0 ξ u).2) := by
  intro u
  induction u with
  | zero =>
    intro _
    simp only [start, Finset.range_zero, Finset.sum_empty]
    rfl
  | succ u ih =>
    intro hu
    rw [start_succ, advance_add, ih (by omega), Nat.zero_add,
      advance_stage S lam Λ α N G ξ (by omega) (hN u (by omega))]
    rfl

lemma advance_frozen (s : ℕ × ℕ × E × E) (hs : S < s.1) :
    ∀ m call, advance (fun k (s : ℕ × ℕ × E × E) =>
        anchorKmUpdate S lam Λ α N s (G (ξ k) s.2.2.1)) m call s = s := by
  intro m
  induction m with
  | zero => intro call; rfl
  | succ m ih =>
    intro call
    simp only [advance]
    have : anchorKmUpdate S lam Λ α N s (G (ξ call) s.2.2.1) = s := by
      simp only [anchorKmUpdate, hs, ite_true]
    rw [this]
    exact ih (call + 1)

end

lemma execute_recursiveAnchorKm {Ω : Type} [MeasurableSpace Ω] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (law : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (G : Ω → F → F)
    (S : ℕ) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 : F) (hN : ∀ u, u ≤ S → 0 < N u) (B : ℕ)
    (hB : start N (S + 1) ≤ B) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => G ω x }
      (recursiveAnchorKm S lam Λ α N x0) (fun _ => B) () ξ =
      (stage G lam Λ α N x0 ξ (S + 1)).1 := by
  refine (execute_advance law (fun x ω => G ω x) (recursiveAnchorKm S lam Λ α N x0) B () ξ).trans ?_
  obtain ⟨m, hm⟩ : ∃ m, B = start N (S + 1) + m := ⟨B - start N (S + 1), by omega⟩
  change (advance (fun k (s : ℕ × ℕ × F × F) => anchorKmUpdate S lam Λ α N s (G (ξ k) s.2.2.1))
    B 0 (0, 0, x0, lam 0 • x0)).2.2.1 = _
  rw [hm, advance_add, advance_stages S lam Λ α N G ξ x0 hN (S + 1) le_rfl,
    advance_frozen S lam Λ α N G ξ _ (by simp)]

end OracleTemplate.RecursiveAnchorKm
