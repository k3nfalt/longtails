import LongTails.Proofs.RelativeHessianScaling
import LongTails.Proofs.Execution

namespace LongTails.Proofs.RelativeHessianInstance

open OracleTemplate RelativeHessianScaling RelativeHessianSimulation RelativeHessianOracle
open LongTails.Setups.PointwiseHessianStationarity (Params Point broadSpec)

noncomputable def oracle (a β : ℝ) {d m : ℕ} (π : Fin (m + 1) ↪ Fin d) :
    Oracle (EuclideanSpace ℝ (Fin d)) (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d))) where
  answer _ q _ := scaleReply a β (jet (RelativeHessianLocalized.value (axes π)) (β • q.2))

lemma admissible (p : Params) {a β : ℝ} {m : ℕ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (h₀ : 0 ≤ p.L₀) (h₁ : 0 ≤ p.L₁) (hε : 0 < p.ε)
    (habs : 2 ^ 56 * a * β ^ 3 ≤ p.L₀ + p.L₁ * p.ε)
    (hrel : 2 ^ 56 * β ^ 2 * p.ε ≤ p.L₀ + p.L₁ * p.ε)
    (hgap : a * (4 * (m + 1 : ℕ)) ≤ p.Δ) (hG : a * β ≤ p.G)
    (π : Fin (m + 1) ↪ Fin p.d) : broadSpec.admissible p (scaled a β π) (oracle a β π) := by
  refine ⟨scaled_smooth a β π, growth ha hβ h₀ h₁ hε habs hrel π, ?_, ?_, ?_⟩
  · intro x
    exact (RelativeHessianScaling.gap ha π x).trans hgap
  · rw [RelativeHessianScaling.initial_gradient ha hβ]
    exact hG
  · intro history seed x
    exact (jet_scale a β π x).symm

lemma actual_iterate {d m : ℕ} {S : Type*} (π : Fin (m + 1) ↪ Fin d)
    (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)) → S)
    (initial : S) (T : ℕ) :
    actual π query update initial T =
      (fun state => update state (jet (RelativeHessianLocalized.value (axes π)) (query state)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih => rw [actual, ih, Function.iterate_succ_apply']

noncomputable def normalizedQuery {d : ℕ} (β : ℝ)
    (A : Algorithm (EuclideanSpace ℝ (Fin d)) (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin d))) (state : A.State) : EuclideanSpace ℝ (Fin d) := β • (A.query state).2

noncomputable def normalizedUpdate {d : ℕ} (a β : ℝ)
    (A : Algorithm (EuclideanSpace ℝ (Fin d)) (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin d))) (state : A.State) (v : RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d))) : A.State :=
  A.update state (scaleReply a β v)

lemma execute_normalized {d m : ℕ} (a β : ℝ) (π : Fin (m + 1) ↪ Fin d)
    (A : Algorithm (EuclideanSpace ℝ (Fin d)) (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin d))) (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (oracle a β π) A (fun _ => T) seed ξ =
      A.output (actual π (normalizedQuery β A) (normalizedUpdate a β A) (A.initial seed) T) := by
  have hξ : ξ = fun _ => () := by funext t; exact Subsingleton.elim _ _
  subst ξ
  rw [actual_iterate]
  exact execute_iterate (fun x : EuclideanSpace ℝ (Fin d) =>
    scaleReply a β (jet (RelativeHessianLocalized.value (axes π)) (β • x))) A T seed

lemma execution_gradient {d m : ℕ} {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (π : Fin (m + 1) ↪ Fin d)
    (A : Algorithm (EuclideanSpace ℝ (Fin d)) (RelativeHessianOracle.Reply (EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin d))) (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    ‖gradient (scaled a β π) (execute (oracle a β π) A (fun _ => T) seed ξ)‖ =
      (a * β) * ‖gradient (RelativeHessianLocalized.value (axes π))
        (β • A.output (actual π (normalizedQuery β A) (normalizedUpdate a β A) (A.initial seed) T))‖ := by
  rw [execute_normalized, RelativeHessianScaling.gradient_norm ha hβ]

end LongTails.Proofs.RelativeHessianInstance
