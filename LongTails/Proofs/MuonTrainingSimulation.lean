import LongTails.Proofs.MuonSimulation
import LongTails.Proofs.SampledQueryPlan

namespace LongTails.Proofs.MuonProcess

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

lemma trajectory_shift {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    trajectory α η g ξ state call (t + 1) =
      trajectory α η g ξ (trainingStep α η state (g state.1 (ξ call))) (call + 1) t := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
    rw [trajectory, ih, trajectory]
    rw [show call + (t + 1) = call + 1 + t by omega]

lemma sampledEval_trainingPlan {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (T : ℕ)
    (x M : Space m n) (call : ℕ) :
    QueryPlan.sampledEval g ξ (trainingPlan α η T x M) call =
      fun i => (trajectory α η g ξ (x, M) call i.val).1 := by
  induction T generalizing x M call with
  | zero => ext i; exact Fin.elim0 i
  | succ T ih =>
    simp only [trainingPlan, QueryPlan.sampledEval, QueryPlan.sampledEval_map, ih]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cons_succ, Fin.val_succ, trajectory_shift, trainingStep,
      LongTails.Setups.FiniteVarianceSpectralSmooth.trainingStep]

end LongTails.Proofs.MuonProcess

namespace LongTails.Proofs.MuonSimulation

open OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

lemma sampledEval_training_resume {m n T b k q : ℕ} {Ω : Type*}
    (α η ρ : ℝ) (x0 : Space m n) (g : Space m n → Ω → Space m n)
    (ξ : ℕ → Ω) (seed : Fin (q + 1) → Fin (T + 1)) (extra call : ℕ) :
    QueryPlan.sampledEval g ξ
      (resumeMuonPlan α η ρ x0 (T + 1 + ((b * (k + 1)) * (q + 1) + extra))
        ((validatedMuon α η ρ T b k q x0).initial seed)) call =
    QueryPlan.sampledEval g ξ
      (resumeMuonPlan α η ρ x0 (((b * (k + 1)) * (q + 1) + extra))
        (validationStart (T := T) (b := b) (k := k) ρ (fun i =>
          (QueryPlan.sampledEval g ξ (trainingPlan α η (T + 1) x0 0) call) (seed i))))
      (call + (T + 1)) := by
  rw [MuonProcess.sampledEval_trainingPlan]
  let path := trajectory α η g ξ (x0, 0) call
  let points : Fin (T + 1) → Space m n := fun j => (path j.val).1
  let saved := fun t (j : Fin (T + 1)) => if j.val < t then points j else x0
  let state := fun t (ht : t < T + 1) =>
    ValidatedMuonState.training (b := b) (k := k) seed ⟨t, ht⟩
      (path t).1 (path t).2 (saved t)
  let A := validatedMuon α η ρ T b k q x0
  have hsave (t : ℕ) (ht : t < T + 1) :
      Function.update (saved t) ⟨t, ht⟩ (path t).1 = saved (t + 1) := by
    funext j
    by_cases hj : j = ⟨t, ht⟩
    · subst j
      simp [saved, points]
    · have hv : j.val ≠ t := fun h => hj (Fin.ext h)
      rw [Function.update_of_ne hj]
      dsimp only [saved]
      by_cases hlt : j.val < t
      · simp [hlt, show j.val < t + 1 by omega]
      · simp [hlt, show ¬ j.val < t + 1 by omega]
  have hfinal : saved (T + 1) = points := by
    funext j
    simp [saved, j.isLt]
  have hnext (t : ℕ) (ht : t < T + 1) (hn : t + 1 ≠ T + 1) :
      A.update (state t ht) (g (path t).1 (ξ (call + t))) =
        state (t + 1) (by omega) := by
    simp only [A, validatedMuon, validatedMuonDirect, state, hn, dite_false]
    rw [hsave]
    rfl
  have hlast (t : ℕ) (ht : t < T + 1) (he : t + 1 = T + 1) :
      A.update (state t ht) (g (path t).1 (ξ (call + t))) =
        validationStart (T := T) (b := b) (k := k) ρ (fun i => points (seed i)) := by
    simp only [A, validatedMuon, validatedMuonDirect, state, he, dite_true]
    rw [hsave, he, hfinal]
    rfl
  have hrun : ∀ r t (ht : t < T + 1), t + r = T + 1 →
      QueryPlan.sampledEval g ξ
        (resumeMuonPlan α η ρ x0 (r + ((b * (k + 1)) * (q + 1) + extra)) (state t ht))
        (call + t) =
      QueryPlan.sampledEval g ξ
        (resumeMuonPlan α η ρ x0 (((b * (k + 1)) * (q + 1) + extra))
          (validationStart (T := T) (b := b) (k := k) ρ (fun i => points (seed i))))
        (call + (T + 1)) := by
    intro r
    induction r with
    | zero => intro t ht he; omega
    | succ r ih =>
        intro t ht he
        rw [Nat.succ_add, resumeMuonPlan, QueryPlan.sampledEval]
        change QueryPlan.sampledEval g ξ
          (resumeMuonPlan α η ρ x0 (r + ((b * (k + 1)) * (q + 1) + extra))
            (A.update (state t ht) (g (path t).1 (ξ (call + t))))) (call + t + 1) = _
        by_cases hl : t + 1 = T + 1
        · have hr : r = 0 := by omega
          rw [hlast t ht hl, hr, Nat.zero_add]
          congr 1
          omega
        · rw [hnext t ht hl]
          simpa only [Nat.add_assoc] using ih (t + 1) (by omega) (by omega)
  simpa [state, saved, path, points, trajectory, validatedMuon, validatedMuonDirect] using
    hrun (T + 1) 0 (by omega) (by omega)

end LongTails.Proofs.MuonSimulation
