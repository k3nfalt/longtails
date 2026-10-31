import LongTails.Proofs.HessianAdaptiveCubicInvariants
import LongTails.Proofs.Execution

namespace LongTails.Proofs.HessianAdaptiveCubicExecution

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants

lemma sampleStep_three {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω)
    (n : ℕ) (s : State p.d) (hphase : s.phase = 0) :
    (sampleStep p g H ξ)^[3] (s, 3 * n) = (round p g H ξ n s, 3 * (n + 1)) := by
  simp [Function.iterate_succ_apply, sampleStep, algorithm, update, hphase, LongTails.Algorithms.HessianAdaptiveCubic.round,
    modelState, center, Nat.mul_add, Nat.add_assoc]

lemma sampleStep_roundState {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) :
    (sampleStep p g H ξ)^[3 * n] (initial p, 0) = (roundState p g H ξ n, 3 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : 3 * (n + 1) = 3 + 3 * n := by omega
    rw [he, Function.iterate_add_apply, ih]
    simpa only [roundState, he] using
      sampleStep_three p g H ξ n _ (roundState_phase p g H ξ n)

lemma execute_roundState {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (n : ℕ) :
    OracleTemplate.execute
      { Seed := fun _ => Ω, law := P,
        answer := fun _ (_, hessian, x) ω => if hessian then (0, H x ω) else (g x ω, 0) }
      (algorithm p) (fun _ => 3 * n) () ξ = output (roundState p g H ξ n) := by
  calc
    _ = output ((sampleStep p g H ξ)^[3 * n] (initial p, 0)).1 := by
      exact OracleTemplate.execute_indexed_of_answer
        { Seed := fun _ => Ω, law := P,
          answer := fun _ (_, hessian, x) ω => if hessian then (0, H x ω) else (g x ω, 0) }
        (algorithm p) (3 * n) () ξ
        (fun k (_, hessian, x) => if hessian then (0, H x (ξ k)) else (g x (ξ k), 0))
        (by intros; rfl)
    _ = _ := by rw [sampleStep_roundState]

lemma roundState_congr {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (ξ ζ : ℕ → Ω) (hξ : ∀ k < 3 * n, ξ k = ζ k) :
    roundState p g H ξ n = roundState p g H ζ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : ∀ k < 3 * n, ξ k = ζ k := fun k hk => hξ k (by omega)
    have h0 := hξ (3 * n) (by omega)
    have h1 := hξ (3 * n + 1) (by omega)
    have h2 := hξ (3 * n + 2) (by omega)
    simp only [roundState, LongTails.Algorithms.HessianAdaptiveCubic.round, ih hp, h0, h1, h2]

lemma modelAt_congr {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (n : ℕ)
    (ξ ζ : ℕ → Ω) (hξ : ∀ k < 3 * n + 2, ξ k = ζ k) :
    modelAt p g H ξ n = modelAt p g H ζ n := by
  have hp := roundState_congr p g H n ξ ζ (fun k hk => hξ k (by omega))
  have h0 := hξ (3 * n) (by omega)
  have h1 := hξ (3 * n + 1) (by omega)
  simp only [modelAt, hp, h0, h1]

lemma roundState_succ_modelAt {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) :
    roundState p g H ξ (n + 1) =
      advance p (modelAt p g H ξ n) (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) := rfl

lemma modelAt_trial {Ω : Type*} (p : Public) (g : Point p.d → Ω → Point p.d)
    (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → Ω) (n : ℕ) :
    (modelAt p g H ξ n).trial = primal p (modelAt p g H ξ n) (modelAt p g H ξ n).modelHessian := rfl

end LongTails.Proofs.HessianAdaptiveCubicExecution
