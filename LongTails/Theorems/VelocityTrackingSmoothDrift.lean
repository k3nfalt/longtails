import LongTails.Setups.SmoothDriftStronglyConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.VelocityTrackingConvergence

namespace OracleTemplate.VelocityTracking.SmoothDrift

open LongTails.Setups.SmoothDriftStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈16 * (2 * p.L / p.μ + 99 * p.σ ^ 2 / (p.μ ^ 2 * p.ε)) * Real.log (1 + (15 * p.R ^ 2 + 45 * p.V ^ 2 * (2 * p.L / p.μ + 99 * p.σ ^ 2 / (p.μ ^ 2 * p.ε)) ^ 2) / p.ε)⌉₊ + p.H + 1

theorem result : Convergence LongTails.Setups.SmoothDriftStronglyConvex.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => velocityTrackingSgd (q.μ * q.ε / (99 * q.σ ^ 2 + 2 * q.L * q.μ * q.ε))
    (q.μ * q.ε / (99 * q.σ ^ 2 + 2 * q.L * q.μ * q.ε) *
      (q.μ * q.ε / (99 * q.σ ^ 2 + 2 * q.L * q.μ * q.ε) * q.μ) / 4) q.x0, ?_, ?_⟩
  · intro p hp N hN f O h
    refine tuned_success p hp N ?_ f O h
    have hc := Nat.le_ceil (16 * (2 * p.L / p.μ + 99 * p.σ ^ 2 / (p.μ ^ 2 * p.ε)) *
      Real.log (1 + (15 * p.R ^ 2 + 45 * p.V ^ 2 *
        (2 * p.L / p.μ + 99 * p.σ ^ 2 / (p.μ ^ 2 * p.ε)) ^ 2) / p.ε))
    have hN' : ((budget p 0 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    simp only [budget] at hN'
    push_cast at hN'
    have hH : (0 : ℝ) ≤ p.H := Nat.cast_nonneg _
    linarith
  · intro _ _
    exact ⟨fun state => state.1, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end OracleTemplate.VelocityTracking.SmoothDrift
