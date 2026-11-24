import LongTails.Setups.MeanSquaredSmoothPL
import LongTails.Proofs.StagewiseSarahExecution

namespace OracleTemplate.MeanSquaredSmoothPLUpperBound

open LongTails.Setups.MeanSquaredSmoothPL OracleTemplate.StagewiseSarah

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let κ := q.L / q.μ
  let κbar := q.Lbar / q.μ
  let s := q.σ / √(q.μ * q.ε)
  ⌈640 * (κ * Real.logb 2 (1 + q.Δ / q.ε) + s ^ 2 + min (κ * s ^ 2) (κbar * s))⌉₊

theorem result : Convergence LongTails.Setups.MeanSquaredSmoothPL.spec budget := by
  refine ⟨fun q => sarah (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  have hv := hq
  obtain ⟨hμ, hL, hLbar, hσ, hΔ, hε⟩ := hv
  have hcost : cost (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) ≤ budget q 0 := by
    have h := (cost_schedule_le hμ hL hLbar hσ hΔ hε).trans (Nat.le_ceil _)
    exact Nat.cast_le.mp h
  exact execution_successful q hq (budget q 0) hcost f O hadm

end OracleTemplate.MeanSquaredSmoothPLUpperBound
