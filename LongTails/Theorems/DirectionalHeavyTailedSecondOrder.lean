import LongTails.Setups.HeavyTailedHessianVector
import LongTails.Algorithms.HeavyTailedSospTuned
import LongTails.Proofs.HeavyTailedSospBudget

namespace OracleTemplate.DirectionalHeavyTailedSecondOrder

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned
open LongTails.Proofs.HeavyTailedSospBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ (64 * (p.p / (p.p - 1)) ^ 2) * ((1 + p.σg / p.ε) ^ (p.p / (p.p - 1)) + (1 + p.Δ * (p.L + Real.sqrt (p.ρ * p.ε)) / p.ε ^ 2) * (1 + (1 + p.σg / p.ε) ^ (1 / (p.p - 1)) * (p.σh / (p.L + Real.sqrt (p.ρ * p.ε)) + p.ρ * p.ε / (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2) + (p.σh / (p.L + Real.sqrt (p.ρ * p.ε)) + p.ρ * p.ε / (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2) ^ (p.p / (p.p - 1)) + Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) * Real.log (2 + (p.d : ℝ)) * ((p.L + Real.sqrt (p.ρ * p.ε)) / Real.sqrt (p.ρ * p.ε)) + Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε)) * (Real.log (2 + (p.d : ℝ))) ^ (p.p / (p.p - 1)) * (p.σh / Real.sqrt (p.ρ * p.ε)) ^ (p.p / (p.p - 1)) + (Real.log (2 + (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2 / (p.ρ * p.ε))) ^ 2 * (1 + (p.σh / Real.sqrt (p.ρ * p.ε)) ^ (p.p / (p.p - 1)))))⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedHessianVector.spec budget := by
  refine ⟨fun p => LongTails.Algorithms.HeavyTailedSosp.algorithm p (config p), ?_, ?_⟩
  · intro p hp f O hO
    have hb := publicEnvelope_bounds p hp
    have hbudget : budget p = fun _ => ⌈publicEnvelope p⌉₊ := by
      funext i
      simp only [budget, publicEnvelope,
        LongTails.Proofs.HeavyTailedSospSpectralCost.conjugate_sub_one p hp.2.2.2.2.2.1]
      rfl
    change spec.successful p f
      (fun w : (LongTails.Algorithms.HeavyTailedSosp.algorithm p (config p)).Seed × ((k : ℕ) → O.Seed k) => execute O (LongTails.Algorithms.HeavyTailedSosp.algorithm p (config p)) (budget p) w.1 w.2) _
    rw [hbudget]
    exact LongTails.Proofs.HeavyTailedSospConfigured.configured_execute_success p hp f O hO
      ⌈publicEnvelope p⌉₊ (Nat.one_le_ceil_iff.mpr hb.1) (hb.2.trans (Nat.le_ceil _))
  · intro p hp
    trivial

end OracleTemplate.DirectionalHeavyTailedSecondOrder
