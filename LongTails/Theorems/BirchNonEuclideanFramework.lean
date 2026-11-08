import LongTails.Setups.BirchNonEuclidean
import LongTails.Proofs.BirchNonEuclideanTuning
import LongTails.Proofs.BirchNonEuclideanSharedCertificate
import LongTails.Proofs.BirchNonEuclideanPhysicalBudget
import LongTails.Proofs.BirchNonEuclideanRennalaSuccess

namespace LongTails.Theorems.BirchNonEuclideanFramework

open OracleTemplate
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFramework
open LongTails.Proofs.BirchNonEuclideanTuning

noncomputable def budget : (let S := LongTails.Setups.BirchNonEuclidean.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.callCount (1 + ⌈48 * p.L * p.Δ * (1 + p.profile.driftConstant + p.profile.driftLinear * (p.profile.minimumBatch + ⌈64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε + 8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε)⌉₊)) / p.ε⌉₊) (p.profile.minimumBatch + ⌈64 * p.κ * p.σ ^ 2 * p.profile.noiseLinear / p.ε + 8 * Real.sqrt (p.κ * p.σ ^ 2 * p.profile.noiseQuadratic / p.ε)⌉₊)

theorem result : Convergence LongTails.Setups.BirchNonEuclidean.spec budget := by
  refine ⟨algorithm, ?_, algorithm_allowed⟩
  intro p hp I O hI
  rcases hI with ⟨hf, Ω, m, horacle⟩
  let := m
  rcases horacle with ⟨μ, P, g, hiid, hg, rfl⟩
  obtain ⟨R, hRpos, hRbound⟩ :=
    LongTails.Proofs.BirchLmoExistence.exists_norm_le_seminorm p.N hp.1 hp.2.1
  have hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R := fun v hv =>
    (hRbound v).trans (by nlinarith)
  obtain ⟨w⟩ := hp.2.2.2.2.2.2.2.1
  obtain ⟨_, hcalls, ⟨c⟩⟩ := program_certificate p hp
  have hbudget : budget p = fun _ => (program p).oracleCalls := by
    funext i
    simpa only [budget, horizon, batchSize, Nat.cast_add] using hcalls.symm
  rw [hbudget]
  exact LongTails.Proofs.BirchNonEuclideanCertificate.certificate_execute_success
    p (program p) (chosenLMO p) c I hf μ P hiid g hg w hR hRpos.le hp.1
    (chosenLMO_valid p hp) hp.2.2.1.le (step_positive p hp) (drift_nonneg p hp)
    (step_conditions p hp).1 (step_conditions p hp).2 (accuracy_bound p hp)

end LongTails.Theorems.BirchNonEuclideanFramework
