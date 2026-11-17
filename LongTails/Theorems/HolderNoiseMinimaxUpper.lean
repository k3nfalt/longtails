import LongTails.Setups.HolderNoiseNonconvex
import LongTails.Proofs.HolderNoiseExecution
import LongTails.Proofs.HolderNoiseCount

namespace OracleTemplate.HolderNoiseMinimaxUpper

open MeasureTheory DyadicHolder HolderNoise LongTails.Setups.HolderNoiseNonconvex
open LongTails.Proofs.HolderNoiseAccuracy

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈min (600 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.L * q.Δ * q.σ ^ 2 / q.ε ^ 4)) (3200 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Δ / q.ε ^ 3 * max (q.M * (q.L / q.ε) ^ (1 - 2 * q.ν)) (q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν))))⌉₊

theorem result : Convergence LongTails.Setups.HolderNoiseNonconvex.spec budget := by
  refine ⟨fun q => outputAlgorithm
    (if q.ν ≤ 1 / 2 then tcfg q.L (q.M * tEta q.L q.ε ^ (2 * q.ν - 1)) (1 / 2) q.σ q.Δ q.ε
      else tcfg q.L q.M q.ν q.σ q.Δ q.ε)
    (anchorConfig q.L q.σ q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hL, hM, hν, hν1, hσ, hΔ, hε⟩ := hq
  let a := if q.ν ≤ 1 / 2 then
      tcfg q.L (q.M * tEta q.L q.ε ^ (2 * q.ν - 1)) (1 / 2) q.σ q.Δ q.ε
    else tcfg q.L q.M q.ν q.σ q.Δ q.ε
  let cfg := selectConfig a (anchorConfig q.L q.σ q.Δ q.ε)
  have hb : off cfg (cfg.K + 1) ≤ budget q 0 := by
    have hc := combined_calls_le hL hM hν hν1 hσ hΔ hε
    rw [variation_cost_factor hΔ hε.le] at hc
    have hceil := hc.trans (Nat.le_ceil _)
    rw [calls_eq_off] at hceil
    exact_mod_cast hceil
  exact execution_successful q ⟨hL, hM, hν, hν1, hσ, hΔ, hε⟩ cfg (budget q 0)
    (selected_batches q.L q.M q.ν q.σ q.Δ q.ε) hb f
    (fun g p H hgap => selected_accuracy H hν1 hσ hΔ hε q.x0 hgap) O hadm

end OracleTemplate.HolderNoiseMinimaxUpper
