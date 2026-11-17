import LongTails.Setups.HolderNoiseNonconvexLower
import LongTails.TemplateLowerBound
import LongTails.Proofs.HolderNoiseLowerBound

namespace OracleTemplate.HolderNoiseMinimaxLowerBound

open LongTails.Setups.HolderNoiseNonconvexLower

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌊((q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + min (q.L * q.Δ * q.σ ^ 2 / q.ε ^ 4) (q.Δ / q.ε ^ 3 * max (q.M * (q.L / q.ε) ^ (1 - 2 * q.ν)) (q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν)))) / (2 : ℝ) ^ 80⌋₊

theorem result : NonConvergence LongTails.Setups.HolderNoiseNonconvexLower.spec budget := by
  intro q hq A _ b hb
  have hv := hq.1
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  rcases hv with ⟨hL, hM, _, _, hσ, hΔ, hε⟩
  have hn : (b 0 : ℝ) ≤ (budget q 0 : ℝ) := Nat.cast_le.mpr (hb 0)
  change (b 0 : ℝ) ≤ (⌊((q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 +
    min (q.L * q.Δ * q.σ ^ 2 / q.ε ^ 4)
      (q.Δ / q.ε ^ 3 * max (q.M * (q.L / q.ε) ^ (1 - 2 * q.ν))
        (q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν)))) / (2 : ℝ) ^ 80⌋₊ : ℝ) at hn
  have hr := hn.trans (Nat.floor_le (by positivity))
  rw [mul_comm q.L q.Δ] at hr
  have hbudget : b = fun _ => b 0 := funext fun i => congrArg b (Fin.eq_zero i)
  rw [hbudget]
  apply LongTails.Proofs.HolderNoiseLowerBound.failure_at q hq A (b 0)
  convert hr using 1; ring

end OracleTemplate.HolderNoiseMinimaxLowerBound
