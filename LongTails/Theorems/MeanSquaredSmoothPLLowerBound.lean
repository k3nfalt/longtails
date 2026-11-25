import LongTails.Setups.HighDimensionalMeanSquaredSmoothPL
import LongTails.Proofs.MeanSquaredPLLowerBound

namespace OracleTemplate.MeanSquaredSmoothPLLowerBound

open LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let κ := q.L / q.μ
  let κbar := q.Lbar / q.μ
  let s := q.σ / √(q.μ * q.ε)
  ⌊(κ + s ^ 2 + min (κ * s ^ 2) (κbar * s)) / 2 ^ 200⌋₊

theorem result :
    NonConvergence LongTails.Setups.HighDimensionalMeanSquaredSmoothPL.spec budget := by
  intro q hq A _ b hb
  have hv := hq.1
  change 0 < q.μ ∧ q.μ ≤ q.L ∧ q.L ≤ q.Lbar ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  obtain ⟨hμ, hL, hLbar, hσ, -, -⟩ := hv
  have hn : (b 0 : ℝ) ≤ (budget q 0 : ℝ) := Nat.cast_le.mpr (hb 0)
  change (b 0 : ℝ) ≤ (⌊(q.L / q.μ + (q.σ / √(q.μ * q.ε)) ^ 2 +
    min (q.L / q.μ * (q.σ / √(q.μ * q.ε)) ^ 2) (q.Lbar / q.μ * (q.σ / √(q.μ * q.ε)))) /
      2 ^ 200⌋₊ : ℝ) at hn
  have hL0 : 0 ≤ q.L := hμ.le.trans hL
  have hLb0 : 0 ≤ q.Lbar := hL0.trans hLbar
  have hs0 : 0 ≤ q.σ / √(q.μ * q.ε) := div_nonneg hσ (Real.sqrt_nonneg _)
  have hmin0 : 0 ≤ min (q.L / q.μ * (q.σ / √(q.μ * q.ε)) ^ 2)
      (q.Lbar / q.μ * (q.σ / √(q.μ * q.ε))) :=
    le_min (mul_nonneg (div_nonneg hL0 hμ.le) (sq_nonneg _))
      (mul_nonneg (div_nonneg hLb0 hμ.le) hs0)
  have hκ0 : 0 ≤ q.L / q.μ := div_nonneg hL0 hμ.le
  have hr := hn.trans (Nat.floor_le
    (div_nonneg (add_nonneg (add_nonneg hκ0 (sq_nonneg _)) hmin0) (by positivity)))
  have hbudget : b = fun _ => b 0 := funext fun i => congrArg b (Fin.eq_zero i)
  rw [hbudget]
  exact LongTails.Proofs.MeanSquaredPLLowerBound.failure_at q hq A (b 0) hr

end OracleTemplate.MeanSquaredSmoothPLLowerBound
