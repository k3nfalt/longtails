import LongTails.Proofs.RelativeQuasarConvergence
import LongTails.Setups.HighDimensionalStrongQuasar

namespace LongTails.Proofs.StrongQuasarChainUpper

open LongTails.Setups.HighDimensionalStrongQuasar

lemma valid_relative {p : Params} (hp : spec.valid p) :
    LongTails.Setups.RelativeGradientStrongQuasar.spec.valid p.toRelative := by
  obtain ⟨hL, hμ, hγ, hγ1, hε, -, -, h8, -⟩ := hp
  have h0 : 0 < 1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε := by
    have : 0 < Real.sqrt (p.L / p.μ) := Real.sqrt_pos.mpr (by positivity)
    positivity
  exact ⟨hL, hμ, hγ, by linarith, le_refl 0, by norm_num, by linarith, hε⟩

lemma calls_eq {p : Params} (hp : spec.valid p) :
    OracleTemplate.RelativeQuasar.calls p.toRelative =
      ⌈32 * Real.sqrt (p.L / p.μ) / p.γ⌉₊ * Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ := by
  obtain ⟨hL, hμ, hγ, -, hε, -, -, h8, -⟩ := hp
  have hΔ : 0 < p.Δ := by
    have : 0 < 1000 * p.γ * Real.sqrt (p.L / p.μ) * p.ε := by positivity
    linarith
  have hc : OracleTemplate.RelativeQuasar.calls p.toRelative =
      max 1 ⌈32 * Real.sqrt (p.L / (p.μ * (1 - 0))) / p.γ +
        128 * 0 ^ 2 * p.L / (p.γ ^ 2 * p.μ * (1 - 0))⌉₊ *
      max 1 (Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊) := rfl
  have h0 : (128 : ℝ) * 0 ^ 2 * p.L / (p.γ ^ 2 * p.μ * (1 - 0)) = 0 := by ring
  have h0' : p.μ * (1 - 0) = p.μ := by ring
  rw [hc, h0, h0', add_zero]
  have h1 : 1 ≤ ⌈32 * Real.sqrt (p.L / p.μ) / p.γ⌉₊ := by
    apply Nat.one_le_iff_ne_zero.mpr
    rw [Ne, Nat.ceil_eq_zero, not_le]
    positivity
  have h2 : 1 ≤ Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ := by
    have : ((1 : ℕ) : ℝ) < 1 + 2 * p.Δ / (p.γ * p.ε) := by
      have : 0 < 2 * p.Δ / (p.γ * p.ε) := by positivity
      rw [Nat.cast_one]
      linarith
    exact Nat.clog_pos (by norm_num) (Nat.lt_ceil.mpr this)
  rw [max_eq_right h1, max_eq_right h2]

end LongTails.Proofs.StrongQuasarChainUpper
