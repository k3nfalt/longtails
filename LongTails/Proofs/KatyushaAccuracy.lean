import LongTails.Proofs.KatyushaTuning
import Mathlib.Data.Nat.Log

namespace OracleTemplate.Katyusha

open LongTails.Setups.CompositeFiniteSumStronglyConvex

lemma growth_block (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) :
    2 ≤ (theta p ^ (2 * p.n)) ^ (12 * tuning p) := by
  have hτ := (tuning_bounds p hL hμ).1
  have h := one_add_mul_le_pow (show -2 ≤ tau p / 6 by linarith) (12 * tuning p)
  have he : 1 + ((12 * tuning p : ℕ) : ℝ) * (tau p / 6) = 2 := by
    have hr : (0 : ℝ) < tuning p := by exact_mod_cast tuning_pos p
    unfold tau
    push_cast
    field_simp; ring
  rw [he] at h
  exact h.trans (pow_le_pow_left₀ (by positivity)
    (theta_epoch_bounds p hL hμ).1 (12 * tuning p))

lemma katyusha_budget_accuracy (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hε : 0 < p.ε) :
    let S := 12 * tuning p * Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊
    14 * p.Δ ≤ theta p ^ (2 * p.n * S) * p.ε := by
  let B := Nat.clog 2 ⌈14 * p.Δ / p.ε⌉₊
  have hp : (2 : ℝ) ^ B ≤ theta p ^ (2 * p.n * (12 * tuning p * B)) := by
    rw [← Nat.mul_assoc, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (growth_block p hL hμ) B
  have hc : 14 * p.Δ / p.ε ≤ (2 : ℝ) ^ B := by
    calc
      _ ≤ (⌈14 * p.Δ / p.ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ B : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) ⌈14 * p.Δ / p.ε⌉₊
      _ = _ := by norm_cast
  exact (div_le_iff₀ hε).mp (hc.trans hp)

end OracleTemplate.Katyusha
