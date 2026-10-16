import LongTails.Algorithms.RelativeQuasar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.RelativeQuasar

open LongTails.Setups.RelativeGradientStrongQuasar

lemma theta_bounds (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hγ : 0 < p.γ) (hδ : p.δ < 1) :
    0 < theta p ∧ 64 * theta p ^ 2 * p.L ≤ p.μ * (1 - p.δ) ∧
      32 * theta p * p.δ ^ 2 * p.L ≤ p.γ * p.μ * (1 - p.δ) := by
  let a := 8 * Real.sqrt (p.L / (p.μ * (1 - p.δ)))
  let d := 32 * p.δ ^ 2 * p.L / (p.γ * p.μ * (1 - p.δ))
  have hs : 0 < 1 - p.δ := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hZ : 0 < a + d := by linarith
  have ht : theta p = 1 / (a + d) := rfl
  have htp : 0 < theta p := by rw [ht]; positivity
  have hta : theta p * a ≤ 1 := by
    rw [ht, one_div, inv_mul_eq_div]
    exact (div_le_one hZ).mpr (by linarith)
  have htd : theta p * d ≤ 1 := by
    rw [ht, one_div, inv_mul_eq_div]
    exact (div_le_one hZ).mpr (by linarith)
  have ha2 : a ^ 2 = 64 * (p.L / (p.μ * (1 - p.δ))) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hsq := pow_le_pow_left₀ (show 0 ≤ theta p * a by positivity) hta 2
  rw [mul_pow, ha2] at hsq
  have hh := mul_le_mul_of_nonneg_right hsq (show 0 ≤ p.μ * (1 - p.δ) by positivity)
  have hid : (theta p ^ 2 * (64 * (p.L / (p.μ * (1 - p.δ))))) *
      (p.μ * (1 - p.δ)) = 64 * theta p ^ 2 * p.L := by
    field_simp
  rw [hid] at hh
  refine ⟨htp, by nlinarith, ?_⟩
  have hn := mul_le_mul_of_nonneg_right htd
    (show 0 ≤ p.γ * p.μ * (1 - p.δ) by positivity)
  dsimp [d] at hn
  field_simp at hn
  nlinarith

lemma generator_coefficient {L μ γ θ δ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hγ : 0 < γ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hs : 64 * θ ^ 2 * L ≤ μ * (1 - δ))
    (hn : 32 * θ * δ ^ 2 * L ≤ γ * μ * (1 - δ)) :
    (δ ^ 2 - 1) / (2 * L) + 4 * θ ^ 2 / μ + 2 * θ * δ ^ 2 / (γ * μ) ≤ 0 := by
  have h1 : (δ ^ 2 - 1) / (2 * L) ≤ -(1 - δ) / (2 * L) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have h2 : 4 * θ ^ 2 / μ ≤ (1 - δ) / (16 * L) := by
    rw [div_le_div_iff₀ hμ (by positivity)]
    nlinarith
  have h3 : 2 * θ * δ ^ 2 / (γ * μ) ≤ (1 - δ) / (16 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc
    _ ≤ -(1 - δ) / (2 * L) + (1 - δ) / (16 * L) + (1 - δ) / (16 * L) :=
      add_le_add (add_le_add h1 h2) h3
    _ = -3 * (1 - δ) / (8 * L) := by ring
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

lemma blockLength_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hγ : 0 < p.γ) (hδ : p.δ < 1) : 4 ≤ (blockLength p : ℝ) * (p.γ * theta p) := by
  have ht := (theta_bounds p hL hμ hγ hδ).1
  have hc : 0 < p.γ * theta p := mul_pos hγ ht
  have he : 4 / (p.γ * theta p) =
      32 * Real.sqrt (p.L / (p.μ * (1 - p.δ))) / p.γ +
        128 * p.δ ^ 2 * p.L / (p.γ ^ 2 * p.μ * (1 - p.δ)) := by
    unfold theta
    field_simp
    ring
  apply (div_le_iff₀ hc).mp
  rw [he]
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _))

lemma block_contraction {c : ℝ} (hc : 0 < c) (m : ℕ) (hm : 4 ≤ (m : ℝ) * c) :
    (4 / (4 + c)) ^ m ≤ (1 / 2 : ℝ) := by
  have hq : 0 ≤ 4 / (4 + c) := by positivity
  have hprod : (4 / (4 + c)) * (1 + c / 4) = 1 := by field_simp
  have hp : (4 / (4 + c)) ^ m * (1 + c / 4) ^ m = 1 := by
    rw [← mul_pow, hprod, one_pow]
  have hb := one_add_mul_le_pow (show -2 ≤ c / 4 by linarith) m
  have hh := mul_le_mul_of_nonneg_left hb (pow_nonneg hq m)
  have hbase : (2 : ℝ) ≤ 1 + (m : ℝ) * (c / 4) := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hbase (pow_nonneg hq m)
  nlinarith

lemma blocks_accuracy (p : Params) (hγ : 0 < p.γ) (hε : 0 < p.ε) :
    2 * p.Δ / p.γ ≤ (2 : ℝ) ^ blocks p * p.ε := by
  have hc : 2 * p.Δ / (p.γ * p.ε) ≤ (2 : ℝ) ^ blocks p := by
    calc
      _ ≤ 1 + 2 * p.Δ / (p.γ * p.ε) := by linarith
      _ ≤ (⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) _
      _ ≤ (2 : ℝ) ^ blocks p := by
        norm_cast
        exact Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  have hh := (div_le_iff₀ (mul_pos hγ hε)).mp hc
  apply (div_le_iff₀ hγ).mpr
  nlinarith

end OracleTemplate.RelativeQuasar
