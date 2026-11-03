import LongTails.Algorithms.StrongGrowthBatchProx
import LongTails.Proofs.KatyushaTuning

namespace LongTails.Proofs.StrongGrowthBatchProx

open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
open LongTails.Algorithms.StrongGrowthBatchProx
open OracleTemplate

lemma batchSize_eq_min (p : Params) (hρ : 1 ≤ p.ρ) :
    batchSize p = min p.n ⌈128 * p.ρ⌉₊ := by
  have hc : (1 : ℝ) ≤ (⌈128 * p.ρ⌉₊ : ℝ) :=
    (by linarith : (1 : ℝ) ≤ 128 * p.ρ).trans (Nat.le_ceil _)
  have hc' : 1 ≤ ⌈128 * p.ρ⌉₊ := by exact_mod_cast hc
  have hn := NeZero.pos p.n
  unfold batchSize
  omega

lemma uncapped_batch_lower (p : Params) (hρ : 1 ≤ p.ρ)
    (hcap : batchSize p ≠ p.n) : 128 * p.ρ ≤ (batchSize p : ℝ) := by
  have hb : batchSize p = ⌈128 * p.ρ⌉₊ := by
    have hh := batchSize_eq_min p hρ
    omega
  rw [hb]
  exact Nat.le_ceil _

lemma innerCost_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) :
    innerCost p ≤ 108 * (batchSize p +
      ⌈Real.sqrt ((batchSize p : ℝ) * p.L / p.μ)⌉₊) *
        Nat.clog 2 ⌈7168 * (p.L + p.μ) / p.μ⌉₊ := by
  have ht := Katyusha.tuning_cost_bound (innerParams p p.x0) hL hμ
  change batchSize p * Katyusha.tuning (innerParams p p.x0) ≤
    batchSize p + ⌈Real.sqrt ((batchSize p : ℝ) * p.L / p.μ)⌉₊ at ht
  calc
    innerCost p = 108 * (batchSize p * Katyusha.tuning (innerParams p p.x0)) *
        Nat.clog 2 ⌈7168 * (p.L + p.μ) / p.μ⌉₊ := by
      unfold innerCost innerEpochs
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)

lemma totalCost_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hρ : 1 ≤ p.ρ) (T : ℕ) :
    innerCost p * T ≤ 108 * (min p.n ⌈128 * p.ρ⌉₊ +
      ⌈Real.sqrt (((min p.n ⌈128 * p.ρ⌉₊ : ℕ) : ℝ) * p.L / p.μ)⌉₊) *
        Nat.clog 2 ⌈7168 * (1 + p.L / p.μ)⌉₊ * T := by
  have hh := Nat.mul_le_mul_right T (innerCost_bound p hL hμ)
  rw [batchSize_eq_min p hρ] at hh
  have he : 7168 * (p.L + p.μ) / p.μ = 7168 * (1 + p.L / p.μ) := by
    field_simp
    ring
  simpa only [he] using hh

lemma accuracy_tuning (p : Params) (hε : 0 < p.ε) :
    p.L / 2 * ((1 / 2 : ℝ) ^ Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊ * p.R ^ 2) ≤ p.ε := by
  let T := Nat.clog 2 ⌈p.L * p.R ^ 2 / p.ε⌉₊
  have hc : p.L * p.R ^ 2 / p.ε ≤ (2 : ℝ) ^ T := by
    calc
      _ ≤ (⌈p.L * p.R ^ 2 / p.ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ T : ℕ) : ℝ) := by
        exact Nat.cast_le.mpr (Nat.le_pow_clog (by decide : 1 < 2) ⌈p.L * p.R ^ 2 / p.ε⌉₊)
      _ = _ := by simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hp : 0 < (2 : ℝ) ^ T := pow_pos (by norm_num) T
  have hs : (1 / 2 : ℝ) ^ T = ((2 : ℝ) ^ T)⁻¹ := by rw [one_div, inv_pow]
  have he : p.L / 2 * ((1 / 2 : ℝ) ^ T * p.R ^ 2) =
      (p.L * p.R ^ 2) / (2 * (2 : ℝ) ^ T) := by rw [hs]; ring
  change p.L / 2 * ((1 / 2 : ℝ) ^ T * p.R ^ 2) ≤ p.ε
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ T)).mpr
  have hh := (div_le_iff₀ hε).mp hc
  nlinarith [mul_pos hε hp]

end LongTails.Proofs.StrongGrowthBatchProx
