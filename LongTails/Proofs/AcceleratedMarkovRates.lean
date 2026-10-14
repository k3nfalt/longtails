import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.HeavyTailedMarkovGradient

lemma sum_accelerated_weights_rpow {p : ℝ} (hp : 0 ≤ p) (K : ℕ) :
    (∑ k ∈ Finset.range K, (((k : ℝ) + 1) / 2) ^ p) ≤
      (K : ℝ) * ((K : ℝ) / 2) ^ p := by
  calc
    _ ≤ ∑ _k ∈ Finset.range K, ((K : ℝ) / 2) ^ p := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp
    _ = _ := by simp

lemma accelerated_noise_coefficient {N D R p : ℝ} (hN : 0 < N) (hD : 0 < D) (hR : 0 ≤ R) :
    4 / N * (N / 2) ^ p * ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1)) =
      4 * R ^ (2 - p) * N ^ (p - 1) / D ^ (p - 1) := by
  have htwo : (2 : ℝ) ^ (2 - p) * 4 ^ (p - 1) = 2 ^ p := by
    have hf : (4 : ℝ) ^ (p - 1) = 2 ^ (2 * (p - 1)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
      norm_num
    rw [hf, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnp : N ^ p = N * N ^ (p - 1) := by
    nth_rw 2 [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [Real.div_rpow hN.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR,
    Real.div_rpow hD.le (by norm_num : (0 : ℝ) ≤ 4), hnp]
  have hpowD : D ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hD _)
  have hpow2 : (2 : ℝ) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow4 : (4 : ℝ) ^ (p - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp
  linear_combination R ^ (2 - p) * htwo

lemma accelerated_finite_sum_bound {D R p σ b : ℝ} (hD : 0 < D) (hR : 0 ≤ R)
    (hσ : 0 ≤ σ) (hp : 0 ≤ p) (K : ℕ) (hK : 0 < K) :
    (D / 2 * R ^ 2 + (∑ k ∈ Finset.range K, (((k : ℝ) + 1) / 2) ^ p) *
      ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) * σ ^ p)) /
        ((K : ℝ) * ((K : ℝ) + 1) / 4) + b ≤
      2 * D * R ^ 2 / (K : ℝ) ^ 2 +
      4 * σ ^ p * R ^ (2 - p) * (K : ℝ) ^ (p - 1) / D ^ (p - 1) + b := by
  have hN : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hW : (K : ℝ) ^ 2 / 4 ≤ (K : ℝ) * ((K : ℝ) + 1) / 4 := by nlinarith
  have hWpos : 0 < (K : ℝ) ^ 2 / 4 := by positivity
  let c := (2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) * σ ^ p
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi : (D / 2 * R ^ 2) / ((K : ℝ) * ((K : ℝ) + 1) / 4) ≤
      2 * D * R ^ 2 / (K : ℝ) ^ 2 := by
    calc
      _ ≤ (D / 2 * R ^ 2) / ((K : ℝ) ^ 2 / 4) := div_le_div_of_nonneg_left (by positivity) hWpos hW
      _ = _ := by ring
  have hn : (∑ k ∈ Finset.range K, (((k : ℝ) + 1) / 2) ^ p) * c /
      ((K : ℝ) * ((K : ℝ) + 1) / 4) ≤
      4 * σ ^ p * R ^ (2 - p) * (K : ℝ) ^ (p - 1) / D ^ (p - 1) := by
    calc
      _ ≤ ((K : ℝ) * ((K : ℝ) / 2) ^ p) * c / ((K : ℝ) * ((K : ℝ) + 1) / 4) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (sum_accelerated_weights_rpow hp K) hc) (by positivity)
      _ ≤ ((K : ℝ) * ((K : ℝ) / 2) ^ p) * c / ((K : ℝ) ^ 2 / 4) :=
        div_le_div_of_nonneg_left (by positivity) hWpos hW
      _ = (4 / (K : ℝ) * ((K : ℝ) / 2) ^ p * ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1))) * σ ^ p := by
        dsimp [c]
        field_simp
      _ = _ := by rw [accelerated_noise_coefficient hN hD hR]; ring
  rw [add_div]
  exact add_le_add (add_le_add hi hn) (le_refl b)

lemma polynomial_mixing_tuning {τ β H : ℝ} (hτ : 0 < τ) (hβ : 0 < β) (hH : 0 < H)
    (m : ℕ) (hm : τ * H ^ (1 / β) ≤ (m : ℝ)) :
    (1 + (m : ℝ) / τ) ^ (-β) ≤ 1 / H := by
  have hh : H ^ (1 / β) ≤ 1 + (m : ℝ) / τ := by
    have h := (le_div_iff₀ hτ).mpr (by nlinarith only [hm] : H ^ (1 / β) * τ ≤ (m : ℝ))
    linarith
  calc
    _ ≤ (H ^ (1 / β)) ^ (-β) := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hH _) hh (by linarith)
    _ = 1 / H := by
      rw [← Real.rpow_mul hH.le, show 1 / β * -β = -1 by field_simp, Real.rpow_neg_one, one_div]

lemma accelerated_initial_tuning {L R ε N : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hN : 0 < N) (hbudget : Real.sqrt (32 * L * R ^ 2 / ε) ≤ N) :
    2 * (2 * L + ε * N ^ 2 / (16 * R ^ 2)) * R ^ 2 / N ^ 2 ≤ ε / 4 := by
  have hs : 32 * L * R ^ 2 / ε ≤ N ^ 2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hN.le).mpr hbudget
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hs' := (div_le_iff₀ hε).mp hs
  calc
    _ = 4 * L * R ^ 2 / N ^ 2 + ε / 8 := by field_simp; ring
    _ ≤ ε / 8 + ε / 8 := by
      apply add_le_add _ (le_refl _)
      apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
      nlinarith only [hs']
    _ = _ := by ring

end OracleTemplate.HeavyTailedMarkovGradient
