import LongTails.Proofs.AffineResidualRadius

namespace LongTails.Proofs.AffineResidualPublicBudget

open LongTails.Algorithms.AffineResidualRadius
open LongTails.Algorithms.AffineSoftmaxRadius (publicDepth)

lemma meanCostBound_nonneg {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) : 0 ≤ meanCostBound m G L R ε := by
  have hr := AffineResidualRadius.publicRadius_bounds (m := m) (L := L) (ε := ε) hR
  have ht := zero_le_one.trans (AffineSoftmaxOuterParameters.compilerScale_bounds hr.1 hr.2).1
  have hf := AffineSoftmaxOuterParameters.compilerFloor_pos hr.1 hr.2 (show 0 < ε / 2 by positivity) (G := G)
  have hτ := AffineSoftmaxRadius.public_temperature_pos hm hε
  dsimp only [meanCostBound]
  positivity

lemma trial_budget_le {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    Nat.ceil (12 * meanCostBound m G L R ε) + m ≤
      Nat.ceil (10000000000000000000000 * (publicDepth m G L R ε : ℝ) ^ 8 *
        ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (2 / 5 : ℝ) +
          (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) + (L * R ^ 2 / ε) ^ (2 / 3 : ℝ))) := by
  let h := (publicDepth m G L R ε : ℝ)
  let S := (m : ℝ) + m * (L * R ^ 2 / ε) ^ (2 / 5 : ℝ) +
    (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) + (L * R ^ 2 / ε) ^ (2 / 3 : ℝ)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hS : (m : ℝ) ≤ S := by
    dsimp [S]
    have h1 : 0 ≤ (m : ℝ) * (L * R ^ 2 / ε) ^ (2 / 5 : ℝ) := by positivity
    have h2 : 0 ≤ (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) := by positivity
    have h3 : 0 ≤ (L * R ^ 2 / ε) ^ (2 / 3 : ℝ) := by positivity
    linarith
  have hh : 1 ≤ h := by
    have hh3 : (3 : ℝ) ≤ publicDepth m G L R ε := by
      exact_mod_cast (AffineSoftmaxRadius.public_height_bounds hm hG hL hR hε).1
    dsimp [h]
    linarith
  have hprod : S ≤ h ^ 8 * S := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hh)
  have hB := AffineResidualRadius.meanCostBound_public_le hm hG hL hR hε
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 12 * meanCostBound m G L R ε from
    mul_nonneg (by norm_num) (meanCostBound_nonneg hm hL hR hε))
  have hcost : (Nat.ceil (12 * meanCostBound m G L R ε) : ℝ) + m ≤
      10000000000000000000000 * h ^ 8 * S := by
    change meanCostBound m G L R ε ≤ 600000000000000000000 * h ^ 8 * S at hB
    nlinarith only [hB, hceil, hprod, hS, hm2]
  exact Nat.cast_le.mp (show ((Nat.ceil (12 * meanCostBound m G L R ε) + m : ℕ) : ℝ) ≤
    (Nat.ceil (10000000000000000000000 * h ^ 8 * S) : ℝ) by
      rw [Nat.cast_add]
      exact hcost.trans (Nat.le_ceil _))

end LongTails.Proofs.AffineResidualPublicBudget
