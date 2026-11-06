import LongTails.Proofs.AffineSoftmaxRadius

namespace LongTails.Proofs.AffineSoftmaxPublicBudget

open LongTails.Algorithms.AffineSoftmaxRadius
open AffineSoftmaxRadius

lemma mixed_dimensionless_identity {G L R ε : ℝ} :
    (G * R / ε) * (L * R ^ 2 / ε) = G * L * R ^ 3 / ε ^ 2 := by ring

lemma meanCostBound_nonneg {m : ℕ} {G L R ε : ℝ}
    (hR : 0 < R) : 0 ≤ meanCostBound m G L R ε := by
  have hr := publicRadius_bounds (m := m) (G := G) (L := L) (ε := ε) hR
  have ht := zero_le_one.trans (AffineSoftmaxOuterParameters.compilerScale_bounds hr.1 hr.2).1
  dsimp only [meanCostBound]
  positivity

lemma meanCostBound_public_le {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    meanCostBound m G L R ε ≤ 46875000000000000000 * (publicDepth m G L R ε : ℝ) ^ 7 *
      ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
        (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) + G * R / ε) := by
  let h := (publicDepth m G L R ε : ℝ)
  let S := (m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
    (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) + G * R / ε
  have hdepth : (LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) (publicRadius m G L R ε) (ε / 2) : ℝ) ≤ 5 * h := by
    have hh : (LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) (publicRadius m G L R ε) (ε / 2) : ℝ) ≤
        ((5 * publicDepth m G L R ε : ℕ) : ℝ) := Nat.cast_le.mpr (public_compiler_depth_bound hm hG hL hR hε)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hr := publicRadius_bounds (m := m) (G := G) (L := L) (ε := ε) hR
  have ht := zero_le_one.trans (AffineSoftmaxOuterParameters.compilerScale_bounds hr.1 hr.2).1
  have hbracket := public_cost_bracket_bound hm hG hL hR hε
  rw [mixed_dimensionless_identity] at hbracket
  dsimp only [meanCostBound]
  calc
    _ ≤ 50000000000000 * (5 * h) ^ 6 * (60 * h * S) := by
      gcongr
    _ = 46875000000000000000 * h ^ 7 * S := by ring

lemma amplification_budget_le {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    6 * (Nat.ceil (6 * meanCostBound m G L R ε) + m) ≤
      Nat.ceil (2000000000000000000000 * (publicDepth m G L R ε : ℝ) ^ 7 *
        ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
          (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) + G * R / ε)) := by
  let h := (publicDepth m G L R ε : ℝ)
  let S := (m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
    (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) + G * R / ε
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hS : (m : ℝ) ≤ S := by
    dsimp [S]
    have h1 : 0 ≤ (m : ℝ) * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) := by positivity
    have h2 : 0 ≤ (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) := by positivity
    have h3 : 0 ≤ (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) := by positivity
    have h4 : 0 ≤ G * R / ε := by positivity
    linarith
  have hh : 1 ≤ h := by
    have hh3 : (3 : ℝ) ≤ publicDepth m G L R ε := by exact_mod_cast (public_height_bounds hm hG hL hR hε).1
    dsimp [h]
    linarith
  have hprod : S ≤ h ^ 7 * S := le_mul_of_one_le_left (by linarith) (one_le_pow₀ hh)
  have hB := meanCostBound_public_le hm hG hL hR hε
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 6 * meanCostBound m G L R ε from mul_nonneg (by norm_num) (meanCostBound_nonneg hR))
  have hcost : (6 * (Nat.ceil (6 * meanCostBound m G L R ε) + m) : ℝ) ≤ 2000000000000000000000 * h ^ 7 * S := by
    change meanCostBound m G L R ε ≤ 46875000000000000000 * h ^ 7 * S at hB
    nlinarith only [hB, hceil, hprod, hS, hm2]
  have hhcast : ((6 * (Nat.ceil (6 * meanCostBound m G L R ε) + m) : ℕ) : ℝ) ≤
      (Nat.ceil (2000000000000000000000 * h ^ 7 * S) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    exact hcost.trans (Nat.le_ceil _)
  exact Nat.cast_le.mp hhcast

lemma repetitions_budget_le {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) (n : ℕ) :
    n * (Nat.ceil (6 * meanCostBound m G L R ε) + m) ≤
      n * Nat.ceil (2000000000000000000000 * (publicDepth m G L R ε : ℝ) ^ 7 *
        ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
          (m : ℝ) ^ (6 / 7 : ℝ) * (G * L * R ^ 3 / ε ^ 2) ^ (2 / 7 : ℝ) + G * R / ε)) := by
  have hh := amplification_budget_le hm hG hL hR hε
  exact Nat.mul_le_mul_left n ((show Nat.ceil (6 * meanCostBound m G L R ε) + m ≤
    6 * (Nat.ceil (6 * meanCostBound m G L R ε) + m) by omega).trans hh)

end LongTails.Proofs.AffineSoftmaxPublicBudget
