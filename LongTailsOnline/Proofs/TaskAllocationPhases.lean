import LongTailsOnline.Proofs.TaskAllocationConfidence
import LongTailsOnline.Proofs.TaskAllocationOracle

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma level_eq_optimum {k B : ℕ} (u : Worker k → ℝ) :
    level (B := B) u = optimum (B := B) u :=
  (upperOracle_le u (oracle (B := B) u)).antisymm (optimum_le_loss u (upperOracle u))

lemma quota_pos (p : Public) (θ u : ℝ) {C : ℕ} (hC : 0 < C) : 0 < quota p θ u C := by
  unfold quota
  rw [ite_eq_right (Nat.ne_of_gt hC)]
  omega

lemma quota_refinement {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ u : ℝ} {C N : ℕ} (hθ : 0 < θ) (hu : 0 ≤ u) (hC : 0 < C)
    (hN : quota p θ u C ≤ N) (hβ : bias p ≤ θ / (16 * C)) :
    2 * radius p u N ≤ θ / (2 * C) := by
  have hχ := scale_ge_one hB hT
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hNr : (0 : ℝ) < N := by exact_mod_cast (quota_pos p θ u hC).trans_le hN
  have hceil : ⌈256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
      32 * scale p * C / θ⌉₊ + 1 ≤ N := by
    simpa only [quota, ite_eq_right (Nat.ne_of_gt hC)] using hN
  have hceil' : (⌈256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
      32 * scale p * C / θ⌉₊ : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ _) hceil)
  have hsum := (Nat.le_ceil (256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
    32 * scale p * C / θ)).trans hceil'
  have h0 : 0 ≤ 256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 := by positivity
  have h1 : 0 ≤ 32 * scale p * C / θ := by positivity
  have hquad : 256 * scale p * u * (C : ℝ) ^ 2 ≤ N * θ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hθ)).mp
    linarith
  have hlinear : 32 * scale p * C ≤ N * θ := by
    apply (div_le_iff₀ hθ).mp
    linarith
  let r := Real.sqrt (u * scale p / N)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : (N : ℝ) * r ^ 2 = u * scale p := by
    dsimp only [r]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hsquare : (16 * (C : ℝ) * r) ^ 2 ≤ θ ^ 2 := by
    apply le_of_mul_le_mul_left (a0 := hNr)
    calc
      (N : ℝ) * (16 * (C : ℝ) * r) ^ 2 = 256 * (C : ℝ) ^ 2 * ((N : ℝ) * r ^ 2) := by ring
      _ = 256 * scale p * u * (C : ℝ) ^ 2 := by rw [hrsq]; ring
      _ ≤ _ := hquad
  have hroot : 4 * r ≤ θ / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    nlinarith
  have hlin : 4 * scale p / N ≤ θ / (8 * C) := by
    apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < 8 * C)).mpr
    nlinarith
  have hbias : 2 * bias p ≤ θ / (8 * C) := by
    calc
      _ ≤ 2 * (θ / (16 * C)) := mul_le_mul_of_nonneg_left hβ (by norm_num)
      _ = _ := by ring
  calc
    2 * radius p u N = 4 * r + 4 * scale p / N + 2 * bias p := by unfold radius r; ring
    _ ≤ θ / (4 * C) + θ / (8 * C) + θ / (8 * C) :=
      add_le_add (add_le_add hroot hlin) hbias
    _ = _ := by ring

end LongTailsOnline.Proofs.TaskAllocation
