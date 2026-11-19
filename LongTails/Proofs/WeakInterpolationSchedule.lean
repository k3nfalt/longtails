import LongTails.Algorithms.WeightedInterpolationSgd
import Mathlib.Tactic

namespace LongTails.Proofs.WeakInterpolationSchedule

lemma initial_phase {D : ℕ → ℝ} {m R V e : ℝ} {H : ℕ}
    (hm : 1 ≤ m) (hV : 0 ≤ V) (he : 0 ≤ e) (h0 : D 0 ≤ R)
    (hstep : ∀ k < H, D (k + 1) ≤ (1 - 1 / m) * D k + 4 * V / m ^ 2 + e) :
    ∀ k ≤ H, D k ≤ (1 - 1 / m) ^ k * R + 4 * V / m + k * e := by
  have hm0 : 0 < m := by linarith
  have ha : 0 ≤ 1 - 1 / m := sub_nonneg.mpr ((div_le_one hm0).mpr hm)
  intro k
  induction k with
  | zero =>
    intro _
    simpa using h0.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hV) hm0.le))
  | succ k ih =>
    intro hk
    have h := hstep k (by omega)
    have hb := mul_le_mul_of_nonneg_left (ih (by omega)) ha
    have heq : (1 - 1 / m) * (4 * V / m) + 4 * V / m ^ 2 = 4 * V / m := by
      field_simp
      ring
    push_cast
    rw [pow_succ]
    have hshrink := mul_le_mul_of_nonneg_right (sub_le_self 1 (one_div_nonneg.mpr hm0.le))
      (mul_nonneg (Nat.cast_nonneg k) he)
    linear_combination h + hb + heq + hshrink

lemma final_phase {D : ℕ → ℝ} {m B V e : ℝ} {H : ℕ}
    (hm : 1 ≤ m) (hB : 0 ≤ B) (hV : 0 ≤ V) (he : 0 ≤ e)
    (h0 : D H ≤ B + 4 * V / m + H * e)
    (hstep : ∀ j < H, let s : ℝ := 2 * m + j
      D (H + j + 1) ≤ (1 - 2 / s) * D (H + j) + 16 * V / s ^ 2 + e) :
    ∀ j ≤ H, D (H + j) ≤ B + 16 * V / (2 * m + j) + (H + j : ℕ) * e := by
  have hm0 : 0 < m := by linarith
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.cast_zero, add_zero]
    have hfrac : 4 * V / m ≤ 16 * V / (2 * m) := by
      rw [div_le_div_iff₀ hm0 (by positivity)]
      nlinarith [mul_nonneg hV hm0.le]
    linarith
  | succ j ih =>
    intro hj
    let s : ℝ := 2 * m + j
    have hs : 2 ≤ s := by dsimp [s]; linarith [show 0 ≤ (j : ℝ) from Nat.cast_nonneg j]
    have hs0 : 0 < s := by linarith
    have ha : 0 ≤ 1 - 2 / s := sub_nonneg.mpr ((div_le_one hs0).mpr hs)
    have h1 := hstep j (by omega)
    have h2 := mul_le_mul_of_nonneg_left (ih (show j ≤ H by omega)) ha
    change D (H + j + 1) ≤ (1 - 2 / s) * D (H + j) + 16 * V / s ^ 2 + e at h1
    change (1 - 2 / s) * D (H+j) ≤ (1 - 2 / s) * (B + 16 * V / s + (H+j : ℕ) * e) at h2
    have hfrac : (1 - 2 / s) * (16 * V / s) + 16 * V / s ^ 2 ≤ 16 * V / (s + 1) := by
      field_simp
      nlinarith
    have hshrink := mul_le_mul_of_nonneg_right (sub_le_self 1 (show 0 ≤ 2 / s by positivity))
      (show 0 ≤ B + (H+j : ℕ) * e by positivity)
    rw [Nat.cast_succ, show 2*m+((j:ℝ)+1) = s+1 by dsimp [s]; ring]
    push_cast at *
    simp only [← Nat.add_assoc] at *
    linear_combination h1 + h2 + hfrac + hshrink

end LongTails.Proofs.WeakInterpolationSchedule
