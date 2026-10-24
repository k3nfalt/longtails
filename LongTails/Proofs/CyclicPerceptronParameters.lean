import LongTails.Algorithms.CyclicFullWidthPerceptron
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace LongTails.Proofs.CyclicPerceptronParameters

lemma tuning_bounds (κ μ H : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hμ : 0 < μ) (hμ₁ : μ ≤ κ ^ 4 / 2 ^ 20)
    (hH : 1 ≤ H) (hH₁ : H ≤ 256 / κ ^ 4) :
    let η := κ ^ 6 / 2 ^ 28
    0 < η ∧ η ^ 2 ≤ 1 ∧ μ ≤ 1 ∧ μ * H ≤ 1 / 4096 ∧
      η ^ 2 * H ^ 2 ≤ 1 / 1024 ∧
      256 * η ^ 2 * H ^ 3 ≤ 1 / 6 ∧
      256 * η ^ 2 * H ^ 4 * κ ^ 4 ≤ 1 := by
  dsimp only
  have hκ₄ : κ ^ 4 ≤ 1 := pow_le_one₀ hκ.le hκ₁
  have hκ₁₂ : κ ^ 12 ≤ 1 := pow_le_one₀ hκ.le hκ₁
  have hH0 : 0 ≤ H := by linarith
  have hη : 0 < κ ^ 6 / 2 ^ 28 := by positivity
  have hμ₂ : μ ≤ 1 := by nlinarith
  have hμH : μ * H ≤ 1 / 4096 := by
    calc
      μ * H ≤ (κ ^ 4 / 2 ^ 20) * (256 / κ ^ 4) := by gcongr
      _ = 1 / 4096 := by field_simp; norm_num
  have hcube : (κ ^ 6 / 2 ^ 28) ^ 2 * H ^ 3 ≤ 1 / 2 ^ 32 := by
    calc
      _ ≤ (κ ^ 6 / 2 ^ 28) ^ 2 * (256 / κ ^ 4) ^ 3 := by gcongr
      _ = 1 / 2 ^ 32 := by field_simp; ring
  have hfour : 256 * (κ ^ 6 / 2 ^ 28) ^ 2 * H ^ 4 * κ ^ 4 ≤ 1 := by
    calc
      _ ≤ 256 * (κ ^ 6 / 2 ^ 28) ^ 2 * (256 / κ ^ 4) ^ 4 * κ ^ 4 := by gcongr
      _ = 1 / 65536 := by field_simp; ring
      _ ≤ 1 := by norm_num
  have hpow : H ^ 2 ≤ H ^ 3 := by nlinarith [sq_nonneg (H - 1)]
  have hsq := mul_le_mul_of_nonneg_left hpow (sq_nonneg (κ ^ 6 / 2 ^ 28))
  have hη₂ : (κ ^ 6 / 2 ^ 28) ^ 2 ≤ 1 := by
    have hh : 1 ≤ H ^ 2 := by nlinarith
    nlinarith [sq_nonneg (κ ^ 6 / 2 ^ 28)]
  exact ⟨hη, hη₂, hμ₂, hμH, by linarith, by linarith, hfour⟩

lemma horizon_bounds (κ : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) :
    let H : ℕ := ⌈128 / κ ^ 4⌉₊
    1 ≤ (H : ℝ) ∧ (H : ℝ) ≤ 256 / κ ^ 4 ∧
      ∀ m : ℕ, (m : ℝ) ≤ 68 / κ ^ 4 → m + 1 ≤ H := by
  dsimp only
  have hκ₄ : κ ^ 4 ≤ 1 := pow_le_one₀ hκ.le hκ₁
  have hpos : 0 < κ ^ 4 := pow_pos hκ 4
  have hlow := Nat.le_ceil (128 / κ ^ 4)
  have hone : (1 : ℝ) ≤ 128 / κ ^ 4 :=
    (le_div_iff₀ hpos).mpr (by nlinarith)
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ 128 / κ ^ 4 by positivity)
  refine ⟨hone.trans hlow, ?_, ?_⟩
  · have hh : 128 / κ ^ 4 + 1 ≤ 256 / κ ^ 4 := by
      have he : 256 / κ ^ 4 = 128 / κ ^ 4 + 128 / κ ^ 4 := by ring
      rw [he]
      linarith
    exact hupper.le.trans hh
  · intro m hm
    have hh : (m : ℝ) + 1 ≤ 128 / κ ^ 4 := by
      have hc : 68 / κ ^ 4 + 1 ≤ 128 / κ ^ 4 := by
        apply (le_div_iff₀ hpos).mpr
        have he : (68 / κ ^ 4 + 1) * κ ^ 4 = 68 + κ ^ 4 := by field_simp
        rw [he]
        nlinarith
      linarith
    exact_mod_cast hh.trans hlow

lemma mismatch_scaling (κ μ ν : ℝ) (hκ : 0 < κ) (hμ : 0 < μ)
    (hν : 0 ≤ ν) (hν₁ : ν ≤ κ ^ 12 * μ ^ 2 / 2 ^ 56) :
    let η := κ ^ 6 / 2 ^ 28
    let β := ν / (η ^ 2 * μ ^ 2)
    0 ≤ β ∧ β ≤ 1 ∧ ν = β * η ^ 2 * μ ^ 2 := by
  dsimp only
  have hd : 0 < (κ ^ 6 / 2 ^ 28) ^ 2 * μ ^ 2 := by positivity
  have he : (κ ^ 6 / 2 ^ 28) ^ 2 * μ ^ 2 = κ ^ 12 * μ ^ 2 / 2 ^ 56 := by ring
  refine ⟨div_nonneg hν hd.le, (div_le_one hd).mpr (by rwa [he]), ?_⟩
  field_simp

end LongTails.Proofs.CyclicPerceptronParameters
