import LongTails.Proofs.CyclicPerceptronBootstrap
import LongTails.Proofs.CyclicPerceptronCone

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronCounting

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronComparisonDynamics CyclicPerceptronBootstrap CyclicPerceptronCone

noncomputable def energy {d : ℕ} (s : Comparison d) : ℝ := ‖s.U‖ ^ 2 - comparisonBias s

lemma energy_positive {d : ℕ} (β : ℝ) (s : Comparison d) (u : Features d)
    (h : s.R + s.V = s.U) :
    energy (comparisonStep false β s u) = energy s + β + ⟪s.U, u⟫ + ‖u‖ ^ 2 := by
  unfold energy
  rw [positive_bias_step β s u h]
  change ‖s.U + u‖ ^ 2 - (comparisonBias s + ⟪s.U, u⟫ - β) = _
  rw [norm_add_sq_real]
  ring

lemma energy_negative {d : ℕ} (β : ℝ) (s : Comparison d) (u : Features d)
    (h : s.R + s.V = s.U) :
    energy (comparisonStep true β s u) = energy s + β := by
  unfold energy
  rw [negative_bias_step β s u h]
  change ‖s.U + u‖ ^ 2 - (comparisonBias s + 2 * ⟪s.U, u⟫ + ‖u‖ ^ 2 - β) = _
  rw [norm_add_sq_real]
  ring

lemma bias_lower_bound {d : ℕ} (s : Comparison d) (p : Features d)
    (κ σ δ m q : ℝ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hσ : σ ≤ m) (hδ : δ ≤ 1 / 6) (hq : q ≤ 1)
    (hp : κ ≤ ‖p‖)
    (hcount : m ≤ 2 * s.positivePairs / κ + 2 / κ ^ 3)
    (hE : energy s ≤ σ + s.positivePairs * ⟪s.U, p⟫ -
      ‖p‖ ^ 2 * s.positivePairs * (s.positivePairs + 1) / 2 +
      s.positivePairs * (q + 2 * δ / κ)) :
    κ ^ 2 * (s.positivePairs : ℝ) ^ 2 / 4 -
      4 * s.positivePairs / κ - 2 / κ ^ 3 ≤ comparisonBias s := by
  let k : ℝ := s.positivePairs
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hs := square_completion s.U p k
  have hp₂ : κ ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hprod := mul_le_mul_of_nonneg_right hp₂ (show 0 ≤ k ^ 2 / 4 + k / 2 by positivity)
  have hq' := mul_le_mul_of_nonneg_left hq hk
  have hd := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 2 * k / κ by positivity)
  have hkk : k ≤ k / κ := (le_div_iff₀ hκ).mpr (by nlinarith)
  unfold energy at hE
  change _ ≤ σ + k * _ - _ * k * (k + 1) / 2 + k * _ at hE
  change m ≤ 2 * k / κ + 2 / κ ^ 3 at hcount
  change κ ^ 2 * k ^ 2 / 4 - 4 * k / κ - 2 / κ ^ 3 ≤ _
  simp only [div_eq_mul_inv] at hE hcount hd hkk ⊢
  nlinarith [mul_nonneg (sq_nonneg κ) hk]

structure Potential {d : ℕ} (β δ κ : ℝ) (p u₀ : Features d)
    (m : ℕ) (s : Comparison d) : Prop where
  partition : s.R + s.V = s.U
  count : s.positivePairs ≤ m
  energy_bound : energy s ≤ β + s.positivePairs * ⟪s.U, p⟫ -
    ‖p‖ ^ 2 * s.positivePairs * (s.positivePairs + 1) / 2 +
    s.positivePairs * (‖u₀‖ ^ 2 + 2 * δ / κ)
  norm_auxiliary : ‖s.U‖ ^ 2 ≤ 2 * (energy s - β) + m * (1 + 2 * δ) -
    s.positivePairs * (‖u₀‖ ^ 2 + 1 + 2 * δ)

lemma potential_start {d : ℕ} (δ κ : ℝ) (p u₀ : Features d) :
    Potential 0 δ κ p u₀ 0 (comparisonStart d) := by
  constructor <;> simp [comparisonStart, energy, comparisonBias]

lemma potential_positive {d : ℕ} (β γ δ κ : ℝ) (p u₀ : Features d)
    (m : ℕ) (s : Comparison d) (hs : Potential β δ κ p u₀ m s)
    (hp : ⟪p, u₀⟫ = ‖p‖ ^ 2)
    (hscore : ⟪s.U, u₀⟫ ≤ ⟪s.U, p⟫ + 2 * δ / κ) :
    Potential (β + γ) δ κ p u₀ (m + 1) (comparisonStep false γ s u₀) := by
  constructor
  · exact comparison_partition false γ s u₀ hs.partition
  · simpa [comparisonStep] using Nat.add_le_add_right hs.count 1
  · rw [energy_positive γ s u₀ hs.partition]
    simp only [comparisonStep, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one,
      inner_add_left]
    have hp' : ⟪u₀, p⟫ = ‖p‖ ^ 2 := by linarith [real_inner_comm p u₀]
    rw [hp']
    nlinarith [hs.energy_bound]
  · rw [energy_positive γ s u₀ hs.partition]
    simp only [comparisonStep, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one,
      norm_add_sq_real]
    nlinarith [hs.norm_auxiliary]

lemma potential_negative {d : ℕ} (β γ δ κ : ℝ) (p u₀ u : Features d)
    (m : ℕ) (s : Comparison d) (hs : Potential β δ κ p u₀ m s)
    (hp : 0 ≤ ⟪p, u⟫) (hu : ‖u‖ ≤ 1) (hscore : ⟪s.U, u⟫ ≤ δ) :
    Potential (β + γ) δ κ p u₀ (m + 1) (comparisonStep true γ s u) := by
  constructor
  · exact comparison_partition true γ s u hs.partition
  · simp only [comparisonStep, ↓reduceIte, Nat.add_zero]
    exact hs.count.trans (Nat.le_succ m)
  · rw [energy_negative γ s u hs.partition]
    simp only [comparisonStep, ↓reduceIte, Nat.add_zero, inner_add_left]
    have hp' : 0 ≤ ⟪u, p⟫ := by linarith [real_inner_comm p u]
    have hmul := mul_nonneg (Nat.cast_nonneg s.positivePairs) hp'
    nlinarith [hs.energy_bound]
  · rw [energy_negative γ s u hs.partition]
    simp only [comparisonStep, ↓reduceIte, Nat.add_zero, Nat.cast_add, Nat.cast_one,
      norm_add_sq_real]
    have hu₂ : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    nlinarith [hs.norm_auxiliary]

lemma potential_count {d : ℕ} (β δ κ : ℝ) (p u₀ w : Features d)
    (m : ℕ) (s : Comparison d) (hs : Potential β δ κ p u₀ m s)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 6)
    (hp : ‖p‖ ≤ 1) (hu : ‖u₀‖ ≤ 1) (hw : ‖w‖ = 1)
    (hprogress : κ * m ≤ ⟪w, s.U⟫) :
    (m : ℝ) ≤ 2 * s.positivePairs / κ + 2 / κ ^ 3 := by
  have hz : ⟪s.U, p⟫ ≤ ‖s.U‖ :=
    (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg s.U])
  have hq : ‖u₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u₀]
  have hg := energy_norm_growth ‖s.U‖ s.positivePairs m (‖u₀‖ ^ 2)
    (‖p‖ ^ 2) ⟪s.U, p⟫ 0 δ κ (energy s - β) (Nat.cast_nonneg _)
    (by exact_mod_cast hs.count) hq (sq_nonneg _) hz hκ hκ₁ hδ hδ₁
    (by simpa only [zero_mul] using (show energy s - β ≤ _ by linarith [hs.energy_bound]))
    (by simpa only [zero_mul, sub_zero] using hs.norm_auxiliary)
  have hr : κ * m ≤ ‖s.U‖ := hprogress.trans (by
    have hi := real_inner_le_norm w s.U
    simpa [hw] using hi)
  exact tolerant_norm_count _ _ _ _ (norm_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hκ hr hg

lemma positive_count_obstruction {d : ℕ} (s : Comparison d) (p u₀ : Features d)
    (β δ κ : ℝ) (m : ℕ) (hs : Potential β δ κ p u₀ m s)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hβ : β ≤ m) (hδ : δ ≤ 1 / 6)
    (hp : κ ≤ ‖p‖) (hu : ‖u₀‖ ≤ 1)
    (hcount : (m : ℝ) ≤ 2 * s.positivePairs / κ + 2 / κ ^ 3)
    (hbias : comparisonBias s * κ ^ 4 ≤ 1) :
    (s.positivePairs : ℝ) < 32 / κ ^ 3 := by
  have hu₂ : ‖u₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u₀]
  have hl := bias_lower_bound s p κ β δ m (‖u₀‖ ^ 2)
    hκ hκ₁ hβ hδ hu₂ hp hcount hs.energy_bound
  by_contra hn
  have ht : 32 ≤ κ ^ 3 * (s.positivePairs : ℝ) := by
    have hh := (div_le_iff₀ (pow_pos hκ 3)).mp (le_of_not_gt hn)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hl (pow_nonneg hκ.le 4)
  have he : (κ ^ 2 * (s.positivePairs : ℝ) ^ 2 / 4 -
      4 * s.positivePairs / κ - 2 / κ ^ 3) * κ ^ 4 =
      (κ ^ 3 * s.positivePairs) ^ 2 / 4 - 4 * (κ ^ 3 * s.positivePairs) - 2 * κ := by
    field_simp
  rw [he] at hmul
  exact (not_lt_of_ge hbias) (tolerant_bias_obstruction κ _ _ hκ₁ ht hmul)

end LongTails.Proofs.CyclicPerceptronCounting
