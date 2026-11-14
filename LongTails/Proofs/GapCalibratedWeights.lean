import LongTails.Proofs.GeneralizedSmoothHardChainRadius

open scoped BigOperators

namespace LongTails.Proofs.GapCalibratedWeights

noncomputable def weight (m : ℕ) (g t : ℝ) (i : Fin m) : ℝ :=
  g * Real.exp (((m : ℝ) - 1 - i.val) * t)

noncomputable def peak (m : ℕ) (g t : ℝ) : ℝ :=
  g * Real.exp (((m : ℝ) - 1) * t)

lemma weight_pos (m : ℕ) (g t : ℝ) (hg : 0 < g) (i : Fin m) :
    0 < weight m g t i := by
  unfold weight
  positivity

lemma peak_pos (m : ℕ) (g t : ℝ) (hg : 0 < g) : 0 < peak m g t := by
  unfold peak
  positivity

lemma weight_lower (m : ℕ) (g t : ℝ) (hg : 0 ≤ g) (ht : 0 ≤ t) (i : Fin m) :
    g ≤ weight m g t i := by
  have hi : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  have he := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith : 0 ≤ (m : ℝ) - 1 - i.val) ht)
  simpa only [mul_one, weight] using mul_le_mul_of_nonneg_left he hg

lemma weight_le_peak (m : ℕ) (g t : ℝ) (hg : 0 ≤ g) (ht : 0 ≤ t) (i : Fin m) :
    weight m g t i ≤ peak m g t := by
  unfold weight peak
  apply mul_le_mul_of_nonneg_left _ hg
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ ht
  linarith [Nat.cast_nonneg i.val (α := ℝ)]

lemma weight_ratio (m : ℕ) (g t : ℝ) (i j : Fin m) :
    weight m g t i = weight m g t j * Real.exp (((j.val : ℝ) - i.val) * t) := by
  unfold weight
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma ratio_lower (m : ℕ) (g t : ℝ) (hg : 0 ≤ g) (ht : 0 ≤ t)
    (i j : Fin m) (hij : i < j) : weight m g t j * (1 + t) ≤ weight m g t i := by
  have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  have he := Real.add_one_le_exp (((j.val : ℝ) - i.val) * t)
  have hx : t ≤ ((j.val : ℝ) - i.val) * t := by nlinarith
  rw [weight_ratio m g t i j]
  apply mul_le_mul_of_nonneg_left _ (by unfold weight; positivity)
  linarith

lemma tail_bound (m : ℕ) (g t : ℝ) (hg : 0 ≤ g) (ht : 0 < t) (i : Fin m) :
    GeneralizedSmoothHardTransfer.tailSum (weight m g t) i ≤ (1 + 1 / t) * weight m g t i := by
  apply GeneralizedSmoothHardChainRadius.tailSum_geometric_bound _ _ (by positivity)
    (fun j => by unfold weight; positivity)
  intro j k hjk
  simpa only [one_div_one_div] using ratio_lower m g t hg ht.le j k hjk

lemma margin (m : ℕ) (g t L₁ : ℝ) (hg : 0 < g) (ht : 0 < t) (ht1 : t ≤ 1)
    (hL₁ : 0 < L₁) (i j : Fin m) (hij : i < j) :
    t / (8 * L₁) * (weight m g t i + weight m g t j) <
      2 * (weight m g t i - weight m g t j) / L₁ :=
  GeneralizedSmoothHardChain.ratio_margin _ _ t L₁ (weight_pos m g t hg j) ht ht1 hL₁
    (ratio_lower m g t hg.le ht.le i j hij)

lemma peak_bound (m : ℕ) (g t : ℝ) (hg : 0 ≤ g) (ht : 0 ≤ t) :
    peak m g t ≤ g * Real.exp ((m : ℝ) * t) := by
  unfold peak
  apply mul_le_mul_of_nonneg_left _ hg
  apply Real.exp_le_exp.mpr
  nlinarith

lemma calibrated_gap (ε Δ t : ℝ) (m : ℕ) (hε : 0 < ε) (hΔ : 8 * ε ≤ Δ)
    (ht : (m : ℝ) * t ≤ Real.log (Δ / (8 * ε)) / 2) :
    8 * ε * Real.exp ((m : ℝ) * t) ≤ Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hD : 0 < Δ / (8 * ε) := by positivity
  have hD1 : 1 ≤ Δ / (8 * ε) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hl : 0 ≤ Real.log (Δ / (8 * ε)) := Real.log_nonneg hD1
  have he := Real.exp_le_exp.mpr (show (m : ℝ) * t ≤ Real.log (Δ / (8 * ε)) by linarith)
  rw [Real.exp_log hD] at he
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 8 * ε by positivity)
  have hx : 8 * ε * (Δ / (8 * ε)) = Δ := by field_simp
  exact hh.trans_eq hx

end LongTails.Proofs.GapCalibratedWeights
