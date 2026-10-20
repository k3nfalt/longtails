import LongTails.Proofs.LoraObjective

namespace LongTails.Proofs.LoraErrorBounds

open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraGeometry
open LongTails.Proofs.LoraFactorRepair
open scoped RealInnerProductSpace

lemma repair_gap {m n r : ℕ} (x c : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n} {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s)
    (hstrong : ∀ X Y, f X + ⟪G X, Y - X⟫ + μ / 2 * ‖Y - X‖ ^ 2 ≤ f Y)
    (hzero : G (product c) = 0)
    (hB : ∀ w, s * ‖w‖ ≤ ‖leftAction c w‖)
    (hA : ∀ w, s * ‖w‖ ≤ ‖rightTransposeAction c w‖)
    (hclose : ‖x - c‖ ≤ s / 2) :
    ∃ z : Factors m n r, product z = product c ∧
      (μ * s ^ 2 / 8) * ‖x - z‖ ^ 2 ≤ μ * ‖product x - product c‖ ^ 2 ∧
      (μ * s ^ 2 / 8) * ‖x - z‖ ^ 2 ≤ 2 * (f (product x) - f (product c)) := by
  obtain ⟨z, hz, hd⟩ := factor_repair x c hs hB hA hclose
  have hgap := hstrong (product c) (product x)
  rw [hzero, inner_zero_left, add_zero] at hgap
  have hscaled := mul_le_mul_of_nonneg_left hd (show 0 ≤ μ / 8 by positivity)
  refine ⟨z, hz, ?_, ?_⟩ <;> nlinarith

lemma repair_alignment {m n r : ℕ} (x z c : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n} {μ α : ℝ}
    (hα : 0 ≤ α)
    (hstrong : ∀ X Y, f X + ⟪G X, Y - X⟫ + μ / 2 * ‖Y - X‖ ^ 2 ≤ f Y)
    (hz : product z = product c)
    (hd : α * ‖x - z‖ ^ 2 ≤ μ * ‖product x - product c‖ ^ 2)
    (hM : ‖G (product x)‖ ≤ α) :
    f (product x) - f (product c) ≤ ⟪pullback x (G (product x)), x - z⟫ := by
  have hs := hstrong (product x) (product c)
  rw [show product c - product x = -(product x - product c) by abel,
    inner_neg_right, norm_neg] at hs
  have hrem := LongTails.Proofs.LoraLocalInterpolation.remainder_inner_bound hα
    (show ‖-G (product x)‖ ≤ α by simpa using hM) (product_norm (x - z))
  rw [inner_neg_left] at hrem
  rw [pullback_inner, linearization_repair, hz, inner_add_right]
  nlinarith

lemma gradient_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g d : E) {α e : ℝ} (hα : 0 < α) (he : 0 ≤ e)
    (hd : α * ‖d‖ ^ 2 ≤ 2 * e) (hi : e ≤ ⟪g, d⟫) : α * e ≤ 2 * ‖g‖ ^ 2 := by
  have hc := hi.trans (real_inner_le_norm g d)
  have hc2 := pow_le_pow_left₀ he hc 2
  have h1 := mul_le_mul_of_nonneg_left hc2 (le_of_lt hα)
  have h2 := mul_le_mul_of_nonneg_left hd (sq_nonneg ‖g‖)
  by_cases hz : e = 0
  · simp [hz]
  · have hep : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    nlinarith

lemma local_gradient_domination {m n r : ℕ} (x c : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n} {μ s : ℝ}
    (hμ : 0 < μ) (hs : 0 < s)
    (hstrong : ∀ X Y, f X + ⟪G X, Y - X⟫ + μ / 2 * ‖Y - X‖ ^ 2 ≤ f Y)
    (hzero : G (product c) = 0)
    (hB : ∀ w, s * ‖w‖ ≤ ‖leftAction c w‖)
    (hA : ∀ w, s * ‖w‖ ≤ ‖rightTransposeAction c w‖)
    (hclose : ‖x - c‖ ≤ s / 2) (hM : ‖G (product x)‖ ≤ μ * s ^ 2 / 8) :
    (μ * s ^ 2 / 8) * (f (product x) - f (product c)) ≤
      2 * ‖pullback x (G (product x))‖ ^ 2 := by
  obtain ⟨z, hz, hd, hg⟩ := repair_gap x c hμ hs hstrong hzero hB hA hclose
  have hα : 0 < μ * s ^ 2 / 8 := by positivity
  have he : 0 ≤ f (product x) - f (product c) := by
    have hh := hstrong (product c) (product x)
    rw [hzero, inner_zero_left, add_zero] at hh
    nlinarith [sq_nonneg ‖product x - product c‖]
  exact gradient_domination _ _ hα he hg
    (repair_alignment x z c (le_of_lt hα) hstrong hz hd hM)

end LongTails.Proofs.LoraErrorBounds
