import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace LongTails.Proofs.OptimumHeterogeneityGeometry

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def remainder (f : E → ℝ) (g z x : E) : ℝ := f x - f z - ⟪g, x - z⟫

lemma remainder_bounds {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z x : E) :
    0 ≤ remainder f (g z) z x ∧ remainder f (g z) z x ≤ L * (‖x - z‖ ^ 2 / 2) := by
  have h₁ := OracleTemplate.Gradient.convex_support hc hg z x
  have h₂ := OracleTemplate.Gradient.smooth_upper_bound hg hl z x
  unfold remainder
  constructor <;> linarith

omit [CompleteSpace E] in
lemma balanced_offset (w : ι → ℝ) (g : ι → E) (c : ℝ) (hg : ∑ i, g i = 0) :
    ‖∑ i, w i • g i‖ ≤ Real.sqrt (∑ i, (w i - c) ^ 2) * Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  have he : ∑ i, (w i - c) • g i = ∑ i, w i • g i := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hg, smul_zero, sub_zero]
  calc
    ‖∑ i, w i • g i‖ = ‖∑ i, (w i - c) • g i‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖(w i - c) • g i‖ := norm_sum_le _ _
    _ = ∑ i, |w i - c| * ‖g i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => |w i - c|) (fun i => ‖g i‖)

omit [CompleteSpace E] in
lemma remainder_sum (f : ι → E → ℝ) (g : ι → E) (hg : ∑ i, g i = 0) (z x : E) :
    ∑ i, remainder (f i) (g i) z x = ∑ i, (f i x - f i z) := by
  simp only [remainder, Finset.sum_sub_distrib, ← sum_inner, hg, inner_zero_left, sub_zero]

lemma weighted_radial (f : ι → E → ℝ) (g : ι → E → E) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x) (z x : E) :
    ∑ i, w i * remainder (f i) (g i z) z x ≤
      ⟪∑ i, w i • (g i x - g i z), x - z⟫ := by
  simp only [sum_inner, real_inner_smul_left, inner_sub_left]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  have hi := OracleTemplate.Gradient.convex_support (hc i) (hg i) x z
  rw [← neg_sub x z, inner_neg_right] at hi
  unfold remainder
  linarith

end LongTails.Proofs.OptimumHeterogeneityGeometry
