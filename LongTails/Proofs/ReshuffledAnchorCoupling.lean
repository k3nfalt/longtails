import LongTails.Proofs.CyclicGradientStep

open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledAnchorCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma inner_young {η : ℝ} (hη : 0 < η) (u v : E) :
    ⟪u, v⟫ ≤ η * ‖u‖ ^ 2 + ‖v‖ ^ 2 / (4 * η) := by
  have hs := sq_nonneg ‖(2 * η) • u - v‖
  rw [norm_sub_sq_real] at hs
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at hs
  have hd : ⟪u, v⟫ ≤ (η * ‖u‖ ^ 2 * (4 * η) + ‖v‖ ^ 2) / (4 * η) :=
    (le_div_iff₀ (by positivity : 0 < 4 * η)).2 (by nlinarith)
  convert hd using 1; field_simp

lemma reverse_loss_difference {f : E → ℝ} {g : E → E} {η a : ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hη : 0 < η) (x x' : E) (hx : ‖x' - x‖ ≤ η * a) :
    f x - f x' ≤ η * ‖g x‖ ^ 2 + η * a ^ 2 / 4 := by
  have hc' := Gradient.convex_support hc hg x x'
  have hy := inner_young hη (g x) (x - x')
  rw [show x - x' = -(x' - x) by abel, inner_neg_right, norm_neg] at hy
  have hxx := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hdx := div_le_div_of_nonneg_right hxx (by positivity : 0 ≤ 4 * η)
  have he : (η * a) ^ 2 / (4 * η) = η * a ^ 2 / 4 := by field_simp
  rw [he] at hdx
  linarith

lemma coupled_loss_difference {f : E → ℝ} {g : E → E} {L η a : ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hη : 0 < η) (hstep : η * L ≤ 1 / 6)
    (x x' z z' : E) (hx : ‖x' - x‖ ≤ η * a) (hz : ‖z' - z‖ ≤ η * a) :
    f x' - f x + f z - f z' ≤
      η * ‖g x‖ ^ 2 + η * ‖g z‖ ^ 2 + (7 / 12 : ℝ) * η * a ^ 2 := by
  have hu := Gradient.smooth_upper_bound hg hlip x x'
  have hc' := Gradient.convex_support hc hg z z'
  have hyx := inner_young hη (g x) (x' - x)
  have hyz := inner_young hη (g z) (z - z')
  rw [show z - z' = -(z' - z) by abel, inner_neg_right, norm_neg] at hyz
  have hxx := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hzz := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hdx := div_le_div_of_nonneg_right hxx (by positivity : 0 ≤ 4 * η)
  have hdz := div_le_div_of_nonneg_right hzz (by positivity : 0 ≤ 4 * η)
  have hlx := mul_le_mul_of_nonneg_left hxx (by positivity : 0 ≤ L / 2)
  have he : (η * a) ^ 2 / (4 * η) = η * a ^ 2 / 4 := by field_simp
  rw [he] at hdx hdz
  have hh := mul_le_mul_of_nonneg_right hstep (by positivity : 0 ≤ η * a ^ 2 / 2)
  nlinarith

lemma step_nonexpansive {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hη : 0 < η) (hstep : η * L ≤ 1) (x y : E) :
    ‖(x - η • g x) - (y - η • g y)‖ ≤ ‖x - y‖ := by
  have hL : L ≤ 1 / η := (le_div_iff₀ hη).2 (by linarith)
  have hlip' : ∀ x y, ‖g x - g y‖ ≤ (1 / η) * ‖x - y‖ := fun x y =>
    (hlip x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have h := CyclicInterpolation.step_firm (one_div_pos.mpr hη) hc hg hlip' x y
  simp only [one_div_one_div] at h
  nlinarith [sq_nonneg ‖η • g x - η • g y‖,
    norm_nonneg ((x - η • g x) - (y - η • g y)), norm_nonneg (x - y)]

end OracleTemplate.ReshuffledAnchorCoupling
