import LongTails.Proofs.LinearDecaySgdStep

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SamCocoercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_cocoercive {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖g y - g x‖ ^ 2 ≤ L * ⟪g y - g x, y - x⟫ := by
  have h1 := OracleTemplate.SampledConvex.cocoercive hL hc hg hlip y x
  have h2 := OracleTemplate.SampledConvex.cocoercive hL hc hg hlip x y
  rw [norm_sub_rev (g x) (g y), ← neg_sub y x, inner_neg_right] at h2
  rw [inner_sub_left]
  linarith

lemma perturbation_cocoercive {f : E → ℝ} {g : E → E} {L ρ : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖g (x + (ρ / ‖g x‖) • g x) - g x‖ ^ 2 ≤
      (L * ρ / ‖g x‖) * ⟪g x, g (x + (ρ / ‖g x‖) • g x) - g x⟫ := by
  have h := gradient_cocoercive hL hc hg hlip x (x + (ρ / ‖g x‖) • g x)
  simpa only [add_sub_cancel_left, inner_smul_right, real_inner_comm,
    mul_div_assoc, mul_assoc] using h

lemma perturbed_descent {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x e : E) :
    f (x - η • (g x + e)) ≤ f x - η * ‖g x‖ ^ 2 - η * ⟪g x, e⟫ +
      L * η ^ 2 / 2 * (‖g x‖ ^ 2 + 2 * ⟪g x, e⟫ + ‖e‖ ^ 2) := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - η • (g x + e))
  have he : x - η • (g x + e) - x = -η • (g x + e) := by module
  rw [he, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq, norm_add_sq_real] at h
  convert h using 1
  ring

lemma descent_algebra {L η ρ a b c : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hstep : 2 * L * η ≤ 1)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hco : a * c ≤ L * ρ * b) (hlarge : η * L ^ 2 * ρ ≤ a) :
    -η * a ^ 2 - η * b + L * η ^ 2 / 2 * (a ^ 2 + 2 * b + c) ≤
      -η / 2 * a ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_left hco (show 0 ≤ η * L by positivity)
  have h2 := mul_le_mul_of_nonneg_right hlarge hb
  have h3 : η * L * c ≤ b := by
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith [h1, h2]
  have h4 := mul_le_mul_of_nonneg_left h3 hη
  have h5 := mul_le_mul_of_nonneg_right hstep (show 0 ≤ η * a ^ 2 by positivity)
  have h6 := mul_le_mul_of_nonneg_right hstep (show 0 ≤ η * b by positivity)
  nlinarith

lemma large_gradient_descent {f : E → ℝ} {g : E → E} {L η ρ : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hρ : 0 < ρ) (hstep : 2 * L * η ≤ 1)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E)
    (hpos : 0 < ‖g x‖) (hlarge : η * L ^ 2 * ρ ≤ ‖g x‖) :
    f (x - η • g (x + (ρ / ‖g x‖) • g x)) ≤ f x - η / 2 * ‖g x‖ ^ 2 := by
  let e := g (x + (ρ / ‖g x‖) • g x) - g x
  have hco := perturbation_cocoercive (ρ := ρ) hL hc hg hlip x
  change ‖e‖ ^ 2 ≤ (L * ρ / ‖g x‖) * ⟪g x, e⟫ at hco
  have hb : 0 ≤ ⟪g x, e⟫ := by
    have : 0 ≤ (L * ρ / ‖g x‖) * ⟪g x, e⟫ := (sq_nonneg _).trans hco
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < L * ρ / ‖g x‖)).mp this
  have hco' : ‖g x‖ * ‖e‖ ^ 2 ≤ L * ρ * ⟪g x, e⟫ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos] at hco
    nlinarith
  have ha := descent_algebra hL hη hstep hpos hb hco' hlarge
  have hd := perturbed_descent (η := η) hg hlip x e
  have he : g x + e = g (x + (ρ / ‖g x‖) • g x) := by dsimp [e]; abel
  rw [he] at hd
  linarith

end LongTails.Proofs.SamCocoercive
