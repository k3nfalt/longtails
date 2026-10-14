import LongTails.Proofs.ReshuffledEpoch
import LongTails.Proofs.ReshuffledAnchorCoupling
import LongTails.Proofs.AcceleratedFiniteSum

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledCentered

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def loss (f : E → ℝ) (g : E → E) (z x : E) : ℝ :=
  f x - f z - ⟪g z, x - z⟫

lemma loss_nonneg {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x) (z x : E) :
    0 ≤ loss f g z x := by
  have h := Gradient.convex_support hc hg z x
  unfold loss
  linarith

omit [CompleteSpace E] in
lemma loss_self (f : E → ℝ) (g : E → E) (z : E) : loss f g z z = 0 := by simp [loss]

omit [CompleteSpace E] in
lemma loss_convex {f : E → ℝ} {g : E → E} (hc : ConvexOn ℝ Set.univ f) (z : E) :
    ConvexOn ℝ Set.univ (loss f g z) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hc.2 hx hy ha hb hab
  change f (a • x + b • y) - f z - ⟪g z, a • x + b • y - z⟫ ≤
    a * (f x - f z - ⟪g z, x - z⟫) + b * (f y - f z - ⟪g z, y - z⟫)
  simp only [inner_sub_right, inner_add_right, inner_smul_right]
  change f (a • x + b • y) ≤ a * f x + b * f y at h
  linear_combination h + (f z - ⟪g z, z⟫) * hab

lemma loss_grad {f : E → ℝ} {g : E → E} (hg : ∀ x, HasGradientAt f (g x) x) (z x : E) :
    HasGradientAt (loss f g z) (g x - g z) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin := HasFDerivAt.inner ℝ (hasFDerivAt_const (g z) x)
    ((hasFDerivAt_id x).sub_const z)
  convert ((hg x).hasFDerivAt.sub_const (f z)).sub hlin using 1
  · funext y
    rfl
  · ext v
    simp [fderivInnerCLM_apply]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma loss_lip {g : E → E} {L : ℝ}
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z x y : E) :
    ‖(g x - g z) - (g y - g z)‖ ≤ L * ‖x - y‖ := by simpa using hlip x y

lemma centered_grad_sq {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z x : E) :
    ‖g x - g z‖ ^ 2 ≤ 2 * L * loss f g z x :=
  SampledConvex.cocoercive hL hc hg hlip x z

lemma grad_sq {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (z x : E) :
    ‖g x‖ ^ 2 ≤ 4 * L * loss f g z x + 2 * ‖g z‖ ^ 2 := by
  have hc' := centered_grad_sq hL hc hg hlip z x
  have ht : ‖g x‖ ≤ ‖g x - g z‖ + ‖g z‖ := by
    simpa using norm_add_le (g x - g z) (g z)
  nlinarith [sq_nonneg (‖g x - g z‖ - ‖g z‖), norm_nonneg (g x),
    norm_nonneg (g x - g z), norm_nonneg (g z)]

omit [CompleteSpace E] in
lemma step_identity (f : E → ℝ) (g : E → E) (η : ℝ) (x z : E) :
    ‖x - η • g x - z‖ ^ 2 = ‖x - z‖ ^ 2 - 2 * η * (f x - f z) +
      η ^ 2 * ‖g x‖ ^ 2 - 2 * η * loss f g x z := by
  rw [show x - η • g x - z = (x - z) - η • g x by module, norm_sub_sq_real]
  simp only [loss, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [show z - x = -(x - z) by module, inner_neg_right, real_inner_comm]
  ring

lemma next_gap {f : E → ℝ} {g : E → E} {L η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {xstar : E}
    (hmin : IsMinOn f Set.univ xstar) (x v : E) :
    f (x - η • v) - f xstar ≤ f x - f xstar + η * L * (f x - f xstar) +
      η / 2 * (1 + η * L) * ‖v‖ ^ 2 := by
  have hu := Gradient.smooth_upper_bound hg hlip x (x - η • v)
  have hg2 := CyclicInterpolation.grad_sq_le hL hc hg hlip hmin x
  have hi := ReshuffledAnchorCoupling.inner_young (by norm_num : (0 : ℝ) < 1 / 2) (g x) (-v)
  simp only [inner_neg_right, norm_neg] at hi
  rw [show x - η • v - x = -(η • v) by module] at hu
  simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hu
  have hi' := mul_le_mul_of_nonneg_left hi hη
  have hg2' := mul_le_mul_of_nonneg_left hg2 (show 0 ≤ η / 2 by positivity)
  nlinarith

variable {n : ℕ} [NeZero n] {f : Fin n → E → ℝ} {g : Fin n → E → E}
  {ℓ : Fin n → ℝ} {Lavg Lmax σ : ℝ} {xstar : E}

lemma sum_loss (h : ReshuffledConvex.Hyp f g ℓ Lavg Lmax σ xstar) (x : E) :
    ∑ i, loss (f i) (g i) xstar x = n * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
  simp only [loss, sum_sub_distrib, ← sum_inner, h.sum_star, inner_zero_left, sub_zero]
  rw [ReshuffledConvex.sum_objective f x, ReshuffledConvex.sum_objective f xstar]
  ring

lemma objective_next_gap (h : ReshuffledConvex.Hyp f g ℓ Lavg Lmax σ xstar)
    {η : ℝ} (hη : 0 ≤ η) (x v : E) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective f (x - η • v) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar +
      η * Lmax * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
      η / 2 * (1 + η * Lmax) * ‖v‖ ^ 2 :=
  next_gap h.lmax_pos hη (FiniteSum.objective_convex h.convex)
    (FiniteSum.objective_gradient (oracle := fun q => g q.1 q.2) h.grad)
    (FiniteSum.fullGradient_lipschitz (g := fun q => g q.1 q.2) h.lip_max) h.min x v

end OracleTemplate.ReshuffledCentered
