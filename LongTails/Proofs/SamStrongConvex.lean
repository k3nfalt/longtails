import LongTails.Proofs.SamCocoercive
import LongTails.Algorithms.NormalizedSam

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SamStrongConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma support_convex {f : E → ℝ} {g : E → E}
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ ≤ f y) : ConvexOn ℝ univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  let z := a • x + b • y
  have h1 := mul_le_mul_of_nonneg_left (hs z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hs z y) hb
  have he : a • (x-z) + b • (y-z) = 0 := by
    calc
      _ = z - (a+b) • z := by dsimp [z]; module
      _ = 0 := by rw [hab, one_smul, sub_self]
  have hi : a * ⟪g z, x-z⟫ + b * ⟪g z, y-z⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, he, inner_zero_right]
  have hf : a*f z+b*f z=f z := by rw [← add_mul, hab, one_mul]
  change f z ≤ a*f x+b*f y
  linarith

omit [CompleteSpace E] in
lemma strong_convex {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 ≤ μ)
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y) : ConvexOn ℝ univ f := by
  apply support_convex (g := g)
  intro x y
  have hn : 0 ≤ μ/2*‖y-x‖^2 := by positivity
  linarith [hs x y]

omit [CompleteSpace E] in
lemma pl {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y) (x xs : E) :
    2*μ*(f x-f xs) ≤ ‖g x‖^2 := by
  have h := hs x xs
  rw [← neg_sub x xs, inner_neg_right, norm_neg] at h
  have hc := real_inner_le_norm (g x) (x-xs)
  have hm := mul_le_mul_of_nonneg_left h hμ.le
  have hn := mul_le_mul_of_nonneg_left hc hμ.le
  nlinarith [sq_nonneg (‖g x‖-μ*‖x-xs‖)]

omit [CompleteSpace E] in
lemma perturbation_norm {g : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) :
    ‖(ρ/‖g x‖) • g x‖ ≤ ρ := by
  by_cases hz : ‖g x‖ = 0
  · simp [hz, hρ]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ (norm_nonneg _)),
      div_mul_cancel₀ ρ hz]

omit [CompleteSpace E] in
lemma perturbed_gradient_norm {g : E → E} {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x : E) :
    ‖g (x+(ρ/‖g x‖) • g x)‖ ≤ ‖g x‖+L*ρ := by
  have h := hl (x+(ρ/‖g x‖) • g x) x
  rw [add_sub_cancel_left] at h
  have hp := mul_le_mul_of_nonneg_left (perturbation_norm (g := g) hρ x) hL
  have hn := norm_add_le (g (x+(ρ/‖g x‖) • g x)-g x) (g x)
  rw [sub_add_cancel] at hn
  linarith

omit [CompleteSpace E] in
lemma next_gradient_norm {g : E → E} {L ρ η : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hη : 0 ≤ η) (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x : E) :
    ‖g (LongTails.Algorithms.NormalizedSam.step g η ρ x)‖ ≤
      (1+L*η)*‖g x‖+η*L^2*ρ := by
  let y := LongTails.Algorithms.NormalizedSam.step g η ρ x
  have h := hl y x
  have he : y-x = -η • g (x+(ρ/‖g x‖) • g x) := by
    dsimp [y, LongTails.Algorithms.NormalizedSam.step]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη] at h
  have hp := mul_le_mul_of_nonneg_left (perturbed_gradient_norm hL hρ hl x)
    (mul_nonneg hL hη)
  have hn := norm_add_le (g y-g x) (g x)
  rw [sub_add_cancel] at hn
  change ‖g y‖ ≤ _
  nlinarith

omit [CompleteSpace E] in
lemma small_gradient_gap {f : E → ℝ} {g : E → E} {L ρ η μ : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hμ : 0 < μ)
    (hstep : 2*L*η ≤ 1)
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x xs : E)
    (hsmall : ‖g x‖ ≤ η*L^2*ρ) :
    f (LongTails.Algorithms.NormalizedSam.step g η ρ x)-f xs ≤ 4*η^2*L^4*ρ^2/μ := by
  let A := η*L^2*ρ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnext := next_gradient_norm hL.le hρ hη hl x
  have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 1+L*η)
  have hstepA := mul_le_mul_of_nonneg_right hstep hA
  have hn : ‖g (LongTails.Algorithms.NormalizedSam.step g η ρ x)‖ ≤ 5/2*A := by
    dsimp [A] at *
    nlinarith
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 5/2*A)).mpr hn
  have hp := pl hμ hs (LongTails.Algorithms.NormalizedSam.step g η ρ x) xs
  apply (le_div_iff₀ hμ).mpr
  dsimp [A] at hsq
  nlinarith [sq_nonneg (η*L^2*ρ)]

lemma step_gap {f : E → ℝ} {g : E → E} {L ρ η μ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hη : 0 < η) (hμ : 0 < μ)
    (hstep : 2*L*η ≤ 1)
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x xs : E) :
    f (LongTails.Algorithms.NormalizedSam.step g η ρ x)-f xs ≤
      max ((1-μ*η)*(f x-f xs)) (4*η^2*L^4*ρ^2/μ) := by
  by_cases hsmall : ‖g x‖ ≤ η*L^2*ρ
  · exact (small_gradient_gap hL hρ.le hη.le hμ hstep hs hl x xs hsmall).trans (le_max_right _ _)
  · have hlarge := (lt_of_not_ge hsmall).le
    have hpos : 0 < ‖g x‖ := lt_of_lt_of_le (by positivity) hlarge
    have hd := SamCocoercive.large_gradient_descent hL hη.le hρ hstep
      (strong_convex hμ.le hs) hg hl x hpos hlarge
    have hp := mul_le_mul_of_nonneg_left (pl hμ hs x xs) hη.le
    apply le_trans _ (le_max_left _ _)
    change f (x-η • g (x+(ρ/‖g x‖) • g x))-f xs ≤ _
    nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma max_contraction {q C Δ : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (a : ℕ → ℝ) (ha : a 0 ≤ Δ) (hs : ∀ k, a (k+1) ≤ max (q*a k) C) (T : ℕ) :
    a T ≤ max (q^T*Δ) C := by
  induction T with
  | zero => simpa using ha.trans (le_max_left Δ C)
  | succ k ih =>
    apply (hs k).trans
    apply max_le
    · have h := mul_le_mul_of_nonneg_left ih hq
      rw [mul_max_of_nonneg _ _ hq] at h
      apply h.trans
      apply max_le
      · apply le_of_eq_of_le _ (le_max_left _ _)
        rw [pow_succ]
        ring
      · exact (mul_le_of_le_one_left hC hq1).trans (le_max_right _ _)
    · exact le_max_right _ _

lemma output_gap {f : E → ℝ} {g : E → E} {L ρ η μ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hη : 0 < η) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hstep : 2*L*η ≤ 1)
    (hs : ∀ x y, f x + ⟪g x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x xs : E) (T : ℕ) :
    f (LongTails.Algorithms.NormalizedSam.output g η ρ x T)-f xs ≤
      max ((1-μ*η)^T*(f x-f xs)) (4*η^2*L^4*ρ^2/μ) := by
  have hq : 0 ≤ 1-μ*η := by nlinarith [mul_le_mul_of_nonneg_right hμL hη.le]
  have hq1 : 1-μ*η ≤ 1 := by nlinarith [mul_pos hμ hη]
  apply max_contraction hq hq1 (by positivity)
    (fun k => f (LongTails.Algorithms.NormalizedSam.output g η ρ x k)-f xs) (by rfl)
  intro k
  simpa only [LongTails.Algorithms.NormalizedSam.output, Function.iterate_succ_apply'] using
    step_gap hL hρ hη hμ hstep hs hg hl
      (LongTails.Algorithms.NormalizedSam.output g η ρ x k) xs

end LongTails.Proofs.SamStrongConvex
