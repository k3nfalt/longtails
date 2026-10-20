import LongTails.Proofs.LoraFactorRepair
import LongTails.Proofs.FrankWolfeDescent

namespace LongTails.Proofs.LoraObjective

open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraGeometry
open Set InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma support_convex {f : E → ℝ} {g : E → E}
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ ≤ f y) : ConvexOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (hs z x) ha
  have hy := mul_le_mul_of_nonneg_left (hs z y) hb
  have he : a * ⟪g z, x - z⟫ + b * ⟪g z, y - z⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hz : a • (x - z) + b • (y - z) = 0 := by
      calc
        a • (x - z) + b • (y - z) = (a • x + b • y) - (a + b) • z := by module
        _ = 0 := by rw [hab, one_smul]; exact sub_self z
    rw [hz, inner_zero_right]
  have hz : a * f z + b * f z = f z := by rw [← add_mul, hab, one_mul]
  change f z ≤ a * f x + b * f y
  nlinarith

lemma self_bound {f : E → ℝ} {g : E → E} {ρ : ℝ} {u : E}
    (hρ : 0 < ρ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ ρ * ‖x - y‖)
    (hmin : IsMinOn f univ u) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * ρ * (f x - f u) := by
  have hd := OracleTemplate.Gradient.descent hρ hg hlip x
  have hm : f u ≤ f (x - (1 / ρ) • g x) := hmin (mem_univ _)
  have hh : ‖g x‖ ^ 2 / (2 * ρ) ≤ f x - f u := by linarith
  have hh' := (div_le_iff₀ (show 0 < 2 * ρ by positivity)).mp hh
  nlinarith

lemma gradient_min_zero {f : E → ℝ} {g : E → E} {ρ : ℝ} {u : E}
    (hρ : 0 < ρ) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ ρ * ‖x - y‖)
    (hmin : IsMinOn f univ u) : g u = 0 := by
  have hh := self_bound hρ hg hlip hmin u
  have hz : ‖g u‖ = 0 := by nlinarith [norm_nonneg (g u)]
  exact norm_eq_zero.mp hz

lemma product_lipschitz_ball {m n r : ℕ} (u v c : Factors m n r) {R s : ℝ}
    (hR : 0 ≤ R) (_hs : 0 ≤ s) (hsR : s ≤ R)
    (hc : ∀ h, ‖linearization c h‖ ≤ R * ‖h‖)
    (hu : ‖u - c‖ ≤ s / 2) (hv : ‖v - c‖ ≤ s / 2) :
    ‖product u - product v‖ ≤ 2 * R * ‖u - v‖ := by
  have hD := derivative_local_bound v c hc hR hv
  have hd : ‖u - v‖ ≤ s := by
    have hh := norm_add_le (u - c) (c - v)
    rw [sub_add_sub_cancel, norm_sub_rev c v] at hh
    linarith
  have hh := product_local_bound u v (fun h =>
    (derivative v).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg h)))
  have hsq := mul_le_mul_of_nonneg_right hd (norm_nonneg (u - v))
  have hsr := mul_le_mul_of_nonneg_right hsR (norm_nonneg (u - v))
  nlinarith

lemma outer_gradient_ball {m n r : ℕ} (u c : Factors m n r)
    (G : MatrixSpace m n → MatrixSpace m n) {ρ R s : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsR : s ≤ R)
    (hc : ∀ h, ‖linearization c h‖ ≤ R * ‖h‖)
    (hu : ‖u - c‖ ≤ s / 2) (hzero : G (product c) = 0)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖) :
    ‖G (product u)‖ ≤ ρ * R ^ 2 := by
  have hh := hlip (product u) (product c)
  rw [hzero, sub_zero] at hh
  have hp := product_lipschitz_ball u c c hR hs hsR hc hu (by simp; positivity)
  have hprod : ‖product u - product c‖ ≤ R ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * R by positivity)
    have hsr := mul_le_mul_of_nonneg_left hsR hR
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left hprod hρ)

lemma objective_lipschitz_ball {m n r : ℕ} (u v c : Factors m n r)
    (G : MatrixSpace m n → MatrixSpace m n) {ρ R s : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsR : s ≤ R)
    (hc : ∀ h, ‖linearization c h‖ ≤ R * ‖h‖)
    (hu : ‖u - c‖ ≤ s / 2) (hv : ‖v - c‖ ≤ s / 2)
    (hzero : G (product c) = 0)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖) :
    ‖pullback u (G (product u)) - pullback v (G (product v))‖ ≤
      (8 * ρ * R ^ 2) * ‖u - v‖ := by
  rw [pullback_adjoint, pullback_adjoint]
  have hDu : ‖derivative u‖ ≤ 2 * R :=
    (derivative_local_bound u c hc hR hu).trans (by linarith)
  have hM := outer_gradient_ball v c G hρ hR hs hsR hc hv hzero hlip
  have hh := LongTails.Proofs.LoraLocalInterpolation.adjoint_gradient_difference
    (derivative u) (derivative v) (G (product u)) (G (product v))
    hDu (derivative_difference_norm u v) hM (norm_nonneg (u - v))
  have hp := product_lipschitz_ball u v c hR hs hsR hc hu hv
  have hgp := (hlip (product u) (product v)).trans (mul_le_mul_of_nonneg_left hp hρ)
  have hscaled := mul_le_mul_of_nonneg_left hgp (show 0 ≤ 2 * R by positivity)
  have hn : 0 ≤ ρ * R ^ 2 * ‖u - v‖ := by positivity
  nlinarith

lemma objective_upper_ball {m n r : ℕ} (u v c : Factors m n r)
    {f : MatrixSpace m n → ℝ} {G : MatrixSpace m n → MatrixSpace m n} {ρ R s : ℝ}
    (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsR : s ≤ R)
    (hc : ∀ h, ‖linearization c h‖ ≤ R * ‖h‖)
    (hu : ‖u - c‖ ≤ s / 2) (hv : ‖v - c‖ ≤ s / 2)
    (hzero : G (product c) = 0) (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ ρ * ‖x - y‖) :
    f (product v) ≤ f (product u) + ⟪pullback u (G (product u)), v - u⟫ +
      (8 * ρ * R ^ 2) / 2 * ‖v - u‖ ^ 2 := by
  apply OracleTemplate.FrankWolfe.smooth_upper_bound_on
    (convex_closedBall c (s / 2))
    (fun x _ => objective_hasGradientAt x (G (product x)) (hg _))
    (fun x hx y hy => objective_lipschitz_ball x y c G hρ hR hs hsR hc
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy) hzero hlip)
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
  · simpa only [Metric.mem_closedBall, dist_eq_norm] using hv

end LongTails.Proofs.LoraObjective
