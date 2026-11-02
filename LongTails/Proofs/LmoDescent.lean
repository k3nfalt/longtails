import LongTails.Proofs.NormBallGeometry
import LongTails.Proofs.LmoTrajectory

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormBallLMO

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem ConstrainedProblem State lmoMethod uscg scg
  constantMomentum vanishingMomentum)

variable {d : ℕ} {N : Seminorm ℝ (Space d)}

lemma unit_bound_of_radius {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (h : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂) :
    ∀ v, N v ≤ 1 → ‖v‖ ≤ ρ₂ / ρ := by
  intro v hv
  have hN : N (ρ • v) ≤ ρ := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hρ]; nlinarith
  have := h _ hN
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at this
  rw [le_div_iff₀ hρ]; linarith

lemma unit_bound_of_diameter {ρ D₂ : ℝ} (hρ : 0 < ρ)
    (h : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂) : ∀ v, N v ≤ 1 → ‖v‖ ≤ D₂ / ρ := by
  refine unit_bound_of_radius hρ fun x hx => ?_
  have := h x 0 hx (by simp; linarith)
  simpa using this

lemma uscg_step {f : Space d → ℝ} {L ρ ρ₂ ζ γ : ℝ} {lmo : Space d → Space d}
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hρ₂ : ∀ x, N x ≤ ρ → ‖x‖ ≤ ρ₂) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y)) (hL : 0 ≤ L)
    (hγ : 0 ≤ γ) (x m : Space d) :
    γ * ρ * dualNorm N (gradient f x) ≤
      f x - f (x + γ • lmo m) + γ * (ρ₂ + ζ * ρ) * ‖m - gradient f x‖ + L * γ ^ 2 * ρ ^ 2 / 2 := by
  open scoped RealInnerProductSpace in
  (
    have hR := unit_bound_of_radius hρ hρ₂
    have hdesc := descent hR hdef hgrad hlip x (x + γ • lmo m)
    rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ,
      inner_smul_right] at hdesc
    have hNl := hlmo.feasible m
    have hNl2 : (γ * N (lmo m)) ^ 2 ≤ (γ * ρ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hγ (apply_nonneg N _)) (mul_le_mul_of_nonneg_left hNl hγ) 2
    have hlmo2 : ‖lmo m‖ ≤ ρ₂ := hρ₂ _ hNl
    have hsplit : ⟪gradient f x, lmo m⟫ = ⟪gradient f x - m, lmo m⟫ + ⟪m, lmo m⟫ := by
      rw [inner_sub_left]; ring
    have hcs : ⟪gradient f x - m, lmo m⟫ ≤ ‖m - gradient f x‖ * ρ₂ := by
      calc ⟪gradient f x - m, lmo m⟫ ≤ ‖gradient f x - m‖ * ‖lmo m‖ := real_inner_le_norm _ _
        _ ≤ ‖m - gradient f x‖ * ρ₂ := by
            rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hlmo2 (norm_nonneg _)
    have hl := lmo_dualNorm hρ hlmo m
    have htri := dualNorm_sub_le hR (gradient f x) m
    have hz := hζ (gradient f x - m)
    rw [norm_sub_rev] at hz
    have hinner : ⟪gradient f x, lmo m⟫ ≤ (ρ₂ + ζ * ρ) * ‖m - gradient f x‖ - ρ * dualNorm N (gradient f x) := by
      nlinarith
    have hγi := mul_le_mul_of_nonneg_left hinner hγ
    have hL2 : L / 2 * (γ * N (lmo m)) ^ 2 ≤ L / 2 * (γ * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left hNl2 (by linarith)
    nlinarith)

lemma scg_feasible {ρ γ : ℝ} {x l : Space d} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hx : N x ≤ ρ)
    (hl : N l ≤ ρ) : N ((1 - γ) • x + γ • l) ≤ ρ := by
  calc N ((1 - γ) • x + γ • l) ≤ N ((1 - γ) • x) + N (γ • l) := map_add_le_add N _ _
    _ = (1 - γ) * N x + γ * N l := by
        rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hγ0]
    _ ≤ (1 - γ) * ρ + γ * ρ := by
        have : 0 ≤ 1 - γ := by linarith
        gcongr
    _ = ρ := by ring

lemma ball_convex (ρ : ℝ) : Convex ℝ {x : Space d | N x ≤ ρ} := by
  have h := N.convex_closedBall 0 ρ
  have e : N.closedBall 0 ρ = {x : Space d | N x ≤ ρ} := by
    ext x; simp [Seminorm.mem_closedBall]
  rwa [e] at h

lemma scg_step {f : Space d → ℝ} {L ρ D₂ γ : ℝ} {lmo : Space d → Space d}
    (hdef : ∀ x, N x = 0 → x = 0) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo)
    (hD₂ : ∀ x y, N x ≤ ρ → N y ≤ ρ → ‖x - y‖ ≤ D₂)
    (hgrad : ∀ x, N x ≤ ρ → HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, N x ≤ ρ → N y ≤ ρ → dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (hL : 0 ≤ L) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {x : Space d} (hx : N x ≤ ρ) (m : Space d)
    {u : Space d} (hu : N u ≤ ρ) :
    γ * ⟪gradient f x, x - u⟫ ≤
      f x - f ((1 - γ) • x + γ • lmo m) + γ * D₂ * ‖m - gradient f x‖ + 2 * L * ρ ^ 2 * γ ^ 2 := by
  open scoped RealInnerProductSpace in
  (
    have hR := unit_bound_of_diameter hρ hD₂
    have hmove : (1 - γ) • x + γ • lmo m - x = γ • (lmo m - x) := by module
    have hdesc := descent_on (ball_convex (N := N) ρ) hR hdef (fun x hx => hgrad x hx)
      (fun x hx y hy => hlip x y hx hy) (x := x) (y := (1 - γ) • x + γ • lmo m) hx
      (scg_feasible hγ0 hγ1 hx (hlmo.feasible m))
    rw [hmove, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ0, inner_smul_right] at hdesc
    have hNl := hlmo.feasible m
    have hN2 : N (lmo m - x) ≤ 2 * ρ := by
      calc N (lmo m - x) ≤ N (lmo m) + N x := map_sub_le_add N _ _
        _ ≤ 2 * ρ := by linarith
    have hNsq : (γ * N (lmo m - x)) ^ 2 ≤ (γ * (2 * ρ)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hγ0 (apply_nonneg N _)) (mul_le_mul_of_nonneg_left hN2 hγ0) 2
    have hmin := hlmo.minimal m u hu
    have hkey : ⟪gradient f x, lmo m - x⟫ ≤ ⟪gradient f x, u - x⟫ + D₂ * ‖m - gradient f x‖ := by
      have e1 : ⟪gradient f x, lmo m - x⟫ = ⟪m, lmo m - x⟫ - ⟪m - gradient f x, lmo m - x⟫ := by
        rw [inner_sub_left]; ring
      have e2 : ⟪gradient f x, u - x⟫ = ⟪m, u - x⟫ - ⟪m - gradient f x, u - x⟫ := by
        rw [inner_sub_left]; ring
      have h1 : ⟪m, lmo m - x⟫ ≤ ⟪m, u - x⟫ := by
        rw [inner_sub_right, inner_sub_right]; linarith
      have h2 : ⟪m - gradient f x, u - x⟫ - ⟪m - gradient f x, lmo m - x⟫ =
          ⟪m - gradient f x, u - lmo m⟫ := by
        rw [← inner_sub_right, sub_sub_sub_cancel_right]
      have h3 : ⟪m - gradient f x, u - lmo m⟫ ≤ ‖m - gradient f x‖ * D₂ :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hD₂ u (lmo m) hu hNl) (norm_nonneg _))
      linarith
    have hneg : ⟪gradient f x, x - u⟫ = -⟪gradient f x, u - x⟫ := by
      rw [← inner_neg_right, neg_sub]
    have hγk := mul_le_mul_of_nonneg_left hkey hγ0
    have hL2 : L / 2 * (γ * N (lmo m - x)) ^ 2 ≤ L / 2 * (γ * (2 * ρ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hNsq (by linarith)
    rw [hneg]
    nlinarith)

end OracleTemplate.NormBallLMO
