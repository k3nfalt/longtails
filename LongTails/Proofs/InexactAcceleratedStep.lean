import LongTails.Algorithms.InexactAccelerated
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.InexactGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (f : E → ℝ) (μ : ℝ) (xs : E) (s : E × E) : ℝ :=
  f s.1 - f xs + μ / 4 * ‖s.2 - xs‖ ^ 2

lemma error_sq_le {α δ a e : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (he0 : 0 ≤ e)
    (he : e ≤ α * a + δ) :
    e ^ 2 ≤ 2 * α ^ 2 / (1 + α) * a ^ 2 + 2 / (1 - α) * δ ^ 2 := by
  have h1 : e ^ 2 ≤ (α * a + δ) ^ 2 := pow_le_pow_left₀ he0 he 2
  have hp : 0 < 1 + α := by linarith
  have hm : 0 < 1 - α := by linarith
  have hid : 2 * α ^ 2 / (1 + α) * a ^ 2 + 2 / (1 - α) * δ ^ 2 - (α * a + δ) ^ 2 =
      ((1 - α) * (α * a) - (1 + α) * δ) ^ 2 / ((1 + α) * (1 - α)) := by
    field_simp
    ring
  have hnn : 0 ≤ ((1 - α) * (α * a) - (1 + α) * δ) ^ 2 / ((1 + α) * (1 - α)) := by
    positivity
  linarith

lemma two_inner_le (a b : E) : 2 * ⟪a, b⟫ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := sq_nonneg ‖a - b‖
  rw [norm_sub_sq_real] at h
  linarith

lemma potential_arith {fx fy fs fx' Gs gg ee ew Gw ww Z Y Z' μ θ α δ iL u v A c : ℝ}
    (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hiL : 0 < iL) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hc0 : 0 ≤ c)
    (hA1 : A ≤ α) (hu : 4 * u ≤ (1 - α) * iL) (hAv : 2 * (A * v) ≤ (1 - α) * iL)
    (h1 : fx' ≤ fy - (Gs - ee) * iL)
    (h2 : θ * (fy - fs + μ / 2 * Y) + (1 - θ) * (fy - fx) ≤ θ * Gw)
    (h3 : ww ≤ (1 - θ) * Z + θ * Y)
    (h4 : μ / 4 * Z' = μ / 4 * ww - θ * (Gw + ew) + u / 2 * gg)
    (h5 : -(θ * ew) ≤ θ * μ / 8 * ww + v * ee)
    (h6 : ee ≤ A * Gs + c * δ ^ 2)
    (h7 : gg ≤ 2 * Gs + 2 * ee)
    (hZ : 0 ≤ Z) (hY : 0 ≤ Y) (hGs : 0 ≤ Gs) (hfs : fs ≤ fx) :
    fx' - fs + μ / 4 * Z' ≤
      (1 - θ / 2) * (fx - fs + μ / 4 * Z) + c * (3 / 2 * iL + v) * δ ^ 2 := by
  have p1 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ μ / 4 * (1 + θ / 2) by positivity)
  have p2 := mul_le_mul_of_nonneg_left h7 (show 0 ≤ u / 2 by positivity)
  have p3 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ iL + v + u by positivity)
  have hAiL : A * iL ≤ α * iL := mul_le_mul_of_nonneg_right hA1 hiL.le
  have hAu : A * u ≤ u := by nlinarith
  have hbr : 0 ≤ (1 - A) * iL - (1 + A) * u - A * v := by nlinarith
  have p4 := mul_nonneg hGs hbr
  have p5 : 0 ≤ θ * μ * Y * (1 / 4 - θ / 8) :=
    mul_nonneg (mul_nonneg (mul_nonneg hθ0.le hμ.le) hY) (by linarith)
  have p6 : 0 ≤ μ * θ ^ 2 * Z := by positivity
  have p7 : 0 ≤ θ / 2 * (fx - fs) := mul_nonneg (by positivity) (by linarith)
  have hδ : 0 ≤ c * δ ^ 2 := by positivity
  have hαiL : α * iL ≥ 0 := by positivity
  have p8 : 0 ≤ c * δ ^ 2 * (3 / 2 * iL + v - (iL + v + u)) :=
    mul_nonneg hδ (by nlinarith)
  linarith [p1, p2, p3, p4, p5, p6, p7, p8]

lemma step_potential_aux {fx fy fs fx' L μ α δ θ : ℝ} {x z xs y g G : E}
    (hL : 0 < L) (hμ : 0 < μ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθL : 16 * L * θ ^ 2 ≤ μ * (1 - α)) (hθα : 16 * α ^ 2 * L * θ ≤ μ * (1 - α))
    (hyq : (1 + θ) • y = x + θ • z)
    (a1 : fx' ≤ fy + ⟪G, y - (1 / L) • g - y⟫ + L / 2 * ‖y - (1 / L) • g - y‖ ^ 2)
    (a2 : fy + ⟪G, xs - y⟫ + μ / 2 * ‖xs - y‖ ^ 2 ≤ fs)
    (a3 : fy + ⟪G, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ fx)
    (hfs : fs ≤ fx) (hg : ‖g - G‖ ≤ α * ‖G‖ + δ) :
    fx' - fs + μ / 4 * ‖(1 - θ) • z + θ • y - (2 * θ / μ) • g - xs‖ ^ 2 ≤
      (1 - θ / 2) * (fx - fs + μ / 4 * ‖z - xs‖ ^ 2) +
        2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2 := by
  have hm : 0 < 1 - α := by linarith
  have hp : 0 < 1 + α := by linarith
  let w : E := (1 - θ) • (z - xs) + θ • (y - xs)
  have hee : ‖g - G‖ ^ 2 = ‖g‖ ^ 2 - 2 * ⟪g, G⟫ + ‖G‖ ^ 2 := norm_sub_sq_real g G
  have hcomm : ⟪g, G⟫ = ⟪G, g⟫ := real_inner_comm G g
  have h1 : fx' ≤ fy - (‖G‖ ^ 2 - ‖g - G‖ ^ 2) * (1 / (2 * L)) := by
    have e1 : y - (1 / L) • g - y = -((1 / L) • g) := by abel
    rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at a1
    have e2 : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = ‖g‖ ^ 2 * (1 / (2 * L)) := by
      field_simp
    have e3 : 1 / L * ⟪G, g⟫ = 2 * ⟪G, g⟫ * (1 / (2 * L)) := by
      field_simp
    rw [hee, hcomm]
    linarith
  have h2 : θ * (fy - fs + μ / 2 * ‖y - xs‖ ^ 2) + (1 - θ) * (fy - fx) ≤ θ * ⟪G, w⟫ := by
    have hw : θ • w = θ • (y - xs) + (1 - θ) • (y - x) := by
      have : θ • w = θ • (y - xs) + (1 - θ) • (y - x) +
          (1 - θ) • (x + θ • z - (1 + θ) • y) := by
        simp only [w]
        module
      rw [this, hyq, sub_self, smul_zero, add_zero]
    have hi : θ * ⟪G, w⟫ = θ * ⟪G, y - xs⟫ + (1 - θ) * ⟪G, y - x⟫ := by
      rw [← inner_smul_right, hw, inner_add_right, inner_smul_right, inner_smul_right]
    have b2 : fy - fs + μ / 2 * ‖y - xs‖ ^ 2 ≤ ⟪G, y - xs⟫ := by
      have : ⟪G, xs - y⟫ = -⟪G, y - xs⟫ := by rw [← neg_sub, inner_neg_right]
      rw [this, norm_sub_rev] at a2
      linarith
    have b3 : fy - fx ≤ ⟪G, y - x⟫ := by
      have : ⟪G, x - y⟫ = -⟪G, y - x⟫ := by rw [← neg_sub, inner_neg_right]
      rw [this] at a3
      have := mul_nonneg (show 0 ≤ μ / 2 by positivity) (sq_nonneg ‖x - y‖)
      linarith
    rw [hi]
    have := mul_le_mul_of_nonneg_left b2 hθ0.le
    have := mul_le_mul_of_nonneg_left b3 (show 0 ≤ 1 - θ by linarith)
    linarith
  have h3 : ‖w‖ ^ 2 ≤ (1 - θ) * ‖z - xs‖ ^ 2 + θ * ‖y - xs‖ ^ 2 := by
    have hn : ‖w‖ ^ 2 = (1 - θ) ^ 2 * ‖z - xs‖ ^ 2 +
        2 * ((1 - θ) * θ * ⟪z - xs, y - xs⟫) + θ ^ 2 * ‖y - xs‖ ^ 2 := by
      simp only [w]
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
        sq_abs, sq_abs]
      ring
    have ht := two_inner_le (z - xs) (y - xs)
    have := mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (1 - θ) * θ by exact mul_nonneg (by linarith) hθ0.le)
    rw [hn]
    nlinarith
  have hgw : ⟪g, w⟫ = ⟪G, w⟫ + ⟪g - G, w⟫ := by
    rw [← inner_add_left, add_sub_cancel]
  have h4 : μ / 4 * ‖(1 - θ) • z + θ • y - (2 * θ / μ) • g - xs‖ ^ 2 =
      μ / 4 * ‖w‖ ^ 2 - θ * (⟪G, w⟫ + ⟪g - G, w⟫) + (2 * θ ^ 2 / μ) / 2 * ‖g‖ ^ 2 := by
    have hz : (1 - θ) • z + θ • y - (2 * θ / μ) • g - xs = w - (2 * θ / μ) • g := by
      simp only [w]
      module
    rw [hz, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm g w, hgw]
    field_simp
    ring
  have h5 : -(θ * ⟪g - G, w⟫) ≤ θ * μ / 8 * ‖w‖ ^ 2 + 2 * θ / μ * ‖g - G‖ ^ 2 := by
    have hs := sq_nonneg ‖w + (4 / μ) • (g - G)‖
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm (g - G) w] at hs
    have hm' := mul_nonneg (show 0 ≤ θ * μ / 8 by positivity) hs
    have e : θ * μ / 8 * (‖w‖ ^ 2 + 2 * (4 / μ * ⟪g - G, w⟫) + (4 / μ) ^ 2 * ‖g - G‖ ^ 2) =
        θ * μ / 8 * ‖w‖ ^ 2 + θ * ⟪g - G, w⟫ + 2 * θ / μ * ‖g - G‖ ^ 2 := by
      field_simp
      ring
    rw [e] at hm'
    linarith
  have h6 : ‖g - G‖ ^ 2 ≤ 2 * α ^ 2 / (1 + α) * ‖G‖ ^ 2 + 2 / (1 - α) * δ ^ 2 :=
    error_sq_le hα0 hα1 (norm_nonneg _) hg
  have h7 : ‖g‖ ^ 2 ≤ 2 * ‖G‖ ^ 2 + 2 * ‖g - G‖ ^ 2 := by
    have hgG : ‖g‖ ^ 2 = ‖G‖ ^ 2 + 2 * ⟪G, g - G⟫ + ‖g - G‖ ^ 2 := by
      rw [← norm_add_sq_real, add_sub_cancel]
    have := two_inner_le G (g - G)
    linarith
  have hA1 : 2 * α ^ 2 / (1 + α) ≤ α := by
    rw [div_le_iff₀ hp]
    nlinarith
  have hu : 4 * (2 * θ ^ 2 / μ) ≤ (1 - α) * (1 / (2 * L)) := by
    rw [show 4 * (2 * θ ^ 2 / μ) = 8 * θ ^ 2 / μ by ring,
      show (1 - α) * (1 / (2 * L)) = (1 - α) / (2 * L) by ring,
      div_le_div_iff₀ hμ (by positivity)]
    linarith
  have hAv : 2 * (2 * α ^ 2 / (1 + α) * (2 * θ / μ)) ≤ (1 - α) * (1 / (2 * L)) := by
    have hle : 2 * α ^ 2 / (1 + α) ≤ 2 * α ^ 2 :=
      div_le_self (by positivity) (by linarith)
    have hv : 0 ≤ 2 * θ / μ := by positivity
    have h8 : 2 * (2 * α ^ 2 * (2 * θ / μ)) ≤ (1 - α) * (1 / (2 * L)) := by
      rw [show 2 * (2 * α ^ 2 * (2 * θ / μ)) = 8 * α ^ 2 * θ / μ by ring,
        show (1 - α) * (1 / (2 * L)) = (1 - α) / (2 * L) by ring,
        div_le_div_iff₀ hμ (by positivity)]
      linarith
    have := mul_le_mul_of_nonneg_right hle hv
    linarith
  have hfin := potential_arith hμ hθ0 hθ1 hα0 hα1
    (show 0 < 1 / (2 * L) by positivity) (show 0 ≤ 2 * θ ^ 2 / μ by positivity)
    (show 0 ≤ 2 * θ / μ by positivity)
    (show 0 ≤ 2 / (1 - α) by positivity) hA1 hu hAv h1 h2 h3 h4 h5 h6 h7
    (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hfs
  have e : 2 / (1 - α) * (3 / 2 * (1 / (2 * L)) + 2 * θ / μ) =
      2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) := by
    congr 2
    field_simp
    ring
  rw [e] at hfin
  exact hfin

lemma step_potential {f : E → ℝ} {grad : E → E} {L μ α δ θ : ℝ} {xs : E}
    (hL : 0 < L) (hμ : 0 < μ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθL : 16 * L * θ ^ 2 ≤ μ * (1 - α)) (hθα : 16 * α ^ 2 * L * θ ≤ μ * (1 - α))
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hsc : ∀ x y, f x + ⟪grad x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : ∀ x, f xs ≤ f x) (s : E × E) (g : E)
    (hg : ‖g - grad (query θ s)‖ ≤ α * ‖grad (query θ s)‖ + δ) :
    potential f μ xs (step L μ θ s g) ≤
      (1 - θ / 2) * potential f μ xs s +
        2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2 := by
  have h1θ : (1 + θ) ≠ 0 := by positivity
  have hyq : (1 + θ) • query θ s = s.1 + θ • s.2 := by
    rw [query, smul_smul, mul_one_div_cancel h1θ, one_smul]
  exact step_potential_aux hL hμ hα0 hα1 hθ0 hθ1 hθL hθα hyq (hup _ _) (hsc _ _) (hsc _ _)
    (hmin _) hg

end OracleTemplate.InexactGradient
