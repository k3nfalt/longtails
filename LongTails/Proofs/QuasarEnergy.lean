import LongTails.Algorithms.CachedQuasar
import LongTails.Proofs.GdConvex

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.SimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def energy (f : E → ℝ) (μ : ℝ) (u : E) (s : E × E) : ℝ :=
  f s.1 - f u + μ / 2 * ‖s.2 - u‖ ^ 2

lemma model_energy_step {f : E → ℝ} {μ γ θ : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hrt : γ * θ ≤ 1)
    (x z u g : E)
    (hx : f (query θ (x, z)) + ⟪g, x - query θ (x, z)⟫ -
      γ * μ / (2 * θ) * ‖x - query θ (x, z)‖ ^ 2 ≤ f x)
    (hu : γ * f (query θ (x, z)) + ⟪g, u - query θ (x, z)⟫ +
      γ * μ / 2 * ‖u - query θ (x, z)‖ ^ 2 ≤ γ * f u) :
    f (query θ (x, z)) - f u - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 +
      μ / 2 * ‖(update γ θ μ (x, z) g).2 - u‖ ^ 2 ≤
        (1 - γ * θ) * energy f μ u (x, z) := by
  let y := query θ (x, z)
  let q := 1 - γ * θ
  let v := q • (z - u) + (γ * θ) • (y - u)
  have hden : 1 + θ ≠ 0 := by positivity
  have hi : q • (x - y) + θ • (u - y) = -θ • v := by
    dsimp [v, q, y, query]
    match_scalars
    all_goals field_simp; ring
  have hip := congrArg (fun w => ⟪g, w⟫) hi
  simp only [inner_add_right, inner_smul_right] at hip
  have hm : ‖v‖ ^ 2 = q * ‖z - u‖ ^ 2 + γ * θ * ‖y - u‖ ^ 2 -
      q * γ * θ * ‖z - y‖ ^ 2 := by
    have hdiff : z - y = (z - u) - (y - u) := by module
    rw [hdiff]
    dsimp [v, q]
    rw [norm_add_sq_real, norm_sub_sq_real (z - u) (y - u)]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, inner_smul_right]
    ring
  have hxy : x - y = θ • (y - z) := by
    dsimp [y, query]
    match_scalars
    all_goals field_simp; ring
  have hxy2 : ‖x - y‖ ^ 2 = θ ^ 2 * ‖z - y‖ ^ 2 := by
    rw [hxy, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev y z]
  have hz : (update γ θ μ (x, z) g).2 - u = v - (θ / μ) • g := by
    dsimp [update, v, q, y]
    module
  rw [hz, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm v g]
  have hc : μ / 2 * (‖v‖ ^ 2 - 2 * ((θ / μ) * ⟪g, v⟫) +
      (θ / μ) ^ 2 * ‖g‖ ^ 2) =
      μ / 2 * ‖v‖ ^ 2 - θ * ⟪g, v⟫ + θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 := by
    field_simp
  rw [hc]
  have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hrt)
  have hu' := mul_le_mul_of_nonneg_left hu hθ.le
  change q * (f y + ⟪g, x - y⟫ - γ * μ / (2 * θ) * ‖x - y‖ ^ 2) ≤ q * f x at hx'
  rw [hxy2] at hx'
  have halg : γ * μ / (2 * θ) * (θ ^ 2 * ‖z - y‖ ^ 2) =
      γ * μ * θ / 2 * ‖z - y‖ ^ 2 := by field_simp
  rw [halg] at hx'
  change θ * (γ * f y + ⟪g, u - y⟫ + γ * μ / 2 * ‖u - y‖ ^ 2) ≤ _ at hu'
  have hm' := congrArg (fun t : ℝ => μ / 2 * t) hm
  rw [norm_sub_rev y u] at hm'
  change f y - f u - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 + _ ≤ q * energy f μ u (x, z)
  dsimp only [energy]
  dsimp [q] at hip hx' hm' ⊢
  nlinarith

lemma noisy_model_step {f : E → ℝ} {μ γ θ : ℝ} (hμ : 0 < μ)
    (s : E × E) (u g e : E)
    (hd : f (update γ θ μ s (g + e)).1 ≤
      f (query θ s) - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 + θ ^ 2 / (2 * μ) * ‖e‖ ^ 2) :
    energy f μ u (update γ θ μ s (g + e)) ≤
      f (query θ s) - f u - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 +
        μ / 2 * ‖(update γ θ μ s g).2 - u‖ ^ 2 -
        θ * ⟪e, (update γ θ μ s g).2 - u⟫ + θ ^ 2 / μ * ‖e‖ ^ 2 := by
  have hz : (update γ θ μ s (g + e)).2 - u =
      ((update γ θ μ s g).2 - u) - (θ / μ) • e := by dsimp [update]; module
  unfold energy
  rw [hz, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← real_inner_comm ((update γ θ μ s g).2 - u) e]
  have hi : μ / 2 * (‖(update γ θ μ s g).2 - u‖ ^ 2 -
      2 * (θ / μ * ⟪e, (update γ θ μ s g).2 - u⟫) + (θ / μ) ^ 2 * ‖e‖ ^ 2) =
      μ / 2 * ‖(update γ θ μ s g).2 - u‖ ^ 2 -
        θ * ⟪e, (update γ θ μ s g).2 - u⟫ + θ ^ 2 / (2 * μ) * ‖e‖ ^ 2 := by
    field_simp
  rw [hi]
  have hs : θ ^ 2 / μ * ‖e‖ ^ 2 = 2 * (θ ^ 2 / (2 * μ) * ‖e‖ ^ 2) := by ring
  linarith

variable [CompleteSpace E]

lemma noisy_descent {f : E → ℝ} {G : E → E} {L μ θ : ℝ}
    (hμ : 0 < μ) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (y e : E) :
    f (y - (θ ^ 2 / μ) • (G y + e)) ≤
      f y - θ ^ 2 / (2 * μ) * ‖G y‖ ^ 2 + θ ^ 2 / (2 * μ) * ‖e‖ ^ 2 := by
  have hd := Gradient.smooth_upper_bound hg hlip y (y - (θ ^ 2 / μ) • (G y + e))
  have hv : y - (θ ^ 2 / μ) • (G y + e) - y = -(θ ^ 2 / μ) • (G y + e) := by module
  rw [hv, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hd
  have hc : L / 2 * (θ ^ 2 / μ) ^ 2 ≤ θ ^ 2 / (2 * μ) := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_one hμ).mpr hstep)
      (show 0 ≤ θ ^ 2 / (2 * μ) by positivity)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖G y + e‖)
  have hi : -(θ ^ 2 / μ) * ⟪G y, G y + e⟫ +
      θ ^ 2 / (2 * μ) * ‖G y + e‖ ^ 2 =
      -(θ ^ 2 / (2 * μ) * ‖G y‖ ^ 2) + θ ^ 2 / (2 * μ) * ‖e‖ ^ 2 := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, norm_add_sq_real]
    ring
  nlinarith

end OracleTemplate.SimilarQuasar
