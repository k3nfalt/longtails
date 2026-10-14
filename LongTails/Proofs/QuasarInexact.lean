import LongTails.Proofs.QuasarEnergy
import LongTails.Proofs.KatyushaStep

open scoped RealInnerProductSpace

namespace OracleTemplate.SimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma robust_energy_step {f : E → ℝ} {G : E → E} {L μ γ θ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hθ : 0 < θ) (hrt : γ * θ ≤ 1)
    (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (x z u e : E) (hmin : ∀ y, f u ≤ f y)
    (hx : f (query θ (x, z)) + ⟪G (query θ (x, z)), x - query θ (x, z)⟫ -
      γ * μ / (2 * θ) * ‖x - query θ (x, z)‖ ^ 2 ≤ f x)
    (hu : γ * f (query θ (x, z)) + ⟪G (query θ (x, z)), u - query θ (x, z)⟫ +
      γ * μ / 2 * ‖u - query θ (x, z)‖ ^ 2 ≤ γ * f u) :
    energy f μ u (update γ θ μ (x, z) (G (query θ (x, z)) + e)) ≤
      (1 - 3 * γ * θ / 4) * energy f μ u (x, z) +
        3 * θ / (γ * μ) * ‖e‖ ^ 2 := by
  let y := query θ (x, z)
  let g := G y
  let w := (update γ θ μ (x, z) g).2 - u
  let E₀ := energy f μ u (x, z)
  have hE : 0 ≤ E₀ := by
    have hf := hmin x
    have hn : 0 ≤ μ / 2 * ‖z - u‖ ^ 2 := by positivity
    dsimp [E₀, energy]
    linarith
  have hm := model_energy_step hμ hθ hrt x z u g hx hu
  change f y - f u - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 + μ / 2 * ‖w‖ ^ 2 ≤
    (1 - γ * θ) * E₀ at hm
  have hd0 := noisy_descent hμ hstep hg hlip y 0
  simp only [add_zero, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hd0
  have hf0 := hmin (y - (θ ^ 2 / μ) • g)
  have hz : μ / 2 * ‖w‖ ^ 2 ≤ (1 - γ * θ) * E₀ := by
    dsimp only [g] at hf0 hm ⊢
    linarith
  have hd := noisy_descent hμ hstep hg hlip y e
  have hn := noisy_model_step (γ := γ) hμ (x, z) u g e hd
  change energy f μ u (update γ θ μ (x, z) (g + e)) ≤
    f y - f u - θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 + μ / 2 * ‖w‖ ^ 2 -
      θ * ⟪e, w⟫ + θ ^ 2 / μ * ‖e‖ ^ 2 at hn
  have hy := Katyusha.quadratic_young (L := γ * μ / 8) (by positivity) e (-w)
  simp only [inner_neg_right, norm_neg] at hy
  have hy' := mul_le_mul_of_nonneg_left hy hθ.le
  have hy'' : -(θ * ⟪e, w⟫) ≤ γ * θ / 4 * (μ / 2 * ‖w‖ ^ 2) +
      (2 * θ / (γ * μ)) * ‖e‖ ^ 2 := by
    convert hy' using 1 <;> field_simp; ring
  have hz' := mul_le_mul_of_nonneg_left hz (show 0 ≤ γ * θ / 4 by positivity)
  have ht := mul_le_mul_of_nonneg_right hrt (show 0 ≤ θ / (γ * μ) by positivity)
  have hi : γ * θ * (θ / (γ * μ)) = θ ^ 2 / μ := by field_simp
  rw [hi, one_mul] at ht
  have ht' := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖e‖)
  have hq : (1 - γ * θ) * E₀ + γ * θ / 4 * ((1 - γ * θ) * E₀) ≤
      (1 - 3 * γ * θ / 4) * E₀ := by
    nlinarith [mul_nonneg (sq_nonneg (γ * θ)) hE]
  have hc : 3 * θ / (γ * μ) * ‖e‖ ^ 2 =
      θ / (γ * μ) * ‖e‖ ^ 2 + 2 * θ / (γ * μ) * ‖e‖ ^ 2 := by ring
  change energy f μ u (update γ θ μ (x, z) (g + e)) ≤
    (1 - 3 * γ * θ / 4) * E₀ + _
  rw [hc]
  linarith

end OracleTemplate.SimilarQuasar
