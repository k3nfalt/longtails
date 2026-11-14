import LongTails.Proofs.EmpiricalProximalMoments
import LongTails.Proofs.EmpiricalProximalApproximation

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalCertificate

open EmpiricalProximalMoments EmpiricalProximalApproximation

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype Ω] [Nonempty Ω]

lemma approximate_certificate {f : E → ℝ} {φ : Ω → E → ℝ}
    {g : E → E} {q : Ω → E → E} {L μ : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hq : ∀ ξ x, HasGradientAt (φ ξ) (q ξ x) x)
    (hc : ∀ ξ, ConvexOn ℝ univ (φ ξ))
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hqlip : ∀ ξ x y, ‖q ξ x - q ξ y‖ ≤ L * ‖x - y‖)
    (v y : E) (z w : Ω → E) (hy : g y = μ • (v - y))
    (hz : ∀ ξ, q ξ (z ξ) = μ • (v - z ξ))
    (hvariance : (𝔼 ξ, ‖z ξ - y‖ ^ 2) ≤ ‖v - y‖ ^ 2 / 1024)
    (hgeneralization : (𝔼 ξ, (f (z ξ) - φ ξ (z ξ))) ≤ μ * ‖v - y‖ ^ 2 / 64)
    (hinner : (L + μ) ^ 2 * (𝔼 ξ, ‖w ξ - z ξ‖ ^ 2) ≤
      μ ^ 2 * ‖v - y‖ ^ 2 / 2 ^ 20) :
    (𝔼 ξ, (f (w ξ) - φ ξ (w ξ))) ≤ μ⁻¹ / 4 * (𝔼 ξ, ‖q ξ (w ξ)‖ ^ 2) ∧
      (𝔼 ξ, ‖μ⁻¹ • q ξ (w ξ) + w ξ - v‖ ^ 2) ≤
        (μ⁻¹) ^ 2 / 16 * (𝔼 ξ, ‖q ξ (w ξ)‖ ^ 2) := by
  have hgen := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    scaled_generalization_change hL hμ hg (hq ξ) (hc ξ) hlip hy (hz ξ) (w ξ))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hgen
  have hres := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    scaled_residual_bound hμ (hqlip ξ) (hz ξ) (w ξ))
  simp only [← Finset.mul_expect] at hres
  exact normalized_certificate hL hμ (sq_nonneg _)
    (Finset.expect_nonneg fun ξ _ => sq_nonneg ‖w ξ - z ξ‖)
    (Finset.expect_nonneg fun ξ _ => sq_nonneg ‖q ξ (w ξ)‖)
    hgen hgeneralization hvariance hinner hres
    (mean_displacement_bound v y z w (fun ξ => q ξ (w ξ)) μ⁻¹)

end LongTails.Proofs.EmpiricalProximalCertificate
