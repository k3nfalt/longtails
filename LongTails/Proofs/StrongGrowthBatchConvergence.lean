import LongTails.Proofs.StrongGrowthBatchContraction

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StrongGrowthBatchProx

open OracleTemplate
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
open LongTails.Algorithms.StrongGrowthBatchProx

lemma one_step_distance (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    (hsc : StrongConvexOn univ p.μ (objective f))
    {u : p.E} (hu : IsMinOn (objective f) univ u) (c : p.E) :
    (𝔼 ξ : BatchIndices p × InnerSeeds p,
      ‖innerOutput p g c (indices p ξ.1) ξ.2 - u‖ ^ 2) ≤ ‖c - u‖ ^ 2 / 2 := by
  have hcommon (i : Fin p.n) (x : p.E) : f i u ≤ f i x :=
    common_minima_of_strong_growth hc hg hsg hu i (mem_univ x)
  let y := prox (FiniteSum.fullGradient g) p.μ c
  let w := fun ξ : BatchIndices p × InnerSeeds p =>
    prox (FiniteSum.fullGradient (fun q => g (indices p ξ.1 q.1, q.2))) p.μ c
  let z := fun ξ : BatchIndices p × InnerSeeds p =>
    innerOutput p g c (indices p ξ.1) ξ.2
  have hy : ‖y - u‖ ^ 2 ≤ ‖c - u‖ ^ 2 / 4 := by
    have hh := population_prox_contraction (FiniteSum.objective_gradient hg) hμ hsc hu c
    have hs := pow_le_pow_left₀ (norm_nonneg (y - u)) hh 2
    nlinarith
  have hw : (𝔼 ξ : BatchIndices p × InnerSeeds p, ‖w ξ - y‖ ^ 2) ≤
      ‖c - u‖ ^ 2 / 128 := by
    have hh := selected_prox_variance p hμ hρ f g hc hg hsg hcommon c
    rw [← Finset.univ_product_univ, Finset.expect_product]
    simp only [w, Fintype.expect_const]
    exact hh
  have hz : (𝔼 ξ : BatchIndices p × InnerSeeds p, ‖z ξ - w ξ‖ ^ 2) ≤
      ‖c - u‖ ^ 2 / 256 := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
    have hh := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
      inner_distance_bound p hL hμ f g hc hg hlip hcommon c (indices p ξ))
    have hbound : (𝔼 ξ : BatchIndices p, 𝔼 ζ : InnerSeeds p,
        ‖z (ξ, ζ) - w (ξ, ζ)‖ ^ 2) ≤ ‖c - u‖ ^ 2 / 512 := by
      simpa only [z, w, Fintype.expect_const] using hh
    exact hbound.trans (by nlinarith [sq_nonneg ‖c - u‖])
  exact mean_three_error_contraction z w y u hy hw hz

lemma output_distance_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hρ : 1 ≤ p.ρ) (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    (hsc : StrongConvexOn univ p.μ (objective f))
    {u : p.E} (hu : IsMinOn (objective f) univ u) (T : ℕ) (c : p.E) :
    (𝔼 ξ : Seeds p T, ‖output p g T c ξ - u‖ ^ 2) ≤
      (1 / 2 : ℝ) ^ T * ‖c - u‖ ^ 2 := by
  induction T generalizing c with
  | zero => simp [output]
  | succ T ih =>
    erw [NonconvexFiniteSum.expect_function_succ]
    simp only [output, Fin.cons_zero, Fin.cons_succ]
    have hh := Finset.expect_le_expect (s := Finset.univ)
      (fun (ξ : BatchIndices p × InnerSeeds p) _ =>
      ih (innerOutput p g c (indices p ξ.1) ξ.2))
    rw [← Finset.mul_expect] at hh
    have hs := mul_le_mul_of_nonneg_left
      (one_step_distance p hL hμ hρ f g hc hg hlip hsg hsc hu c)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) T)
    have he : (1 / 2 : ℝ) ^ T * (‖c - u‖ ^ 2 / 2) =
        (1 / 2 : ℝ) ^ (T + 1) * ‖c - u‖ ^ 2 := by rw [pow_succ]; ring
    exact hh.trans (hs.trans_eq he)

lemma output_gap_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (hρ : 1 ≤ p.ρ) (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    (hsc : StrongConvexOn univ p.μ (objective f))
    {u : p.E} (hu : IsMinOn (objective f) univ u) (T : ℕ) (c : p.E) :
    (𝔼 ξ : Seeds p T, (objective f (output p g T c ξ) - objective f u)) ≤
      p.L / 2 * ((1 / 2 : ℝ) ^ T * ‖c - u‖ ^ 2) := by
  have huG := FiniteSum.fullGradient_minimizer hg hu
  have hp (x : p.E) : objective f x - objective f u ≤ p.L / 2 * ‖x - u‖ ^ 2 := by
    have hh := Gradient.smooth_upper_bound (FiniteSum.objective_gradient hg)
      (FiniteSum.fullGradient_lipschitz hlip) u x
    rw [huG, inner_zero_left, add_zero] at hh
    linarith
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => hp (output p g T c ξ))
  rw [← Finset.mul_expect] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (output_distance_bound p hL hμ hρ f g hc hg hlip hsg hsc hu T c) (by positivity))

end LongTails.Proofs.StrongGrowthBatchProx
