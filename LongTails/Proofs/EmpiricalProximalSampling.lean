import LongTails.Proofs.EmpiricalProximalParameters

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalSampling

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration
open EmpiricalProximalModel EmpiricalProximalMoments EmpiricalProximalParameters
open EmpiricalProximalInner

lemma gradient_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n b : ℕ} (h : b = n) (g : Fin n × E → E) (x : E) :
    FiniteSum.fullGradient (fun q => g (Fin.cast h q.1, q.2)) x =
      FiniteSum.fullGradient g x := by
  subst n
  rfl

lemma objective_cast {E : Type*} {n b : ℕ} (h : b = n) (f : Fin n → E → ℝ) (x : E) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (Fin.cast h i)) x =
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f x := by
  subst n
  rfl

lemma batchPoint_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n b : ℕ} (h : b = n) (g : Fin n × E → E) (μ : ℝ) (c : E) :
    batchPoint g μ c (fun i => Fin.cast h i) =
      RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) μ c := by
  subst n
  rfl

lemma sampled_objective_mean (p : Params) (f : Fin p.n → p.E → ℝ) (x : p.E) :
    (𝔼 ξ : BatchIndices p,
      LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun j => f (indices p ξ j)) x) =
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f x := by
  by_cases h : batchSize p = p.n
  · simp only [indices, dite_eq_left h, objective_cast, Fintype.expect_const]
  · simp only [indices, dite_eq_right h, FiniteSum.objective_eq_expect]
    exact CappedProximalSampling.uniform_cohort_mean (fun i => f i x)

lemma sampled_raw_moment (p : Params) (hρ : 1 ≤ p.ρ) (g : Fin p.n × p.E → p.E)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    (x : p.E) :
    (𝔼 ξ : BatchIndices p, ‖FiniteSum.fullGradient (fun q => g (indices p ξ q.1, q.2)) x‖ ^ 2) ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2 := by
  by_cases h : batchSize p = p.n
  · simp only [indices, dite_eq_left h, gradient_cast, Fintype.expect_const]
    nlinarith [mul_le_mul_of_nonneg_right hρ (sq_nonneg ‖FiniteSum.fullGradient g x‖)]
  · simp only [indices, dite_eq_right h]
    exact (batch_raw_moment g x).trans (hsg x)

lemma sampled_variance (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) :
    (𝔼 ξ : BatchIndices p,
      ‖batchPoint g (regularization p) c (indices p ξ) -
        RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) (regularization p) c‖ ^ 2) ≤
      ‖c - RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) (regularization p) c‖ ^ 2 / 1024 := by
  by_cases h : batchSize p = p.n
  · simp only [indices, dite_eq_left h, batchPoint_cast, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Fintype.expect_const]
    positivity
  · simp only [indices, dite_eq_right h]
    have hv := batch_point_variance (b := batchSize p) hc hg (regularization_pos p hL) hsg hu c
    have hb := stochastic_batch_lower p hρ h
    have hn : 0 ≤ (𝔼 ξ : BatchIndices p,
      ‖batchPoint g (regularization p) c ξ -
        RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) (regularization p) c‖ ^ 2) :=
      Finset.expect_nonneg (fun _ _ => sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hb hn
    apply (mul_le_mul_iff_right₀ (show 0 < p.ρ by linarith)).mp
    nlinarith only [hv, hm]

lemma sampled_generalization (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) :
    (𝔼 ξ : BatchIndices p,
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective f
          (batchPoint g (regularization p) c (indices p ξ)) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun j => f (indices p ξ j))
          (batchPoint g (regularization p) c (indices p ξ)))) ≤
      regularization p *
        ‖c - RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) (regularization p) c‖ ^ 2 / 64 := by
  have hμ := regularization_pos p hL
  by_cases h : batchSize p = p.n
  · simp only [indices, dite_eq_left h, objective_cast, sub_self, Fintype.expect_const]
    positivity
  · simp only [indices, dite_eq_right h]
    let G := 𝔼 ξ : BatchIndices p,
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (batchPoint g (regularization p) c ξ) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun j => f (ξ j))
          (batchPoint g (regularization p) c ξ))
    by_cases hG : 0 ≤ G
    · have hg' := batch_generalization hc hg hL hμ (stochastic_stability_size p hL hρ h)
        hlip hsg hu c
      have hb := mul_le_mul_of_nonneg_right (stochastic_batch_lower p hρ h) hG
      have hp : 0 ≤ p.ρ * regularization p *
          ‖c - RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) (regularization p) c‖ ^ 2 := by
        positivity
      apply (mul_le_mul_iff_right₀ (show 0 < p.ρ by linarith)).mp
      change p.ρ * G ≤ _
      change (batchSize p : ℝ) * G ≤ _ at hg'
      nlinarith only [hg', hb, hp]
    · exact (le_of_not_ge hG).trans (by positivity)

end LongTails.Proofs.EmpiricalProximalSampling
