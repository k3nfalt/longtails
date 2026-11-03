import LongTails.Proofs.FiniteSumNondualProxGeometry
import LongTails.Proofs.ComponentEnvelopeCoupling

open Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualProxVariance

open FiniteSumNondualProxGeometry
open RecursiveEnvelopeGeometry (Model)
open OracleTemplate.FiniteSum
open LongTails.Setups.FiniteSumSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [NeZero n]

lemma bregman_le_regularized_gap {C : Set E} (hC : Convex ℝ C)
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hf : Model L f g) (hμ : 0 ≤ μ)
    (c u x : E) (hu : u ∈ C) (hx : x ∈ C)
    (hmin : IsMinOn (regularized f μ c) C u) :
    f x - f u - ⟪g u, x - u⟫ ≤ regularized f μ c x - regularized f μ c u := by
  have hv := minimizer_variational hC (regularized_model hf hμ c) hu hmin x hx
  unfold regularizedGradient at hv
  rw [inner_add_left, real_inner_smul_left] at hv
  unfold regularized
  rw [shifted_square c u x]
  nlinarith [mul_nonneg hμ (sq_nonneg ‖x - u‖)]

lemma component_variation {C : Set E} (hC : Convex ℝ C)
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L μ : ℝ}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x))) (hμ : 0 ≤ μ)
    (c u x : E) (hu : u ∈ C) (hx : x ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) :
    (𝔼 i, ‖g (i, x) - g (i, u)‖ ^ 2) ≤
      2 * L * (regularized (objective f) μ c x - regularized (objective f) μ c u) := by
  have hb := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hm i).bregman x u)
  simp only [← Finset.mul_expect, Finset.expect_sub_distrib, expect_inner_left,
    ← objective_eq_expect] at hb
  have hg := bregman_le_regularized_gap hC (OracleTemplate.ComponentEnvelope.finiteSum_model hm)
    hμ c u x hu hx hmin
  simpa only [objective_eq_expect] using
    hb.trans (mul_le_mul_of_nonneg_left hg (by positivity [(hm 0).pos]))

lemma estimator_variance {C : Set E} (hC : Convex ℝ C)
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L μ : ℝ}
    (hm : ∀ i, Model L (f i) (fun x => g (i, x))) (hμ : 0 ≤ μ)
    (c u z x : E) (hu : u ∈ C) (hz : z ∈ C) (hx : x ∈ C)
    (hmin : IsMinOn (regularized (objective f) μ c) C u) :
    (𝔼 i, ‖estimator g z x i - fullGradient g x‖ ^ 2) ≤
      4 * L * ((regularized (objective f) μ c x - regularized (objective f) μ c u) +
        (regularized (objective f) μ c z - regularized (objective f) μ c u)) := by
  let a := fun i : Fin n => g (i, x) - g (i, z)
  have he : ∀ i, estimator g z x i - fullGradient g x =
      a i - (n : ℝ)⁻¹ • ∑ j, a j := by
    intro i
    simp only [a, Finset.sum_sub_distrib, smul_sub, estimator, fullGradient]
    module
  simp only [he]
  have hc := centered_second_moment a
  have hb := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    norm_sub_sq_le (g (i, x) - g (i, u)) (g (i, z) - g (i, u)))
  simp only [sub_sub_sub_cancel_right, Finset.expect_add_distrib, ← Finset.mul_expect] at hb
  have hx' := component_variation hC hm hμ c u x hu hx hmin
  have hz' := component_variation hC hm hμ c u z hu hz hmin
  dsimp only [a] at hc
  linarith

end LongTails.Proofs.FiniteSumNondualProxVariance
