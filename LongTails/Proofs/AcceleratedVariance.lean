import LongTails.Proofs.SvrgConvex

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]

lemma estimator_variance_bound
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L : ℝ}
    (hL : 0 < L) (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (snapshot x : E) :
    (𝔼 i, ‖estimator g snapshot x i - fullGradient g x‖ ^ 2) ≤
      2 * L * (objective f snapshot - objective f x -
        ⟪fullGradient g x, snapshot - x⟫) := by
  let v := fun i => g (i, x) - g (i, snapshot)
  have hv : ∀ i, estimator g snapshot x i - fullGradient g x =
      v i - (n : ℝ)⁻¹ • ∑ j, v j := by
    intro i
    simp only [v, Finset.sum_sub_distrib, smul_sub, estimator, fullGradient]
    module
  simp only [hv]
  apply (centered_second_moment v).trans
  have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    gradient_difference_bound hL (hc i) (hg i) (hlip i) snapshot x)
  simpa only [v, norm_sub_rev (g (_, snapshot)), ← Finset.mul_expect,
    Finset.expect_sub_distrib, expect_inner_left, ← objective_eq_expect, fullGradient] using h

end OracleTemplate.FiniteSum
