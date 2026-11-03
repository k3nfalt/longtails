import LongTails.Proofs.ComponentEnvelopeProx
import LongTails.Proofs.VarianceReducedWeakMintySampling

open Set InnerProductSpace
open scoped RealInnerProductSpace
open scoped BigOperators

namespace LongTails.Proofs.StrongGrowthBatchProx

open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma prox_perturbation [ProperSpace E] {f : E → ℝ} {g h : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ x, f u ≤ f x)
    (c y : E) (hy : h y = μ • (c - y)) :
    μ * ‖prox g μ c - y‖ ≤ ‖g y - h y‖ := by
  have hr := component_residual_error hc hg hμ hmin c y
  have hl : μ • (c - y) - envelopeField g μ c = μ • (prox g μ c - y) := by
    unfold envelopeField
    module
  have he : g y + μ • (y - c) = g y - h y := by
    rw [hy]
    module
  rw [hl, he, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hr
  exact hr

omit [CompleteSpace E] in
lemma stationary_contraction {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    {u c y : E} (hu : g u = 0) (hy : g y = μ • (c - y))
    (hm : μ * ‖y - u‖ ^ 2 ≤ ⟪g y - g u, y - u⟫) :
    ‖y - u‖ ≤ ‖c - u‖ / 2 := by
  rw [hu, sub_zero, hy, real_inner_smul_left] at hm
  have he : ⟪c - y, y - u⟫ = ⟪c - u, y - u⟫ - ‖y - u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← inner_sub_left]
    congr 1
    module
  rw [he] at hm
  have hb := real_inner_le_norm (c - u) (y - u)
  have hi : 2 * ‖y - u‖ ^ 2 ≤ ‖c - u‖ * ‖y - u‖ := by
    have hh : μ * (2 * ‖y - u‖ ^ 2) ≤ μ * (‖c - u‖ * ‖y - u‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hb hμ.le]
    nlinarith
  by_cases hz : ‖y - u‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖y - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

omit [CompleteSpace E] in
lemma batch_variance {n b : ℕ} [NeZero n] (v : Fin n → E)
    (hb : 0 < b) {V : ℝ} (hv : (𝔼 i, ‖v i‖ ^ 2) ≤ V) :
    (𝔼 ξ : Fin b → Fin n,
      ‖(b : ℝ)⁻¹ • ∑ j, v (ξ j) - (n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2) ≤ V / b := by
  have he (ξ : Fin b → Fin n) := OracleTemplate.RobustGradient.finite_mean_centered
    (X := v) ((n : ℝ)⁻¹ • ∑ i, v i) b hb ξ
  simp only [one_div] at he
  simp_rw [he]
  rw [OracleTemplate.VarianceReducedWeakMinty.batch_mean_second_moment
    (fun i => v i - (n : ℝ)⁻¹ • ∑ j, v j)
    (OracleTemplate.VarianceReducedWeakMinty.component_centered_sum
      (NeZero.pos n) v) hb]
  exact div_le_div_of_nonneg_right
    ((OracleTemplate.FiniteSum.centered_second_moment v).trans hv) (Nat.cast_nonneg b)

omit [CompleteSpace E] in
lemma three_error_bound (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 / 2 * ‖a‖ ^ 2 + 6 * ‖b‖ ^ 2 + 6 * ‖c‖ ^ 2 := by
  have hadd (x y : E) : ‖x + y‖ ^ 2 ≤ 3 / 2 * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real]
    have hi := real_inner_le_norm x y
    nlinarith [sq_nonneg (‖x‖ - 2 * ‖y‖)]
  have hbc : ‖b + c‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
    rw [norm_add_sq_real]
    have hi := real_inner_le_norm b c
    nlinarith [sq_nonneg (‖b‖ - ‖c‖)]
  have hh := hadd a (b + c)
  rw [← add_assoc] at hh
  linarith

lemma mean_prox_perturbation [ProperSpace E] {B : Type*} [Fintype B]
    {f : B → E → ℝ} {g : B → E → E} {h : E → E}
    (hc : ∀ b, ConvexOn ℝ univ (f b))
    (hg : ∀ b x, HasGradientAt (f b) (g b x) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hmin : ∀ b x, f b u ≤ f b x)
    (c y : E) (hy : h y = μ • (c - y)) {V : ℝ}
    (hv : (𝔼 b, ‖g b y - h y‖ ^ 2) ≤ V) :
    (𝔼 b, ‖prox (g b) μ c - y‖ ^ 2) ≤ V / μ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
  have hp (b : B) := prox_perturbation (hc b) (hg b) hμ (hmin b) c y hy
  have hs (b : B) : μ ^ 2 * ‖prox (g b) μ c - y‖ ^ 2 ≤
      ‖g b y - h y‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity)
      (hp b) 2
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun b _ => hs b)
  rw [← Finset.mul_expect] at hh
  nlinarith

omit [CompleteSpace E] in
lemma mean_three_error_contraction {B : Type*} [Fintype B] [Nonempty B]
    (z w : B → E) (y u : E) {D : ℝ}
    (hy : ‖y - u‖ ^ 2 ≤ D / 4)
    (hw : (𝔼 b, ‖w b - y‖ ^ 2) ≤ D / 128)
    (hz : (𝔼 b, ‖z b - w b‖ ^ 2) ≤ D / 256) :
    (𝔼 b, ‖z b - u‖ ^ 2) ≤ D / 2 := by
  have hD : 0 ≤ D := by nlinarith [sq_nonneg ‖y - u‖]
  have he (b : B) : z b - u = (y - u) + (w b - y) + (z b - w b) := by module
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun b _ =>
    three_error_bound (y - u) (w b - y) (z b - w b))
  simp only [← he, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const] at hh
  linarith

end LongTails.Proofs.StrongGrowthBatchProx
