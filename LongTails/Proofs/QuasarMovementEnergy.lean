import LongTails.Proofs.ContinuizedQuasarEnergy

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma jump_energy_slack {f : E → ℝ} {G : E → E} {L μ θ : ℝ}
    (hμ : 0 < μ) (hstep : 2 * θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (s : E × E) (u e : E) :
    SimilarQuasar.energy f μ u (jump θ μ s (G s.1 + e)) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ -
        θ ^ 2 / (4 * μ) * ‖G s.1‖ ^ 2 -
        θ * ⟪e, s.2 - u - (θ / (2 * μ)) • G s.1⟫ +
        θ ^ 2 / μ * ‖e‖ ^ 2 := by
  have hd := Gradient.smooth_upper_bound hg hlip s.1
    (s.1 - (θ ^ 2 / μ) • (G s.1 + e))
  have hv : s.1 - (θ ^ 2 / μ) • (G s.1 + e) - s.1 =
      -(θ ^ 2 / μ) • (G s.1 + e) := by module
  rw [hv, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hd
  have hc : L / 2 * (θ ^ 2 / μ) ^ 2 ≤ θ ^ 2 / (4 * μ) := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_one hμ).mpr hstep)
      (show 0 ≤ θ ^ 2 / (4 * μ) by positivity)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖G s.1 + e‖)
  have hd' : f (s.1 - (θ ^ 2 / μ) • (G s.1 + e)) ≤
      f s.1 - (θ ^ 2 / μ) * ⟪G s.1, G s.1 + e⟫ +
        θ ^ 2 / (4 * μ) * ‖G s.1 + e‖ ^ 2 := by linarith
  have hz : (jump θ μ s (G s.1 + e)).2 - u =
      (s.2 - u) - (θ / μ) • (G s.1 + e) := by simp only [jump]; module
  unfold SimilarQuasar.energy
  rw [hz, norm_sub_sq_real]
  simp only [jump, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, inner_add_right, inner_sub_right, inner_sub_left,
    norm_add_sq_real, real_inner_comm] at hd' ⊢
  rw [real_inner_self_eq_norm_sq] at hd'
  have he := mul_nonneg (sq_nonneg θ) (sq_nonneg ‖e‖)
  field_simp at hd' ⊢
  nlinarith only [hd', he]

lemma expected_jump_slack {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    {L μ θ : ℝ} (hμ : 0 < μ) (hstep : 2 * θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (s : E × E) (u : E) (e : Fin n → E)
    (he : (n : ℝ)⁻¹ • ∑ i, e i = 0) :
    (𝔼 i, SimilarQuasar.energy f μ u (jump θ μ s (G s.1 + e i))) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ -
        θ ^ 2 / (4 * μ) * ‖G s.1‖ ^ 2 + θ ^ 2 / μ * (𝔼 i, ‖e i‖ ^ 2) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => jump_energy_slack hμ hstep hg hlip s u (e i))
  simpa only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, Fintype.expect_const, FiniteSum.expect_inner_left,
    he, inner_zero_left, mul_zero, sub_zero] using h

lemma estimator_jump_slack {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    (g : Fin n × E → E) {L μ θ δ : ℝ}
    (hμ : 0 < μ) (hstep : 2 * θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2) (u w : E) (s : E × E) :
    (𝔼 i, SimilarQuasar.energy f μ u (jump θ μ s (FiniteSum.estimator g w s.1 i))) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ -
        θ ^ 2 / (4 * μ) * ‖G s.1‖ ^ 2 + θ ^ 2 / μ * δ ^ 2 * ‖s.1 - w‖ ^ 2 := by
  let e := fun i => FiniteSum.estimator g w s.1 i - G s.1
  have he : (n : ℝ)⁻¹ • ∑ i, e i = 0 := by
    simp only [e, Finset.sum_sub_distrib, smul_sub]
    rw [FiniteSum.estimator_unbiased, hfull]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, NeZero.ne n]
  have hvar : (𝔼 i, ‖e i‖ ^ 2) ≤ δ ^ 2 * ‖s.1 - w‖ ^ 2 := by
    have hi (i : Fin n) : e i = (g (i, s.1) - G s.1) - (g (i, w) - G w) := by
      dsimp [e, FiniteSum.estimator]
      rw [hfull]
      abel
    simp_rw [hi]
    exact hsim _ _
  have hj := expected_jump_slack hμ hstep hg hlip s u e he
  have hv := mul_le_mul_of_nonneg_left hvar (show 0 ≤ θ ^ 2 / μ by positivity)
  simp only [e, add_sub_cancel] at hj
  nlinarith

omit [CompleteSpace E] in
lemma expected_distance_jump {n : ℕ} [NeZero n] (h : Fin n → E) (G x w : E)
    (η : ℝ) (hu : (n : ℝ)⁻¹ • ∑ i, h i = G) :
    (𝔼 i, ‖x - η • h i - w‖ ^ 2) =
      ‖x - w‖ ^ 2 - 2 * η * ⟪G, x - w⟫ +
        η ^ 2 * (‖G‖ ^ 2 + (𝔼 i, ‖h i - G‖ ^ 2)) := by
  have hzero : (n : ℝ)⁻¹ • ∑ i, (h i - G) = 0 := by
    simp only [Finset.sum_sub_distrib, smul_sub, hu]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, NeZero.ne n]
  have hv : (𝔼 i, ‖h i‖ ^ 2) = ‖G‖ ^ 2 + (𝔼 i, ‖h i - G‖ ^ 2) := by
    have heq (i : Fin n) : ‖h i - G‖ ^ 2 =
        ‖h i‖ ^ 2 - 2 * ⟪h i, G⟫ + ‖G‖ ^ 2 := by
      rw [norm_sub_sq_real]
    simp_rw [heq, Finset.expect_add_distrib, Finset.expect_sub_distrib,
      ← Finset.mul_expect, FiniteSum.expect_inner_left, hu,
      real_inner_self_eq_norm_sq, Fintype.expect_const]
    ring
  have heq (i : Fin n) : ‖x - η • h i - w‖ ^ 2 =
      ‖x - w‖ ^ 2 - 2 * η * ⟪h i, x - w⟫ + η ^ 2 * ‖h i‖ ^ 2 := by
    have hh : x - η • h i - w = (x - w) - η • h i := by module
    rw [hh, norm_sub_sq_real]
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm]
    ring
  simp_rw [heq, Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, FiniteSum.expect_inner_left, hu, Fintype.expect_const, hv]

omit [CompleteSpace E] in
lemma movement_young (h d : E) (a : ℝ) {m : ℝ} (hm : 0 < m) :
    2 * a * ⟪h, d⟫ ≤ ‖h‖ ^ 2 / m + m * a ^ 2 * ‖d‖ ^ 2 := by
  have hh := Katyusha.quadratic_young (show 0 < 1 / m by positivity) ((2 * a) • d) h
  simp only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
  rw [real_inner_comm] at hh
  convert hh using 1; field_simp; ring

omit [CompleteSpace E] in
lemma distance_generator_bound {n : ℕ} [NeZero n] (h : Fin n → E)
    (G x w d : E) (θ η δ : ℝ) {m : ℝ} (hm : 0 < m)
    (hu : (n : ℝ)⁻¹ • ∑ i, h i = G)
    (hv : (𝔼 i, ‖h i - G‖ ^ 2) ≤ δ ^ 2 * ‖x - w‖ ^ 2) :
    2 * θ * ⟪x - w, d⟫ + (𝔼 i, ‖x - η • h i - w‖ ^ 2) - ‖x - w‖ ^ 2 ≤
      (2 / m + η ^ 2 * δ ^ 2) * ‖x - w‖ ^ 2 +
        m * θ ^ 2 * ‖d‖ ^ 2 + (m + 1) * η ^ 2 * ‖G‖ ^ 2 := by
  rw [expected_distance_jump h G x w η hu]
  have h1 := movement_young (x - w) d θ hm
  have h2 := movement_young (x - w) G (-η) hm
  rw [← real_inner_comm (x - w) G] at h2
  have h3 := mul_le_mul_of_nonneg_left hv (sq_nonneg η)
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  nlinarith only [h1, h2, h3]

end OracleTemplate.ContinuizedSimilarQuasar.Movement
