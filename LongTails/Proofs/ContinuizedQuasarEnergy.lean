import LongTails.Algorithms.ContinuizedQuasar
import LongTails.Proofs.QuasarSimilarity

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma jump_energy_bound {f : E → ℝ} {G : E → E} {L μ θ : ℝ}
    (hμ : 0 < μ) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (s : E × E) (u e : E) :
    SimilarQuasar.energy f μ u (jump θ μ s (G s.1 + e)) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ -
        θ * ⟪e, s.2 - u - (θ / μ) • G s.1⟫ + θ ^ 2 / μ * ‖e‖ ^ 2 := by
  have hd := SimilarQuasar.noisy_descent hμ hstep hg hlip s.1 e
  have hz : (jump θ μ s (G s.1 + e)).2 - u =
      (s.2 - u) - (θ / μ) • (G s.1 + e) := by simp only [jump]; module
  unfold SimilarQuasar.energy
  rw [hz, norm_sub_sq_real]
  simp only [jump, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, inner_add_right, inner_sub_right, inner_sub_left,
    norm_add_sq_real, real_inner_comm]
  field_simp at hd ⊢
  nlinarith

omit [CompleteSpace E] in
lemma generator_model {f : E → ℝ} {μ γ θ J Vnoise : ℝ}
    (hθ : 0 ≤ θ) (x z u g : E)
    (hq : γ * f x + ⟪g, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (hJ : J ≤ SimilarQuasar.energy f μ u (x, z) - θ * ⟪g, z - u⟫ + Vnoise) :
    θ * ⟪g, z - x⟫ + μ * γ * θ * ⟪z - u, x - z⟫ + J -
        SimilarQuasar.energy f μ u (x, z) ≤
      -(γ * θ) * SimilarQuasar.energy f μ u (x, z) -
        γ * μ * θ / 2 * ‖z - x‖ ^ 2 + Vnoise := by
  have hq' := mul_le_mul_of_nonneg_left hq hθ
  have hi : ⟪g, z - x⟫ - ⟪g, z - u⟫ = ⟪g, u - x⟫ := by
    simp only [inner_sub_right]
    ring
  have hn : ‖x - u‖ ^ 2 = ‖z - u‖ ^ 2 + 2 * ⟪z - u, x - z⟫ + ‖z - x‖ ^ 2 := by
    have he : x - u = (z - u) + (x - z) := by module
    rw [he, norm_add_sq_real, norm_sub_rev z x]
  rw [norm_sub_rev u x] at hq'
  have hi' := congrArg (fun v : ℝ => θ * v) hi
  have hn' := congrArg (fun v : ℝ => γ * μ * θ / 2 * v) hn
  dsimp only [SimilarQuasar.energy] at hJ ⊢
  nlinarith

lemma expected_jump_bound {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    {L μ θ : ℝ} (hμ : 0 < μ) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (s : E × E) (u : E) (e : Fin n → E)
    (he : (n : ℝ)⁻¹ • ∑ i, e i = 0) :
    (𝔼 i, SimilarQuasar.energy f μ u (jump θ μ s (G s.1 + e i))) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ +
        θ ^ 2 / μ * (𝔼 i, ‖e i‖ ^ 2) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun i _ => jump_energy_bound hμ hstep hg hlip s u (e i))
  simpa only [Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, Fintype.expect_const, FiniteSum.expect_inner_left,
    he, inner_zero_left, mul_zero, sub_zero] using h

lemma resolvent_contraction {V Y I A b c : ℝ} (hc : 0 ≤ c)
    (hgen : Y ≤ V - c * I + b * A) (hjump : Y ≤ 4 * I + b * A) :
    Y ≤ 4 / (4 + c) * V + b * A := by
  have hd : 0 < 4 + c := by positivity
  have h := mul_le_mul_of_nonneg_left hjump hc
  calc
    Y ≤ (4 * V + (4 + c) * b * A) / (4 + c) :=
      (le_div_iff₀ hd).mpr (by nlinarith)
    _ = 4 / (4 + c) * V + b * A := by field_simp

lemma jump_cross_bound {f : E → ℝ} {G : E → E} {L μ θ : ℝ}
    (hμ : 0 < μ) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (u : E) (hmin : ∀ x, f u ≤ f x) (s : E × E) :
    -θ * ⟪G s.1, s.2 - u⟫ ≤ SimilarQuasar.energy f μ u s := by
  have hd := SimilarQuasar.noisy_descent hμ hstep hg hlip s.1 0
  simp only [add_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hd
  have hm := hmin (s.1 - (θ ^ 2 / μ) • G s.1)
  have hy := Katyusha.quadratic_young (show 0 < μ / 2 by positivity)
    ((-θ) • G s.1) (s.2 - u)
  simp only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hy
  have he : θ ^ 2 * ‖G s.1‖ ^ 2 / (4 * (μ / 2)) =
      θ ^ 2 / (2 * μ) * ‖G s.1‖ ^ 2 := by ring
  rw [he] at hy
  dsimp only [SimilarQuasar.energy]
  linarith

omit [CompleteSpace E] in
lemma variance_energy_bound {n : ℕ} {μ γ θ δ V A : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (x w u : E) (e : Fin n → E)
    (hx : γ * μ * ‖x - u‖ ^ 2 ≤ 4 * V)
    (hw : γ * μ * ‖w - u‖ ^ 2 ≤ 4 * A)
    (he : (𝔼 i, ‖e i‖ ^ 2) ≤ δ ^ 2 * ‖x - w‖ ^ 2) :
    θ ^ 2 / μ * (𝔼 i, ‖e i‖ ^ 2) ≤
      (8 * θ ^ 2 * δ ^ 2 / (γ * μ ^ 2)) * (V + A) := by
  have hd := FiniteSum.norm_sub_sq_le (x - u) (w - u)
  have hi : (x - u) - (w - u) = x - w := by module
  rw [hi] at hd
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ γ * μ by positivity)
  have hdist : ‖x - w‖ ^ 2 ≤ 8 * (V + A) / (γ * μ) :=
    (le_div_iff₀ (show 0 < γ * μ by positivity)).mpr (by nlinarith)
  calc
    _ ≤ θ ^ 2 / μ * (δ ^ 2 * ‖x - w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ θ ^ 2 / μ * (δ ^ 2 * (8 * (V + A) / (γ * μ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist (sq_nonneg δ)) (by positivity)
    _ = _ := by field_simp

lemma estimator_jump_bound {n : ℕ} [NeZero n] {f : E → ℝ} {G : E → E}
    (g : Fin n × E → E) {L μ γ θ δ : ℝ}
    (hμ : 0 < μ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hstep : θ ^ 2 * L ≤ μ)
    (hg : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hfull : ∀ x, FiniteSum.fullGradient g x = G x)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2)
    (u : E) (hmin : ∀ x, f u ≤ f x)
    (hqg : ∀ x, γ * μ / (2 * (2 - γ)) * ‖x - u‖ ^ 2 ≤ f x - f u)
    (w : E) (s : E × E) :
    (𝔼 i, SimilarQuasar.energy f μ u (jump θ μ s (FiniteSum.estimator g w s.1 i))) ≤
      SimilarQuasar.energy f μ u s - θ * ⟪G s.1, s.2 - u⟫ +
        (8 * θ ^ 2 * δ ^ 2 / (γ * μ ^ 2)) *
          (SimilarQuasar.energy f μ u s + (f w - f u)) := by
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
  have hx := (SimilarQuasar.energy_distances hμ hγ hγ1 hmin hqg s).1
  have hw : γ * μ * ‖w - u‖ ^ 2 ≤ 4 * (f w - f u) := by
    simpa [SimilarQuasar.energy] using
      (SimilarQuasar.energy_distances hμ hγ hγ1 hmin hqg (w, u)).1
  have hv := variance_energy_bound (θ := θ) hμ hγ s.1 w u e hx hw hvar
  have hj := expected_jump_bound hμ hstep hg hlip s u e he
  simp only [e, add_sub_cancel] at hj
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma components_continuous {n : ℕ} [NeZero n] (g : Fin n × E → E) (G : E → E)
    {δ : ℝ} (hδ : 0 ≤ δ) (hG : Continuous G)
    (hsim : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      δ ^ 2 * ‖x - y‖ ^ 2) (i : Fin n) : Continuous (fun x => g (i, x)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hl : LipschitzWith ⟨(n : ℝ) * δ, by positivity⟩ (fun x => g (i, x) - G x) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    have hs := hsim x y
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin] at hs
    have hsum := (div_le_iff₀ hn).mp hs
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        sq_nonneg ‖(g (j, x) - G x) - (g (j, y) - G y)‖) (Finset.mem_univ i)
    have hnn := mul_le_mul_of_nonneg_right hn1 (show 0 ≤ (n : ℝ) * δ ^ 2 * ‖x - y‖ ^ 2 by positivity)
    apply (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ (n : ℝ) * δ * ‖x - y‖ by positivity)).mp
    nlinarith
  have hh := hG.add hl.continuous
  simpa only [Pi.add_def, add_sub_cancel] using hh

end OracleTemplate.ContinuizedSimilarQuasar
