import LongTails.Proofs.ContinuizedQuasarEnergy

open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma generator_with_reserve {f : E → ℝ} {μ m γ θ J Vnoise : ℝ}
    (hθ : 0 ≤ θ) (x z u g : E)
    (hq : γ * f x + ⟪g, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (hJ : J ≤ SimilarQuasar.energy f m u (x, z) - θ * ⟪g, z - u⟫ + Vnoise) :
    θ * ⟪g, z - x⟫ + m * γ * θ * ⟪z - u, x - z⟫ + J -
        SimilarQuasar.energy f m u (x, z) ≤
      -(γ * θ) * SimilarQuasar.energy f m u (x, z) -
        γ * m * θ / 2 * ‖z - x‖ ^ 2 -
        γ * (μ - m) * θ / 2 * ‖x - u‖ ^ 2 + Vnoise := by
  have hq' := mul_le_mul_of_nonneg_left hq hθ
  have hi : ⟪g, z - x⟫ - ⟪g, z - u⟫ = ⟪g, u - x⟫ := by
    simp only [inner_sub_right]
    ring
  have hn : ‖x - u‖ ^ 2 = ‖z - u‖ ^ 2 + 2 * ⟪z - u, x - z⟫ + ‖z - x‖ ^ 2 := by
    have he : x - u = (z - u) + (x - z) := by module
    rw [he, norm_add_sq_real, norm_sub_rev z x]
  rw [norm_sub_rev u x] at hq'
  have hi' := congrArg (fun v : ℝ => θ * v) hi
  have hn' := congrArg (fun v : ℝ => γ * m * θ / 2 * v) hn
  dsimp only [SimilarQuasar.energy] at hJ ⊢
  nlinarith

omit [CompleteSpace E] in
lemma bias_absorption {μ γ θ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (x z u e : E) :
    -θ * ⟪e, z - u⟫ ≤ γ * μ * θ / 4 * ‖x - u‖ ^ 2 +
      γ * μ * θ / 4 * ‖z - x‖ ^ 2 + 2 * θ / (γ * μ) * ‖e‖ ^ 2 := by
  have ha := Katyusha.quadratic_young (show 0 < γ * μ / 4 by positivity) (-e) (x - u)
  have hb := Katyusha.quadratic_young (show 0 < γ * μ / 4 by positivity) (-e) (z - x)
  simp only [inner_neg_left, norm_neg] at ha hb
  have hi : ⟪e, z - u⟫ = ⟪e, x - u⟫ + ⟪e, z - x⟫ := by
    simp only [inner_sub_right]
    ring
  have he : ‖e‖ ^ 2 / (4 * (γ * μ / 4)) = ‖e‖ ^ 2 / (γ * μ) := by ring
  rw [he] at ha hb
  have hh := mul_le_mul_of_nonneg_left (add_le_add ha hb) hθ
  rw [hi]
  have hid : 2 * θ / (γ * μ) * ‖e‖ ^ 2 = θ * (2 * (‖e‖ ^ 2 / (γ * μ))) := by ring
  rw [hid]
  nlinarith


omit [CompleteSpace E] in
lemma inexact_descent {f : E → ℝ} {L : ℝ} (hL : 0 < L) (x G v : E)
    (hmodel : f (x - (1 / L) • v) ≤ f x +
      ⟪G, x - (1 / L) • v - x⟫ + L / 2 * ‖x - (1 / L) • v - x‖ ^ 2) :
    f (x - (1 / L) • v) ≤ f x - (‖G‖ ^ 2 - ‖v - G‖ ^ 2) / (2 * L) := by
  have hx : x - (1 / L) • v - x = -((1 / L) • v) := by abel
  rw [hx, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hmodel
  rw [norm_sub_sq_real, real_inner_comm G v]
  have hid : f x - (‖G‖ ^ 2 - (‖v‖ ^ 2 - 2 * ⟪G, v⟫ + ‖G‖ ^ 2)) / (2 * L) =
      f x - (1 / L) * ⟪G, v⟫ + L / 2 * ((1 / L) ^ 2 * ‖v‖ ^ 2) := by
    field_simp
    ring
  rw [hid]
  exact hmodel

omit [CompleteSpace E] in
lemma decoupled_jump_bound {f : E → ℝ} {L μ θ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (x z u G v : E)
    (hmodel : f (x - (1 / L) • v) ≤ f x +
      ⟪G, x - (1 / L) • v - x⟫ + L / 2 * ‖x - (1 / L) • v - x‖ ^ 2) :
    SimilarQuasar.energy f (μ / 2) u (x - (1 / L) • v, z - (2 * θ / μ) • v) ≤
      SimilarQuasar.energy f (μ / 2) u (x, z) - θ * ⟪G, z - u⟫ -
        θ * ⟪v - G, z - u⟫ - (‖G‖ ^ 2 - ‖v - G‖ ^ 2) / (2 * L) +
          θ ^ 2 / μ * ‖v‖ ^ 2 := by
  have hd := inexact_descent hL x G v hmodel
  have hz : z - (2 * θ / μ) • v - u = (z - u) - (2 * θ / μ) • v := by module
  have hi : ⟪v, z - u⟫ = ⟪G, z - u⟫ + ⟪v - G, z - u⟫ := by
    rw [inner_sub_left]
    ring
  dsimp only [SimilarQuasar.energy]
  rw [hz, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_comm v (z - u), hi]
  field_simp at hd ⊢
  nlinarith


omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma relative_norm_bounds {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (G v : E)
    (he : ‖v - G‖ ≤ δ * ‖G‖) :
    ‖v - G‖ ^ 2 ≤ δ ^ 2 * ‖G‖ ^ 2 ∧ ‖v‖ ^ 2 ≤ 4 * ‖G‖ ^ 2 := by
  constructor
  · have hh := pow_le_pow_left₀ (norm_nonneg _) he 2
    simpa only [mul_pow] using hh
  · have ht : ‖v‖ ≤ ‖v - G‖ + ‖G‖ := by
      simpa only [sub_add_cancel] using norm_add_le (v - G) G
    have hm := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg G)
    have hv : ‖v‖ ≤ 2 * ‖G‖ := by linarith
    have hh := pow_le_pow_left₀ (norm_nonneg v) hv 2
    nlinarith

omit [CompleteSpace E] in
lemma relative_generator {f : E → ℝ} {L μ γ θ δ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcoef : (δ ^ 2 - 1) / (2 * L) + 4 * θ ^ 2 / μ +
      2 * θ * δ ^ 2 / (γ * μ) ≤ 0)
    (x z u G v : E)
    (hq : γ * f x + ⟪G, u - x⟫ + γ * μ / 2 * ‖u - x‖ ^ 2 ≤ γ * f u)
    (hmodel : f (x - (1 / L) • v) ≤ f x +
      ⟪G, x - (1 / L) • v - x⟫ + L / 2 * ‖x - (1 / L) • v - x‖ ^ 2)
    (he : ‖v - G‖ ≤ δ * ‖G‖) :
    θ * ⟪G, z - x⟫ + (μ / 2) * γ * θ * ⟪z - u, x - z⟫ +
      SimilarQuasar.energy f (μ / 2) u (x - (1 / L) • v, z - (2 * θ / μ) • v) -
      SimilarQuasar.energy f (μ / 2) u (x, z) ≤
        -(γ * θ) * SimilarQuasar.energy f (μ / 2) u (x, z) := by
  have hj := decoupled_jump_bound (θ := θ) hL hμ x z u G v hmodel
  have hg := generator_with_reserve (m := μ / 2) hθ x z u G hq
    (show SimilarQuasar.energy f (μ / 2) u
      (x - (1 / L) • v, z - (2 * θ / μ) • v) ≤
      SimilarQuasar.energy f (μ / 2) u (x, z) - θ * ⟪G, z - u⟫ +
      (-θ * ⟪v - G, z - u⟫ - (‖G‖ ^ 2 - ‖v - G‖ ^ 2) / (2 * L) +
        θ ^ 2 / μ * ‖v‖ ^ 2) from by linarith)
  have hb := bias_absorption hμ hγ hθ x z u (v - G)
  obtain ⟨hee, hv⟩ := relative_norm_bounds hδ hδ1 G v he
  have hee' := mul_le_mul_of_nonneg_left hee
    (show 0 ≤ 1 / (2 * L) + 2 * θ / (γ * μ) by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ θ ^ 2 / μ by positivity)
  have hc := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg ‖G‖)
  have hid : ((δ ^ 2 - 1) / (2 * L) + 4 * θ ^ 2 / μ +
      2 * θ * δ ^ 2 / (γ * μ)) * ‖G‖ ^ 2 =
      -(‖G‖ ^ 2 / (2 * L)) + (1 / (2 * L) + 2 * θ / (γ * μ)) *
        (δ ^ 2 * ‖G‖ ^ 2) + θ ^ 2 / μ * (4 * ‖G‖ ^ 2) := by ring
  rw [hid] at hc
  have hid2 : (‖G‖ ^ 2 - ‖v - G‖ ^ 2) / (2 * L) =
      ‖G‖ ^ 2 / (2 * L) - (1 / (2 * L)) * ‖v - G‖ ^ 2 := by ring
  rw [hid2] at hg
  nlinarith


omit [CompleteSpace E] in
lemma decoupled_jump_growth {f : E → ℝ} {L μ θ δ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hstep : 16 * L * θ ^ 2 ≤ μ) (x z u G v : E)
    (hmin : ∀ y, f u ≤ f y)
    (hmodel : ∀ w, f (x - (1 / L) • w) ≤ f x +
      ⟪G, x - (1 / L) • w - x⟫ + L / 2 * ‖x - (1 / L) • w - x‖ ^ 2)
    (he : ‖v - G‖ ≤ δ * ‖G‖) :
    SimilarQuasar.energy f (μ / 2) u (x - (1 / L) • v, z - (2 * θ / μ) • v) ≤
      4 * SimilarQuasar.energy f (μ / 2) u (x, z) := by
  have hd := inexact_descent hL x G v (hmodel v)
  have hG := inexact_descent hL x G G (hmodel G)
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hG
  have hgap : ‖G‖ ^ 2 ≤ 2 * L * (f x - f u) := by
    have hm := hmin (x - (1 / L) • G)
    have hh : ‖G‖ ^ 2 / (2 * L) ≤ f x - f u := by linarith
    have hh' := (div_le_iff₀ (show 0 < 2 * L by positivity)).mp hh
    nlinarith
  obtain ⟨hee, hv⟩ := relative_norm_bounds hδ hδ1 G v he
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have heG := mul_le_mul_of_nonneg_right hδsq (sq_nonneg ‖G‖)
  have hmono : f (x - (1 / L) • v) ≤ f x := by
    have : 0 ≤ (‖G‖ ^ 2 - ‖v - G‖ ^ 2) / (2 * L) := by
      apply div_nonneg _ (by positivity)
      nlinarith
    linarith
  have hn := FiniteSum.norm_sub_sq_le (z - u) ((2 * θ / μ) • v)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hn
  have hz : z - (2 * θ / μ) • v - u = (z - u) - (2 * θ / μ) • v := by module
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ μ / 4 by positivity)
  have hid : μ / 4 * (2 * ‖z - u‖ ^ 2 + 2 * ((2 * θ / μ) ^ 2 * ‖v‖ ^ 2)) =
      μ / 2 * ‖z - u‖ ^ 2 + 2 * θ ^ 2 / μ * ‖v‖ ^ 2 := by
    field_simp
    ring
  rw [hid] at hn'
  have hvg := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * θ ^ 2 / μ by positivity)
  have hgg := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 8 * θ ^ 2 / μ by positivity)
  have hh : 16 * L * θ ^ 2 / μ ≤ 1 := (div_le_one hμ).mpr hstep
  have hh' := mul_le_mul_of_nonneg_right hh (sub_nonneg.mpr (hmin x))
  have hid2 : 8 * θ ^ 2 / μ * (2 * L * (f x - f u)) =
      (16 * L * θ ^ 2 / μ) * (f x - f u) := by ring
  rw [hid2] at hgg
  have hvbound : 2 * θ ^ 2 / μ * ‖v‖ ^ 2 ≤ f x - f u := by
    calc
      _ ≤ 8 * θ ^ 2 / μ * ‖G‖ ^ 2 := by convert hvg using 1; ring
      _ ≤ _ := hgg.trans (by simpa only [one_mul] using hh')
  have hnfinal := hn'.trans (add_le_add (le_refl (μ / 2 * ‖z - u‖ ^ 2)) hvbound)
  dsimp only [SimilarQuasar.energy]
  rw [hz]
  have hz0 := mul_nonneg hμ.le (sq_nonneg ‖z - u‖)
  nlinarith only [hnfinal, hmono, hz0, hmin x]

end OracleTemplate.RelativeQuasar
