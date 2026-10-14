import LongTails.Proofs.GeneralizedGradientStep
import LongTails.Proofs.GeneralizedAcceleratedEnergy

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma local_step_norm {M : ℝ} (hM : 0 < M) (y v : E) :
    ‖y - (1 / M) • v - y‖ = ‖v‖ / M := by
  have he : y - (1 / M) • v - y = -(1 / M) • v := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr hM)]
  ring

omit [CompleteSpace E] in
lemma local_step_residual {g : E → E} {L0 L1 M : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (y v : E) (hM : 16 * (L0 + L1 * ‖v‖) ≤ M) :
    let w := y - (1 / M) • v
    ‖g w + M • (w - y)‖ ≤ M / 4 * ‖w - y‖ + 2 * ‖g y - v‖ := by
  let w := y - (1 / M) • v
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hd : ‖w - y‖ = ‖v‖ / M := local_step_norm hMpos y v
  have hsmall : L1 * ‖w - y‖ ≤ 1 / 16 := by
    rw [hd, ← mul_div_assoc]
    apply (div_le_iff₀ hMpos).mpr
    nlinarith
  have hexp : Real.exp (L1 * ‖w - y‖) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 16 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hgrad := GeneralizedAccelerated.gradient_growth hL0.le hL1 hg hH w y
  have hbound : ‖g w - g y‖ ≤ 2 * (L0 + L1 * (‖v‖ + ‖g y - v‖)) * ‖w - y‖ := by
    calc
      _ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖w - y‖) * ‖w - y‖ := hgrad
      _ ≤ (L0 + L1 * (‖v‖ + ‖g y - v‖)) * 2 * ‖w - y‖ := by
        gcongr
        · simpa [add_comm] using norm_le_norm_sub_add (g y) v
      _ = _ := by ring
  have he : M • (w - y) = -v := by
    dsimp [w]
    match_scalars
    all_goals field_simp [hMpos.ne'] <;> ring
  change ‖g w + M • (w - y)‖ ≤ _
  rw [he, ← sub_eq_add_neg]
  have ht : ‖g w - v‖ ≤ ‖g w - g y‖ + ‖g y - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle (g w) (g y) v
  have hcurv := mul_le_mul_of_nonneg_right hM (norm_nonneg (w-y))
  have herr := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (g y-v))
  nlinarith [norm_nonneg (g y-v), norm_nonneg (w-y)]

omit [CompleteSpace E] in
lemma ms_inner_error {M : ℝ} (hM : 0 < M) (v d e₁ e₂ : E)
    (hr : ‖v + M • d‖ ≤ M / 4 * ‖d‖ + 2 * ‖e₁‖) :
    ⟪v + e₂, d⟫ - ⟪e₂, d⟫ ≤ -(3 * M / 8) * ‖d‖ ^ 2 -
      ‖v + e₂‖ ^ 2 / (2 * M) + (8 * ‖e₁‖ ^ 2 + 6 * ‖e₂‖ ^ 2) / M := by
  have he : v + e₂ + M • d = (v + M • d) + e₂ := by module
  have hb : ‖v + e₂ + M • d‖ ≤ M / 4 * ‖d‖ + 2 * ‖e₁‖ + ‖e₂‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hr le_rfl)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hsq : ‖v + e₂ + M • d‖ ^ 2 ≤ M ^ 2 / 8 * ‖d‖ ^ 2 +
      16 * ‖e₁‖ ^ 2 + 4 * ‖e₂‖ ^ 2 := by
    nlinarith [sq_nonneg (M / 4 * ‖d‖ - (2 * ‖e₁‖ + ‖e₂‖)),
      sq_nonneg (2 * ‖e₁‖ - ‖e₂‖)]
  rw [norm_add_sq_real] at hsq
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
  have hi := real_inner_le_norm (-e₂) d
  simp only [inner_neg_left, norm_neg] at hi
  have hy := sq_nonneg (M * ‖d‖ - 8 * ‖e₂‖)
  have him := mul_le_mul_of_nonneg_left hi hM.le
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * M by positivity)).mp
  field_simp [hM.ne']
  nlinarith

lemma damped_step_error {f : E → ℝ} {g : E → E} {M A a γ : ℝ}
    (hM : 0 < M) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (x z u w e₁ e₂ : E) (hA : 0 ≤ A) (ha : 0 < a)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hweight : γ * a ^ 2 * M = A + a)
    (hr : let y := (A / (A + a)) • x + (a / (A + a)) • z
      ‖g w + M • (w - y)‖ ≤ M / 4 * ‖w - y‖ + 2 * ‖e₁‖) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    let B := A + γ * a
    let xnew := ((1 - γ) * A / B) • x + (γ * (A + a) / B) • w
    B * (f xnew - f u) + 1 / 2 * ‖z - (γ * a) • (g w + e₂) - u‖ ^ 2 +
        γ * (A + a) * (3 * M / 8) * ‖w - y‖ ^ 2 ≤
      A * (f x - f u) + 1 / 2 * ‖z - u‖ ^ 2 - (γ * a) * ⟪e₂, z - u⟫ +
        (γ * a) ^ 2 * (8 * ‖e₁‖ ^ 2 + 6 * ‖e₂‖ ^ 2) := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  let B := A + γ * a
  let xnew := ((1 - γ) * A / B) • x + (γ * (A + a) / B) • w
  change ‖g w + M • (w - y)‖ ≤ M / 4 * ‖w - y‖ + 2 * ‖e₁‖ at hr
  change B * (f xnew - f u) + 1 / 2 * ‖z - (γ * a) • (g w + e₂) - u‖ ^ 2 +
    γ * (A + a) * (3 * M / 8) * ‖w - y‖ ^ 2 ≤ _
  have hB : 0 < B := by dsimp [B]; positivity
  have hAa : 0 < A + a := by positivity
  have hx := Gradient.convex_support hc hg w x
  have hu := Gradient.convex_support hc hg w u
  have hid : A • (x - w) + a • (u - w) =
      a • (u - z) + (A + a) • (y - w) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hAa.ne'] <;> ring
  have hi := congrArg (fun v => ⟪g w, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hneg (v₁ v₂ : E) : ⟪g w, v₁ - v₂⟫ = -⟪g w, v₂ - v₁⟫ := by
    rw [← inner_neg_right]
    congr 1
    module
  rw [hneg u z, hneg y w] at hi
  have hs : (A + a) * (f w - f u) ≤ A * (f x - f u) +
      a * ⟪g w, z - u⟫ + (A + a) * ⟪g w, w - y⟫ := by
    have hx' := mul_le_mul_of_nonneg_left hx hA
    have hu' := mul_le_mul_of_nonneg_left hu ha.le
    nlinarith
  have hsum : (1 - γ) * A / B + γ * (A + a) / B = 1 := by
    dsimp [B]
    field_simp; ring
  have hmix := hc.2 (mem_univ x) (mem_univ w)
    (show 0 ≤ (1 - γ) * A / B by positivity)
    (show 0 ≤ γ * (A + a) / B by positivity) hsum
  change f xnew ≤ _ at hmix
  have hmix' := mul_le_mul_of_nonneg_left hmix hB.le
  have hmix'' : B * (f xnew - f u) ≤
      (1 - γ) * A * (f x - f u) + γ * (A + a) * (f w - f u) := by
    have he : B * (((1 - γ) * A / B) • f x +
        (γ * (A + a) / B) • f w) =
        (1 - γ) * A * f x + γ * (A + a) * f w := by
      simp only [smul_eq_mul]
      field_simp

    rw [he] at hmix'
    dsimp [B] at hmix' ⊢
    nlinarith
  have hs' := mul_le_mul_of_nonneg_left hs hγ.le
  have hinner := ms_inner_error hM (g w) (w-y) e₁ e₂ hr
  simp only [inner_add_left, add_sub_cancel_right] at hinner
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ γ * (A + a) by positivity)
  have hn : z - (γ * a) • (g w + e₂) - u = (z - u) - (γ * a) • (g w + e₂) := by module
  rw [hn, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_right]
  rw [← real_inner_comm (z-u) (g w), ← real_inner_comm (z-u) e₂]
  have hscale : γ * (A + a) / M = (γ * a) ^ 2 := by
    rw [← hweight]
    field_simp

  have heq : γ * (A + a) *
      (-(3 * M / 8) * ‖w-y‖ ^ 2 - ‖g w + e₂‖ ^ 2 / (2 * M) +
        (8 * ‖e₁‖ ^ 2 + 6 * ‖e₂‖ ^ 2) / M) =
      -γ * (A + a) * (3 * M / 8) * ‖w-y‖ ^ 2 -
        (γ * a) ^ 2 * ‖g w + e₂‖ ^ 2 / 2 +
        (γ * a) ^ 2 * (8 * ‖e₁‖ ^ 2 + 6 * ‖e₂‖ ^ 2) := by
    rw [← hscale]
    ring
  rw [heq] at hinner'
  dsimp [B] at hmix'' ⊢
  nlinarith only [hmix'', hs', hinner']

end OracleTemplate.StochasticGeneralized
