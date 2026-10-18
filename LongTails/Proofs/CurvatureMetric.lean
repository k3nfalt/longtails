import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace LongTails.Proofs.CurvatureMetric

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def metricNorm (B : E →L[ℝ] E) (x : E) : ℝ := Real.sqrt ⟪x, B x⟫

lemma metricNorm_nonneg (B : E →L[ℝ] E) (x : E) : 0 ≤ metricNorm B x :=
  Real.sqrt_nonneg _

lemma metricNorm_sq (B : E →L[ℝ] E) (hB : ∀ x, 0 ≤ ⟪x, B x⟫) (x : E) :
    metricNorm B x ^ 2 = ⟪x, B x⟫ := Real.sq_sqrt (hB x)

lemma quadratic_sub_le (B : E →L[ℝ] E) (hp : ∀ x, 0 ≤ ⟪x, B x⟫) (x y : E) :
    ⟪x - y, B (x - y)⟫ ≤ 2 * ⟪x, B x⟫ + 2 * ⟪y, B y⟫ := by
  have h := hp (x + y)
  simp only [map_add, inner_add_left, inner_add_right] at h
  simp only [map_sub, inner_sub_left, inner_sub_right]
  linarith

lemma metricNorm_sub_three_sq (B : E →L[ℝ] E) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (v x u y : E) :
    metricNorm B (v - x) ^ 2 ≤ 2 * metricNorm B (v - u) ^ 2 +
      4 * metricNorm B (x - y) ^ 2 + 4 * metricNorm B (u - y) ^ 2 := by
  have h₁ := quadratic_sub_le B hp (v - u) (x - u)
  have h₂ := quadratic_sub_le B hp (x - y) (u - y)
  have he₁ : (v - u) - (x - u) = v - x := by abel
  have he₂ : (x - y) - (u - y) = x - u := by abel
  rw [he₁] at h₁
  rw [he₂] at h₂
  simp only [metricNorm_sq B hp]
  linarith

@[instance_reducible] noncomputable def formCore (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫) :
    PreInnerProductSpace.Core ℝ E where
  inner x y := ⟪x, B y⟫
  conj_inner_symm x y := by simpa only [conj_trivial] using (hs y x).trans (real_inner_comm _ _)
  re_inner_nonneg x := hp x
  add_left x y z := inner_add_left x y (B z)
  smul_left x y r := by simp only [real_inner_smul_left, conj_trivial]

lemma metric_cauchy (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (x y : E) : |⟪x, B y⟫| ≤ metricNorm B x * metricNorm B y := by
  let : PreInnerProductSpace.Core ℝ E := formCore B hs hp
  have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) x y
  exact h

lemma metricNorm_add_le (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (x y : E) : metricNorm B (x + y) ≤ metricNorm B x + metricNorm B y := by
  have hc := (abs_le.mp (metric_cauchy B hs hp x y)).2
  have hxy : ⟪y, B x⟫ = ⟪x, B y⟫ := (hs y x).trans (real_inner_comm _ _)
  have he : metricNorm B (x + y) ^ 2 =
      metricNorm B x ^ 2 + 2 * ⟪x, B y⟫ + metricNorm B y ^ 2 := by
    simp only [metricNorm_sq B hp, map_add, inner_add_left, inner_add_right, hxy]
    ring
  nlinarith [metricNorm_nonneg B x, metricNorm_nonneg B y, metricNorm_nonneg B (x + y)]

lemma metricNorm_smul (B : E →L[ℝ] E) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (a : ℝ) (x : E) : metricNorm B (a • x) = |a| * metricNorm B x := by
  have he : metricNorm B (a • x) ^ 2 = a ^ 2 * metricNorm B x ^ 2 := by
    simp only [metricNorm_sq B hp, map_smul, real_inner_smul_left, inner_smul_right]
    ring
  nlinarith [metricNorm_nonneg B (a • x), metricNorm_nonneg B x, abs_nonneg a,
    sq_abs a, mul_nonneg (abs_nonneg a) (metricNorm_nonneg B x)]

lemma metricNorm_lower (B : E →L[ℝ] E) {μ : ℝ} (hμ : 0 ≤ μ)
    (hl : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪x, B x⟫) (x : E) :
    Real.sqrt μ * ‖x‖ ≤ metricNorm B x := by
  have hp : ∀ y, 0 ≤ ⟪y, B y⟫ := fun y => (mul_nonneg hμ (sq_nonneg _)).trans (hl y)
  have hn := metricNorm_sq B hp x
  have hm := Real.sq_sqrt hμ
  have hh := hl x
  nlinarith [Real.sqrt_nonneg μ, norm_nonneg x, metricNorm_nonneg B x,
    mul_nonneg (Real.sqrt_nonneg μ) (norm_nonneg x)]

lemma isUnit_of_lower [CompleteSpace E] (B : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (hl : ∀ x, μ * ‖x‖ ^ 2 ≤ ⟪x, B x⟫) : IsUnit B := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map B
    (c := ⟨μ, hμ.le⟩) hμ
  intro x
  change ‖x‖ ^ 2 * μ ≤ ‖⟪B x, x⟫‖
  rw [real_inner_comm, Real.norm_eq_abs]
  have hh : ‖x‖ ^ 2 * μ ≤ ⟪x, B x⟫ := by simpa only [mul_comm] using hl x
  exact hh.trans (le_abs_self _)

lemma inverse_apply (B : E →L[ℝ] E) (hB : IsUnit B) (x : E) :
    B (Ring.inverse B x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) (Ring.mul_inverse_cancel B hB)
  exact h

lemma apply_inverse (B : E →L[ℝ] E) (hB : IsUnit B) (x : E) :
    Ring.inverse B (B x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel B hB)
  exact h

lemma dual_cauchy (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (g x : E) : |⟪g, x⟫| ≤ metricNorm B (Ring.inverse B g) * metricNorm B x := by
  have h := metric_cauchy B hs hp (Ring.inverse B g) x
  rw [hs, inverse_apply B hB] at h
  exact h

lemma residual_direction_bound (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {r₁ r₂ d : E} {t L : ℝ} (ht : 0 ≤ t)
    (hr : metricNorm B (Ring.inverse B (r₁ - r₂)) ≤ L * metricNorm B (t • d)) :
    |⟪r₁, d⟫ - ⟪r₂, d⟫| ≤ L * metricNorm B d ^ 2 * t := by
  have hc := dual_cauchy B hB hs hp (r₁ - r₂) d
  rw [inner_sub_left] at hc
  rw [metricNorm_smul B hp, abs_of_nonneg ht] at hr
  have hm := mul_le_mul_of_nonneg_right hr (metricNorm_nonneg B d)
  nlinarith only [hc, hm]

lemma dominated_cauchy (A B : E →L[ℝ] E)
    (hAs : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) (hAp : ∀ x, 0 ≤ ⟪x, A x⟫)
    (hBp : ∀ x, 0 ≤ ⟪x, B x⟫) {L : ℝ} (hL : 0 ≤ L)
    (hdom : ∀ x, ⟪x, A x⟫ ≤ L * ⟪x, B x⟫) (x y : E) :
    |⟪x, A y⟫| ≤ L * metricNorm B x * metricNorm B y := by
  have hc := metric_cauchy A hAs hAp x y
  have hx : metricNorm A x ≤ Real.sqrt L * metricNorm B x := by
    have hh := hdom x
    rw [← metricNorm_sq A hAp, ← metricNorm_sq B hBp] at hh
    nlinarith [metricNorm_nonneg A x, metricNorm_nonneg B x,
      Real.sqrt_nonneg L, Real.sq_sqrt hL,
      mul_nonneg (Real.sqrt_nonneg L) (metricNorm_nonneg B x)]
  have hy : metricNorm A y ≤ Real.sqrt L * metricNorm B y := by
    have hh := hdom y
    rw [← metricNorm_sq A hAp, ← metricNorm_sq B hBp] at hh
    nlinarith [metricNorm_nonneg A y, metricNorm_nonneg B y,
      Real.sqrt_nonneg L, Real.sq_sqrt hL,
      mul_nonneg (Real.sqrt_nonneg L) (metricNorm_nonneg B y)]
  calc
    _ ≤ metricNorm A x * metricNorm A y := hc
    _ ≤ (Real.sqrt L * metricNorm B x) * (Real.sqrt L * metricNorm B y) :=
      mul_le_mul hx hy (metricNorm_nonneg A y)
        (mul_nonneg (Real.sqrt_nonneg L) (metricNorm_nonneg B x))
    _ = _ := by
      calc
        _ = (Real.sqrt L) ^ 2 * metricNorm B x * metricNorm B y := by ring
        _ = _ := by rw [Real.sq_sqrt hL]

lemma prox_nonexpansive (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {ψ : E → ℝ} {z₁ z₂ t₁ t₂ : E}
    (h₁ : ψ z₁ ≤ ψ z₂ + ⟪B (z₁ - t₁), z₂ - z₁⟫)
    (h₂ : ψ z₂ ≤ ψ z₁ + ⟪B (z₂ - t₂), z₁ - z₂⟫) :
    metricNorm B (z₁ - z₂) ≤ metricNorm B (t₁ - t₂) := by
  have he : ⟪B (z₁ - t₁), z₂ - z₁⟫ + ⟪B (z₂ - t₂), z₁ - z₂⟫ =
      ⟪z₁ - z₂, B (t₁ - t₂)⟫ - ⟪z₁ - z₂, B (z₁ - z₂)⟫ := by
    have ht (t z : E) : ⟪t, B z⟫ = ⟪z, B t⟫ := (hs t z).trans (real_inner_comm _ _)
    simp only [map_sub, inner_sub_left, inner_sub_right, ← hs]
    rw [ht t₁ z₂, ht t₁ z₁, ht t₂ z₁, ht t₂ z₂]
    ring
  have hc := (abs_le.mp (metric_cauchy B hs hp (z₁ - z₂) (t₁ - t₂))).2
  have hsum : 0 ≤ ⟪B (z₁ - t₁), z₂ - z₁⟫ + ⟪B (z₂ - t₂), z₁ - z₂⟫ := by
    linarith
  rw [he, ← metricNorm_sq B hp] at hsum
  nlinarith [metricNorm_nonneg B (z₁ - z₂), metricNorm_nonneg B (t₁ - t₂)]

lemma metricNorm_neg (B : E →L[ℝ] E) (hp : ∀ x, 0 ≤ ⟪x, B x⟫) (x : E) :
    metricNorm B (-x) = metricNorm B x := by
  simpa using metricNorm_smul B hp (-1) x

lemma metricNorm_sub_le (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (x y : E) : metricNorm B (x - y) ≤ metricNorm B x + metricNorm B y := by
  simpa only [sub_eq_add_neg, metricNorm_neg B hp] using metricNorm_add_le B hs hp x (-y)

lemma proximal_gradient_stability (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {ψ : E → ℝ} {z₁ z₂ y₁ y₂ g₁ g₂ : E} {L : ℝ}
    (h₁ : ψ z₁ ≤ ψ z₂ + ⟪g₁ + B (z₁ - y₁), z₂ - z₁⟫)
    (h₂ : ψ z₂ ≤ ψ z₁ + ⟪g₂ + B (z₂ - y₂), z₁ - z₂⟫)
    (hg : metricNorm B (Ring.inverse B (g₁ - g₂)) ≤ L * metricNorm B (y₁ - y₂)) :
    metricNorm B (z₁ - z₂) ≤ (1 + L) * metricNorm B (y₁ - y₂) := by
  have he (z y g : E) : B (z - (y - Ring.inverse B g)) = g + B (z - y) := by
    simp only [map_sub, inverse_apply B hB]
    abel
  have h := prox_nonexpansive B hs hp (t₁ := y₁ - Ring.inverse B g₁)
    (t₂ := y₂ - Ring.inverse B g₂) (by simpa only [he] using h₁)
      (by simpa only [he] using h₂)
  have heq : y₁ - Ring.inverse B g₁ - (y₂ - Ring.inverse B g₂) =
      (y₁ - y₂) - Ring.inverse B (g₁ - g₂) := by
    rw [map_sub]
    abel
  rw [heq] at h
  have ht := metricNorm_sub_le B hs hp (y₁ - y₂) (Ring.inverse B (g₁ - g₂))
  linarith

lemma residual_stability (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {z₁ z₂ y₁ y₂ : E} {L : ℝ}
    (hz : metricNorm B (z₁ - z₂) ≤ (1 + L) * metricNorm B (y₁ - y₂)) :
    metricNorm B (Ring.inverse B (B (y₁ - z₁) - B (y₂ - z₂))) ≤
      (2 + L) * metricNorm B (y₁ - y₂) := by
  rw [← map_sub, apply_inverse B hB]
  have he : y₁ - z₁ - (y₂ - z₂) = (y₁ - y₂) - (z₁ - z₂) := by abel
  rw [he]
  have ht := metricNorm_sub_le B hs hp (y₁ - y₂) (z₁ - z₂)
  linarith

lemma quadratic_perturbation (A C : E →L[ℝ] E) (u : E) :
    ⟪u, C u⟫ ≤ ⟪u, A u⟫ + ‖C - A‖ * ‖u‖ ^ 2 := by
  have hc := (abs_le.mp (abs_real_inner_le_norm u ((C - A) u))).2
  have hn := (C - A).le_opNorm u
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg u)
  simp only [sub_apply, inner_sub_right] at hc hn hm
  nlinarith

lemma metric_tube_domination (B A C : E →L[ℝ] E) {z w : E} {μ H ρ c a : ℝ}
    (hμ : 0 < μ) (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hl : ∀ u, μ * ‖u‖ ^ 2 ≤ ⟪u, B u⟫)
    (hA : ∀ u, ⟪u, A u⟫ ≤ a * ⟪u, B u⟫)
    (hLip : ‖C - A‖ ≤ H * ‖w - z‖)
    (hr : metricNorm B (w - z) ≤ ρ)
    (hscale : H * ρ ≤ c * μ * Real.sqrt μ) :
    ∀ u, ⟪u, C u⟫ ≤ (a + c) * ⟪u, B u⟫ := by
  have he := metricNorm_lower B hμ.le hl (w - z)
  have hm := mul_le_mul_of_nonneg_left (he.trans hr) hH
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsmall : H * ‖w - z‖ ≤ c * μ := by
    nlinarith
  intro u
  have hq := quadratic_perturbation A C u
  have h1 := mul_le_mul_of_nonneg_right (hLip.trans hsmall) (sq_nonneg ‖u‖)
  have h2 := mul_le_mul_of_nonneg_left (hl u) hc
  have h3 := hA u
  nlinarith

lemma metric_momentum_identity (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (v u r : E) (a : ℝ) :
    metricNorm B (v - a • Ring.inverse B r - u) ^ 2 / 2 -
      metricNorm B (v - u) ^ 2 / 2 =
      -a * ⟪r, v - u⟫ + a ^ 2 * metricNorm B (Ring.inverse B r) ^ 2 / 2 := by
  simp only [metricNorm_sq B hp, map_sub, map_smul, inner_sub_left,
    inner_sub_right, inner_smul_right, real_inner_smul_left, inverse_apply B hB]
  rw [hs (Ring.inverse B r) v, hs (Ring.inverse B r) u, inverse_apply B hB,
    real_inner_comm v r, real_inner_comm u r]
  ring

lemma metric_segment_bound (B : E →L[ℝ] E)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {x y z : E} {t R : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : metricNorm B (x - z) ≤ R) (hy : metricNorm B (y - z) ≤ R) :
    metricNorm B (x + t • (y - x) - z) ≤ R := by
  have he : x + t • (y - x) - z = (1 - t) • (x - z) + t • (y - z) := by module
  rw [he]
  have h := metricNorm_add_le B hs hp ((1 - t) • (x - z)) (t • (y - z))
  rw [metricNorm_smul B hp, metricNorm_smul B hp, abs_of_nonneg (sub_nonneg.mpr ht1),
    abs_of_nonneg ht0] at h
  have h₁ := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht1)
  have h₂ := mul_le_mul_of_nonneg_left hy ht0
  nlinarith only [h, h₁, h₂]

end LongTails.Proofs.CurvatureMetric
