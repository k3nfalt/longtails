import LongTails.Proofs.GeneralizedGradientStep
import LongTails.Proofs.GdConvex
import LongTails.Proofs.GeneralizedComparison
import LongTails.Proofs.GuardedGeneralizedGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.CoarseGeneralized

lemma log_mul_exp_quarter {u : ℝ} (hu : 1 ≤ u) :
    Real.log u * Real.exp (Real.log u / 4) ≤ 2 * u := by
  have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hl : 0 ≤ Real.log u := Real.log_nonneg hu
  have he : Real.exp (Real.log u / 4) ≤ Real.sqrt u := by
    calc
      _ ≤ Real.exp (Real.log u / 2) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.sqrt u := by
        rw [← Real.log_sqrt hup.le, Real.exp_log (Real.sqrt_pos.mpr hup)]
  have hb := GeneralizedAccelerated.log_le_twice_sqrt hup
  calc
    _ ≤ (2 * Real.sqrt u) * Real.sqrt u :=
      mul_le_mul hb he (Real.exp_pos _).le (by positivity)
    _ = 2 * u := by nlinarith [Real.sq_sqrt hup.le]

lemma ray_surplus_scalar {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hG : 1 ≤ L1 * G / L0) :
    let t := Real.log (L1 * G / L0) / (4 * L1)
    G * Real.log (L1 * G / L0) / (8 * L1) ≤
      t * G - L0 * t ^ 2 * Real.exp (L1 * t) := by
  dsimp only
  have hl : 0 ≤ Real.log (L1 * G / L0) := Real.log_nonneg hG
  have hb := log_mul_exp_quarter hG
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ L0 * Real.log (L1 * G / L0) from mul_nonneg hL0.le hl)
  have he : L1 * (Real.log (L1 * G / L0) / (4 * L1)) =
      Real.log (L1 * G / L0) / 4 := by field_simp
  rw [he]
  have hh : L0 * (Real.log (L1 * G / L0) *
      Real.exp (Real.log (L1 * G / L0) / 4)) * Real.log (L1 * G / L0) ≤
      2 * L1 * G * Real.log (L1 * G / L0) := by
    have hc : L0 * (2 * (L1 * G / L0)) = 2 * L1 * G := by field_simp
    nlinarith
  apply (le_of_sub_nonneg ?_)
  field_simp
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma objective_growth_from_minimizer {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {u : E} (hu : g u = 0) (z : E) :
    f z - f u ≤ L0 * ‖z - u‖ ^ 2 * Real.exp (L1 * ‖z - u‖) := by
  have hs := Gradient.convex_support hc hf z u
  have hi : ⟪g z, u - z⟫ = -⟪g z, z - u⟫ := by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [hi] at hs
  have hn := real_inner_le_norm (g z) (z - u)
  have hb := GeneralizedAccelerated.gradient_growth hL0 hL1 hg hH z u
  simp only [hu, sub_zero, norm_zero, mul_zero, add_zero] at hb
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (z - u))
  nlinarith

lemma anchored_ray_surplus {f : E → ℝ} {g : E → E} {L0 L1 t : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {u y d : E} (hu : g u = 0) (hd : ‖d‖ = 1) (ht : 0 ≤ t) :
    f y - f u + t * ⟪g y, d⟫ - L0 * t ^ 2 * Real.exp (L1 * t) ≤
      ⟪g y, y - u⟫ := by
  have hz : ‖u + t • d - u‖ = t := by
    rw [add_sub_cancel_left, norm_smul, hd, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ht]
  have hb := objective_growth_from_minimizer hL0 hL1 hc hf hg hH hu (u + t • d)
  rw [hz] at hb
  have hs := Gradient.convex_support hc hf y (u + t • d)
  have he : u + t • d - y = t • d - (y - u) := by abel
  rw [he, inner_sub_right, inner_smul_right] at hs
  linarith

lemma anchored_log_surplus {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {u y : E} (hu : g u = 0) (hG : 1 ≤ L1 * ‖g y‖ / L0) :
    f y - f u + ‖g y‖ * Real.log (L1 * ‖g y‖ / L0) / (8 * L1) ≤
      ⟪g y, y - u⟫ := by
  have hGp : 0 < ‖g y‖ := by
    have hh := (le_div_iff₀ hL0).mp hG
    nlinarith
  let d := (1 / ‖g y‖) • g y
  have hd : ‖d‖ = 1 := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hi : ⟪g y, d⟫ = ‖g y‖ := by
    dsimp [d]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have ht : 0 ≤ Real.log (L1 * ‖g y‖ / L0) / (4 * L1) :=
    div_nonneg (Real.log_nonneg hG) (by positivity)
  have hr := anchored_ray_surplus (y := y) hL0.le hL1.le hc hf hg hH hu hd ht
  rw [hi] at hr
  have hs := ray_surplus_scalar hL0 hL1 hG
  dsimp only at hs
  linarith

lemma noisy_anchored_surplus {f : E → ℝ} {g : E → E} {L0 L1 R ζ : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {u y h : E} (hu : g u = 0) (hy : ‖y - u‖ ≤ R)
    (hζ : 0 ≤ ζ) (he : ‖h - g y‖ ≤ ζ) (hsmall : 2 * ζ ≤ ‖h‖)
    (hlarge : 1 ≤ L1 * ‖h‖ / (2 * L0))
    (hnoise : ζ * R ≤ ‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (64 * L1)) :
    f y - f u + ‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (64 * L1) ≤
      ⟪h, y - u⟫ := by
  have hn := norm_le_norm_sub_add h (g y)
  have hhalf : ‖h‖ / 2 ≤ ‖g y‖ := by linarith
  have hratio : L1 * ‖h‖ / (2 * L0) ≤ L1 * ‖g y‖ / L0 := by
    apply (div_le_div_iff₀ (by positivity) hL0).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hL1.le hL0.le)
    nlinarith
  have hpos : 0 < L1 * ‖h‖ / (2 * L0) := lt_of_lt_of_le zero_lt_one hlarge
  have hl := Real.log_le_log hpos hratio
  have hln : 0 ≤ Real.log (L1 * ‖h‖ / (2 * L0)) := Real.log_nonneg hlarge
  have hm := mul_le_mul hhalf hl hln (norm_nonneg (g y))
  have hs := anchored_log_surplus hL0 hL1 hc hf hg hH hu (hlarge.trans hratio)
  have hi := real_inner_le_norm (g y - h) (y - u)
  rw [inner_sub_left, norm_sub_rev (g y) h] at hi
  have hb := mul_le_mul he hy (norm_nonneg (y - u)) hζ
  have hd : ‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (16 * L1) ≤
      ‖g y‖ * Real.log (L1 * ‖g y‖ / L0) / (8 * L1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hm hL1.le
    nlinarith
  have hp : 0 ≤ ‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (64 * L1) := by positivity
  have hid : ‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (16 * L1) =
      4 * (‖h‖ * Real.log (L1 * ‖h‖ / (2 * L0)) / (64 * L1)) := by ring
  rw [hid] at hd
  linarith

lemma uncertain_direction_bounds {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    {x v y h : E} {t ζ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hζ : 0 ≤ ζ)
    (hy : y = v + t • (x - v)) (he : ‖h - g y‖ ≤ ζ)
    (hdir : |⟪h, x - v⟫| ≤ ζ * ‖x - v‖) :
    f y ≤ f x + 2 * ζ * ‖x - v‖ ∧
      ⟪h, y - v⟫ ≤ ζ * ‖x - v‖ := by
  have hi := real_inner_le_norm (h - g y) (x - v)
  rw [inner_sub_left] at hi
  have hb := mul_le_mul_of_nonneg_right he (norm_nonneg (x - v))
  have hlo := (abs_le.mp hdir).1
  have hup := (abs_le.mp hdir).2
  have hglo : -(2 * ζ * ‖x - v‖) ≤ ⟪g y, x - v⟫ := by linarith
  have hs := Gradient.convex_support hc hf y x
  have hxy : x - y = (1 - t) • (x - v) := by rw [hy]; module
  rw [hxy, inner_smul_right] at hs
  have hm := mul_le_mul_of_nonneg_left hglo (sub_nonneg.mpr ht1)
  have hn : 0 ≤ ζ * ‖x - v‖ := mul_nonneg hζ (norm_nonneg _)
  have htt : 0 ≤ t * (ζ * ‖x - v‖) := mul_nonneg ht hn
  constructor
  · nlinarith
  · have hyv : y - v = t • (x - v) := by rw [hy]; abel
    rw [hyv, inner_smul_right]
    have hh := mul_le_mul_of_nonneg_left hup ht
    have hh' := mul_le_mul_of_nonneg_right ht1 hn
    nlinarith

lemma noisy_short_descent {f : E → ℝ} {g : E → E} {L0 L1 ζ η : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {y h : E} (hη : 0 ≤ η) (he : ‖h - g y‖ ≤ ζ)
    (hnoise : ζ ≤ ‖h‖ / 4) (hshort : L1 * (η * ‖h‖) ≤ 1 / 4)
    (hstep : η * (L0 + L1 * (‖h‖ + ζ)) ≤ 1 / 4) :
    f (y - η • h) ≤ f y - η * ‖h‖ ^ 2 / 2 := by
  have hd : ‖y - η • h - y‖ = η * ‖h‖ := by
    have hh : y - η • h - y = -(η • h) := by abel
    rw [hh, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  have hb := LongTails.Proofs.GuardedGeneralizedGeometry.short_upper
    hL0 hL1 hf hg hH y (y - η • h) (by rw [hd]; exact hshort)
  have hi : ⟪g y, y - η • h - y⟫ = -η * ⟪g y, h⟫ := by
    have hh : y - η • h - y = -(η • h) := by abel
    rw [hh, inner_neg_right, inner_smul_right]
    ring
  rw [hd, hi] at hb
  have hn := norm_le_norm_sub_add (g y) h
  rw [norm_sub_rev (g y) h] at hn
  have hn' : ‖g y‖ ≤ ‖h‖ + ζ := by linarith
  have he' := real_inner_le_norm (h - g y) h
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at he'
  have hem := mul_le_mul_of_nonneg_right he (norm_nonneg h)
  have hem' := mul_le_mul_of_nonneg_right hnoise (norm_nonneg h)
  have hip : 3 * ‖h‖ ^ 2 / 4 ≤ ⟪g y, h⟫ := by nlinarith
  have hic := mul_le_mul_of_nonneg_left hip hη
  have hl := mul_le_mul_of_nonneg_left hn' hL1
  have hl' := mul_le_mul_of_nonneg_left hl hη
  have hc : η * (L0 + L1 * ‖g y‖) ≤ 1 / 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hη (sq_nonneg ‖h‖))
  nlinarith

lemma bracket_endpoint_bounds {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hf : ∀ x, HasGradientAt f (g x) x)
    {x v y z h : E} {t ζ B : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hζ : 0 ≤ ζ) (hB : 0 ≤ B) (hy : y = v + t • (x - v))
    (he : ‖h - g y‖ ≤ ζ) (hleft : ⟪g z, x - v⟫ ≤ 0)
    (hright : 0 ≤ ⟪g y, x - v⟫) (hgrad : ‖g y - g z‖ ≤ B) :
    f y ≤ f x ∧ ⟪h, y - v⟫ ≤ (B + ζ) * ‖x - v‖ := by
  have hs := Gradient.convex_support hc hf y x
  have hxy : x - y = (1 - t) • (x - v) := by rw [hy]; module
  rw [hxy, inner_smul_right] at hs
  have hp := mul_nonneg (sub_nonneg.mpr ht1) hright
  have heinner := real_inner_le_norm (h - g y) (x - v)
  have hginner := real_inner_le_norm (g y - g z) (x - v)
  rw [inner_sub_left] at heinner hginner
  have hem := mul_le_mul_of_nonneg_right he (norm_nonneg (x - v))
  have hgm := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (x - v))
  have hb : ⟪h, x - v⟫ ≤ (B + ζ) * ‖x - v‖ := by linarith
  constructor
  · linarith
  · have hyv : y - v = t • (x - v) := by rw [hy]; abel
    rw [hyv, inner_smul_right]
    exact (mul_le_mul_of_nonneg_left hb ht).trans
      (mul_le_of_le_one_left (mul_nonneg (add_nonneg hB hζ) (norm_nonneg _)) ht1)

lemma normalized_noisy_descent {f : E → ℝ} {g : E → E} {L0 L1 ζ : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {y h : E} (he : ‖h - g y‖ ≤ ζ) (hnoise : ζ ≤ ‖h‖ / 4) :
    f (y - (1 / (16 * (L0 + L1 * ‖h‖))) • h) ≤
      f y - (‖h‖ ^ 2 / (L0 + L1 * ‖h‖)) / 32 := by
  have hden : 0 < L0 + L1 * ‖h‖ := by positivity
  have hη : 0 ≤ 1 / (16 * (L0 + L1 * ‖h‖)) := by positivity
  have hshort : L1 * (1 / (16 * (L0 + L1 * ‖h‖)) * ‖h‖) ≤ 1 / 4 := by
    have heq : L1 * (1 / (16 * (L0 + L1 * ‖h‖)) * ‖h‖) =
        (L1 * ‖h‖) / (16 * (L0 + L1 * ‖h‖)) := by ring
    rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hL1 (norm_nonneg h)]
  have hstep : 1 / (16 * (L0 + L1 * ‖h‖)) *
      (L0 + L1 * (‖h‖ + ζ)) ≤ 1 / 4 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    have hn := mul_le_mul_of_nonneg_left hnoise hL1
    nlinarith [mul_nonneg hL1 (norm_nonneg h)]
  have hb := noisy_short_descent hL0.le hL1 hf hg hH hη he hnoise hshort hstep
  convert hb using 1
  field_simp
  ring

omit [CompleteSpace E] in
lemma segment_radius {x v u : E} {t R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : ‖x - u‖ ≤ R) (hv : ‖v - u‖ ≤ R) :
    ‖v + t • (x - v) - u‖ ≤ R := by
  have he : v + t • (x - v) - u = (1 - t) • (v - u) + t • (x - u) := by module
  rw [he]
  calc
    _ ≤ ‖(1 - t) • (v - u)‖ + ‖t • (x - u)‖ := norm_add_le _ _
    _ = (1 - t) * ‖v - u‖ + t * ‖x - u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht1)]
    _ ≤ (1 - t) * R + t * R := add_le_add
      (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hx ht)
    _ = R := by ring

omit [CompleteSpace E] in
lemma direction_error {g h d : E} {ζ : ℝ} (he : ‖h - g‖ ≤ ζ) :
    |⟪h, d⟫ - ⟪g, d⟫| ≤ ζ * ‖d‖ := by
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right he (norm_nonneg d))

omit [CompleteSpace E] in
lemma bracket_gradient_difference {g : E → E} {L0 L1 ζ : ℝ} {y z h : E}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (he : ‖h - g y‖ ≤ ζ) (hnoise : ζ ≤ ‖h‖)
    (hsmall : L1 * ‖z - y‖ ≤ 1 / 4) :
    ‖g y - g z‖ ≤ 4 * (L0 + L1 * ‖h‖) * ‖z - y‖ := by
  have hb := LongTails.Proofs.GuardedGeneralizedGeometry.short_gradient_difference
    hL0 hL1 hg hH y z hsmall
  rw [norm_sub_rev (g z) (g y)] at hb
  have hn := norm_le_norm_sub_add (g y) h
  rw [norm_sub_rev (g y) h] at hn
  have hh : ‖g y‖ ≤ 2 * ‖h‖ := by linarith
  have hm := mul_le_mul_of_nonneg_left hh hL1
  have hc : 2 * (L0 + L1 * ‖g y‖) ≤ 4 * (L0 + L1 * ‖h‖) := by linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma radius_pair_distance {x v u : E} {R : ℝ}
    (hx : ‖x - u‖ ≤ R) (hv : ‖v - u‖ ≤ R) : ‖x - v‖ ≤ 2 * R := by
  have he : x - v = (x - u) - (v - u) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

omit [CompleteSpace E] in
lemma interval_segment_distance {x v u : E} {lo hi R ρ : ℝ}
    (hx : ‖x - u‖ ≤ R) (hv : ‖v - u‖ ≤ R)
    (horder : lo ≤ hi) (hwidth : hi - lo ≤ ρ) :
    ‖(v + hi • (x - v)) - (v + lo • (x - v))‖ ≤ 2 * R * ρ := by
  have hd := radius_pair_distance hx hv
  have he : (v + hi • (x - v)) - (v + lo • (x - v)) = (hi - lo) • (x - v) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr horder)]
  have hρ : 0 ≤ ρ := (sub_nonneg.mpr horder).trans hwidth
  have hm := mul_le_mul hwidth hd (norm_nonneg (x - v)) hρ
  nlinarith only [hm]

lemma small_radius_gap {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    {u x : E} (hu : g u = 0) (hdist : ‖x - u‖ ≤ R) (hR : L1 * R ≤ 1) :
    f x - f u ≤ 3 * L0 * R ^ 2 := by
  have hb := objective_growth_from_minimizer hL0 hL1 hc hf hg hH hu x
  have hs := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have he : Real.exp (L1 * ‖x - u‖) ≤ 3 := by
    apply (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hdist hL1).trans hR)).trans
    exact Real.exp_one_lt_three.le
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hs hL0) he
    (Real.exp_nonneg _) (mul_nonneg hL0 (sq_nonneg R))
  nlinarith only [hb, hm]

end OracleTemplate.CoarseGeneralized
