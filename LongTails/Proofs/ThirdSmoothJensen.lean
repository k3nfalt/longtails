import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace LongTails.Proofs.ThirdSmoothJensen

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma hessian_interpolation {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (w s : E) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ‖t • fderiv ℝ (gradient f) (w + s) +
      (1 - t) • fderiv ℝ (gradient f) w -
      fderiv ℝ (gradient f) (w + t • s)‖ ≤
      L * t * (1 - t) * ‖s‖ ^ 2 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let z := w + t • s
  let a := H (w + s) - H z - T z (w + s - z)
  let b := H w - H z - T z (w - z)
  have ha := ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT z (w + s)
  have hb := ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT z w
  have h₁ : w + s - z = (1 - t) • s := by dsimp [z]; module
  have h₂ : w - z = -t • s := by dsimp [z]; module
  have hid : t • H (w + s) + (1 - t) • H w - H z = t • a + (1 - t) • b := by
    dsimp [a, b]
    rw [h₁, h₂, map_smul, map_smul]
    module
  change ‖t • H (w + s) + (1 - t) • H w - H z‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖t • a‖ + ‖(1 - t) • b‖ := norm_add_le _ _
    _ = t * ‖a‖ + (1 - t) * ‖b‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
        abs_of_nonneg (sub_nonneg.mpr ht')]
    _ ≤ t * (L * ‖w + s - z‖ ^ 2) + (1 - t) * (L * ‖w - z‖ ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left ha ht)
        (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ht'))
    _ = _ := by
      rw [h₁, h₂]
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht,
        abs_of_nonneg (sub_nonneg.mpr ht')]
      ring

lemma jensen_gradient_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (s : E) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (x y : E) :
    ‖(t • gradient f (x + s) + (1 - t) • gradient f x - gradient f (x + t • s)) -
      (t • gradient f (y + s) + (1 - t) • gradient f y - gradient f (y + t • s))‖ ≤
      (L * t * (1 - t) * ‖s‖ ^ 2) * ‖x - y‖ := by
  let G := fun w => t • gradient f (w + s) +
    (1 - t) • gradient f w - gradient f (w + t • s)
  let D := fun w => t • fderiv ℝ (gradient f) (w + s) +
    (1 - t) • fderiv ℝ (gradient f) w - fderiv ℝ (gradient f) (w + t • s)
  have hg := (GradientDependentLocal.derivative_chain hf).2.1
  have hd (w : E) : HasFDerivAt G (D w) w := by
    have h₁ := (hg (w + s)).comp w ((hasFDerivAt_id w).add_const s)
    have h₂ := (hg (w + t • s)).comp w ((hasFDerivAt_id w).add_const (t • s))
    convert ((h₁.const_smul t).add ((hg w).const_smul (1 - t))).sub h₂ using 1
    · rfl
    · simp only [D, ContinuousLinearMap.comp_id]
  have hm := (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w _ => (hd w).hasFDerivWithinAt)
    (fun w _ => hessian_interpolation hf hL hT w s ht ht')
    (Set.mem_univ y) (Set.mem_univ x)
  exact hm

lemma jensen_gradient_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (w s : E) (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ‖t • gradient f (w + s) + (1 - t) • gradient f w - gradient f (w + t • s)‖ ^ 2 ≤
      2 * (L * t * (1 - t) * ‖s‖ ^ 2) *
        (t * f (w + s) + (1 - t) * f w - f (w + t • s)) := by
  let J := fun x => t * f (x + s) + (1 - t) * f x - f (x + t • s)
  let G := fun x => t • gradient f (x + s) +
    (1 - t) • gradient f x - gradient f (x + t • s)
  let c := L * t * (1 - t) * ‖s‖ ^ 2
  have hcp : 0 < c := by dsimp [c]; positivity
  have hn (x : E) : 0 ≤ J x := by
    have h := hc.2 (Set.mem_univ x) (Set.mem_univ (x + s))
      (le_of_lt (sub_pos.mpr ht')) ht.le (by ring : (1 - t) + t = 1)
    have he : (1 - t) • x + t • (x + s) = x + t • s := by module
    rw [he] at h
    change f (x + t • s) ≤ (1 - t) * f x + t * f (x + s) at h
    dsimp [J]
    linarith
  have hg (x : E) : HasGradientAt J (G x) x := by
    have hd := (GradientDependentLocal.derivative_chain hf).1
    have h₁ := (hd (x + s)).comp x ((hasFDerivAt_id x).add_const s)
    have h₂ := (hd (x + t • s)).comp x ((hasFDerivAt_id x).add_const (t • s))
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((h₁.const_smul t).add ((hd x).const_smul (1 - t))).sub h₂ using 1
    · rfl
    · ext v
      simp [G, innerSL_apply_apply]
  have hl (x y : E) : ‖G x - G y‖ ≤ c * ‖x - y‖ :=
    jensen_gradient_lipschitz hf hL.le hT s ht.le ht'.le x y
  have hdesc := OracleTemplate.Gradient.descent hcp hg hl w
  have hnonneg := hn (w - (1 / c) • G w)
  have hdiv : ‖G w‖ ^ 2 / (2 * c) ≤ J w := by linarith
  have hmul := (div_le_iff₀ (show 0 < 2 * c by positivity)).mp hdiv
  change ‖G w‖ ^ 2 ≤ 2 * c * J w
  nlinarith

lemma quadratic_remainder_self_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    ‖gradient f (w + s) - gradient f w - fderiv ℝ (gradient f) w s‖ ^ 2 ≤
      2 * L * ‖s‖ ^ 2 * (f (w + s) - f w - ⟪gradient f w, s⟫) := by
  by_cases hs : s = 0
  · subst s
    simp
  let r := fun t : ℝ => gradient f (w + s) - gradient f w -
    t⁻¹ • (gradient f (w + t • s) - gradient f w)
  let q := fun t : ℝ => f (w + s) - f w - t⁻¹ * (f (w + t • s) - f w)
  have hp : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hd := GradientDependentLocal.derivative_chain hf
  have hgr : HasDerivAt (fun t : ℝ => gradient f (w + t • s))
      (fderiv ℝ (gradient f) w s) 0 := by
    simpa [Function.comp_def] using (hd.2.1 (w + 0 • s)).comp_hasDerivAt 0 hp
  have hfr : HasDerivAt (fun t : ℝ => f (w + t • s)) ⟪gradient f w, s⟫ 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply, zero_smul, add_zero] using
      (hd.1 (w + 0 • s)).comp_hasDerivAt 0 hp
  have hr : Filter.Tendsto r (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gradient f (w + s) - gradient f w - fderiv ℝ (gradient f) w s)) := by
    simpa [r] using Filter.Tendsto.const_sub (gradient f (w + s) - gradient f w)
      hgr.tendsto_slope_zero_right
  have hq : Filter.Tendsto q (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f (w + s) - f w - ⟪gradient f w, s⟫)) := by
    simpa [q, smul_eq_mul] using Filter.Tendsto.const_sub (f (w + s) - f w)
      hfr.tendsto_slope_zero_right
  have hcoef : Filter.Tendsto (fun t : ℝ => 2 * L * (1 - t) * ‖s‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * L * ‖s‖ ^ 2)) := by
    have hi : Filter.Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    convert ((hi.const_sub 1).const_mul (2 * L)).mul_const (‖s‖ ^ 2) using 1
    simp
  apply le_of_tendsto_of_tendsto (hr.norm.pow 2) (hcoef.mul hq)
  have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hevent] with t ht ht'
  have hpos : 0 < t := ht
  have hlt : t < 1 := ht'
  have hh := jensen_gradient_bound hf hc hL hT w s hs hpos hlt
  have he : t • gradient f (w + s) + (1 - t) • gradient f w - gradient f (w + t • s) =
      t • r t := by
    dsimp [r]
    rw [smul_sub, smul_sub, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    module
  have hval : t * f (w + s) + (1 - t) * f w - f (w + t • s) = t * q t := by
    dsimp [q]
    field_simp
    ring
  rw [he, hval, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, mul_pow] at hh
  have heq : 2 * (L * t * (1 - t) * ‖s‖ ^ 2) * (t * q t) =
      t ^ 2 * ((2 * L * (1 - t) * ‖s‖ ^ 2) * q t) := by ring
  rw [heq] at hh
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hpos)).mp hh

lemma finite_sum_remainder_bound {n : ℕ} (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L : ℝ} (hL : 0 < L)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (w v : E) :
    (n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) v - gradient (f i) w -
      fderiv ℝ (gradient (f i)) w (v - w)‖ ^ 2 ≤
      2 * L * ‖v - w‖ ^ 2 * ((n : ℝ)⁻¹ * ∑ i,
        (f i v - f i w - ⟪gradient (f i) w, v - w⟫)) := by
  have hi (i : Fin n) := quadratic_remainder_self_bound (hf i) (hc i) hL (hT i) w (v - w)
  simp only [add_sub_cancel] at hi
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i))
    (by positivity : 0 ≤ (n : ℝ)⁻¹)
  simpa only [← Finset.mul_sum, mul_left_comm] using hh

lemma gradient_quadratic_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    ‖gradient f (w + s) - gradient f w - fderiv ℝ (gradient f) w s -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) w s s‖ ≤ L * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let r := fun t : ℝ => gradient f (w + t • s) - gradient f w -
    t • H w s - (t ^ 2 / 2) • T w s s
  let d := fun t : ℝ => H (w + t • s) s - H w s - t • T w s s
  have hd (t : ℝ) : HasDerivAt r (d t) t := by
    have hp : HasDerivAt (fun t : ℝ => w + t • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add w
    have hg := ((GradientDependentLocal.derivative_chain hf).2.1 (w + t • s)).comp_hasDerivAt t hp
    convert ((hg.sub_const (gradient f w)).sub ((hasDerivAt_id t).smul_const (H w s))).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).smul_const (T w s s)) using 1
    · rfl
    · dsimp [d, H]
      module
  have hb (t : ℝ) : ‖d t‖ ≤ (L * ‖s‖ ^ 3) * |t| ^ 2 := by
    have h := ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT w (w + t • s)
    have he : d t = (H (w + t • s) - H w - T w (t • s)) s := by
      simp [d, map_smul]
    rw [he]
    have h' : ‖H (w + t • s) - H w - T w (t • s)‖ ≤ L * ‖t • s‖ ^ 2 := by
      simpa [H, T] using h
    calc
      _ ≤ ‖H (w + t • s) - H w - T w (t • s)‖ * ‖s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖t • s‖ ^ 2) * ‖s‖ := mul_le_mul_of_nonneg_right h' (norm_nonneg s)
      _ = _ := by rw [norm_smul, Real.norm_eq_abs]; ring
  have hh := ThirdOrderTaylorBounds.power_derivative_bound
    (show 0 ≤ L * ‖s‖ ^ 3 by positivity) 2 hd hb 1
  simpa [r, H, T] using hh

lemma reverse_bregman_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    f w - f (w + s) - ⟪gradient f (w + s), w - (w + s)⟫ ≤
      2 * (f (w + s) - f w - ⟪gradient f w, s⟫) + 4 * L * ‖s‖ ^ 4 := by
  have hg := (GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)
  have hsupp (a b : E) : f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) a b
    linarith
  have hH := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound hg hsupp w s
  have hH' : 0 ≤ ⟪fderiv ℝ (gradient f) w s, s⟫ := by
    simpa [real_inner_comm] using hH
  have hF := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT w s 1
  simp only [one_smul, mul_one, one_pow, abs_one] at hF
  have hG := gradient_quadratic_remainder hf hL hT w s
  have hi := (abs_real_inner_le_norm
    (gradient f (w + s) - gradient f w - fderiv ℝ (gradient f) w s -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) w s s) s).trans
    (mul_le_mul_of_nonneg_right hG (norm_nonneg s))
  simp only [inner_sub_left, real_inner_smul_left] at hi
  have hpow : (L * ‖s‖ ^ 3) * ‖s‖ = L * ‖s‖ ^ 4 := by ring
  rw [hpow] at hi
  have hflo := (abs_le.mp hF).1
  have hghi := (abs_le.mp hi).2
  have he : w - (w + s) = -s := by abel
  rw [he, inner_neg_right]
  nlinarith

end LongTails.Proofs.ThirdSmoothJensen
