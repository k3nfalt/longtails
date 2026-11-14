import LongTails.Proofs.PointwiseHessianTuning
import LongTails.Proofs.PointwiseHessianProx

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianTrial

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianNewton
open LongTails.Proofs.PointwiseHessianTuning

lemma newton_contract (p : Public) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    {τ r b : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hb : 0 < b) (hbt : b ≤ 1 / τ)
    (c x : p.E) (hx : ‖x - c‖ ≤ 2 * r)
    (he : ‖b • gradient f x + x - c‖ ≤ 2 * continuationRatio p τ r * r) :
    let y := newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x)
    ‖y - x‖ ≤ ‖b • gradient f x + x - c‖ ∧
      ‖b • gradient f y + y - c‖ ≤ ‖b • gradient f x + x - c‖ / 4 := by
  let H := fderiv ℝ (gradient f) x
  let e := b • gradient f x + x - c
  let u := Function.invFun (ContinuousLinearMap.id ℝ p.E + b • H) e
  let d := -u
  let a := continuationRatio p τ r
  obtain ⟨hu, hun, hHun⟩ := linear_inverse_bounds H
    (LongTails.Proofs.PointwiseHessianGeometry.hessian_psd hf hc x) hb.le e
  change u + b • H u = e at hu
  change ‖u‖ ≤ ‖e‖ at hun
  change ‖b • H u‖ ≤ ‖e‖ at hHun
  have hd : ‖d‖ ≤ ‖e‖ := by simpa [d] using hun
  have hHd : ‖b • H d‖ ≤ ‖e‖ := by simpa [d] using hHun
  have hstep : d + b • H d = -e := by
    dsimp only [d]
    rw [map_neg, smul_neg, ← neg_add, hu]
  have ha : 0 ≤ a := (continuationRatio_pos p hM₀ hM₁ hτ hr.le).le
  have htune : a * (1 + p.M₁ * r ^ 2 + (1 / τ) * p.M₀ * r) ≤ 1 / 64 :=
    (continuationRatio_identity p hM₀ hM₁ hτ hr.le).le
  have hsmall := continuation_smallness ha hr.le (norm_nonneg d) hb.le hbt hM₀ hM₁
    htune (hd.trans he)
  have hq := continuation_smallness ha hr.le (norm_nonneg e) hb.le hbt hM₀ hM₁ htune he
  have hgnorm : ‖b • gradient f x‖ ≤ 3 * r := by
    have hh := norm_sub_le e (x - c)
    have hid : e - (x - c) = b • gradient f x := by dsimp [e]; abel
    rw [hid] at hh
    linarith [hq.1]
  obtain ⟨_, hg, hH⟩ := LongTails.Proofs.GradientDependentLocal.derivative_chain hf
  have hcon := pointwise_newton_contraction hg hH hb.le hr.le hM₀ hM₁ hT c x d
    hgnorm (hHd.trans hq.1) hsmall.2.2.1 hsmall.2.1 hsmall.2.2.2 hstep
  have hy : newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x) = x + d := by
    change x - u = x + (-u)
    exact sub_eq_add_neg x u
  dsimp only
  rw [hy]
  constructor
  · simpa using hd
  · exact hcon.trans (by linarith)

lemma adequate_radius_guard (p : Public) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    {τ r b : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hb : 0 < b) (hbt : b ≤ 1 / τ)
    (c x z : p.E) (hx : ‖x - c‖ ≤ 2 * r)
    (he : ‖b • gradient f x + x - c‖ ≤ 2 * continuationRatio p τ r * r)
    (hz : (1 / τ) • gradient f z + z - c = 0) (hradius : ‖z - c‖ ≤ r / 2) :
    ‖newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x) - c‖ ≤ 2 * r := by
  let y := newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x)
  have hm := LongTails.Proofs.PointwiseHessianGeometry.gradient_monotone hf hc
  obtain ⟨zb, hzb⟩ := LongTails.Proofs.PointwiseHessianProx.proximal_exists hf hc hb c
  have hrb := (LongTails.Proofs.PointwiseHessianProx.radius_mono hm hb hbt c zb z hzb hz).trans hradius
  have hdist := LongTails.Proofs.PointwiseHessianProx.residual_distance hm hb.le c x zb hzb
  have hstep := (newton_contract p hf hc hM₀ hM₁ hT hτ hr hb hbt c x hx he).1
  have hsmall := continuation_smallness
    (continuationRatio_pos p hM₀ hM₁ hτ hr.le).le hr.le
    (norm_nonneg (b • gradient f x + x - c)) hb.le hbt hM₀ hM₁
    (continuationRatio_identity p hM₀ hM₁ hτ hr.le).le he
  have hh := LongTails.Proofs.PointwiseHessianProx.adequate_guard c x zb (y - x)
    hr.le hdist hrb hstep hsmall.1
  simpa [y] using hh

lemma failed_radius_certificate (p : Public) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    {τ r b : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hb : 0 < b) (hbt : b ≤ 1 / τ)
    (c x z : p.E) (hx : ‖x - c‖ ≤ 2 * r)
    (he : ‖b • gradient f x + x - c‖ ≤ 2 * continuationRatio p τ r * r)
    (hz : (1 / τ) • gradient f z + z - c = 0)
    (hfail : 2 * r < ‖newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x) - c‖) :
    r / 2 < ‖z - c‖ := by
  by_contra h
  have hh := adequate_radius_guard p hf hc hM₀ hM₁ hT hτ hr hb hbt c x z hx he hz
    (le_of_not_gt h)
  linarith

lemma continuation_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c x g : E) {a r b bnew : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r)
    (hb : 0 < b) (hlo : b ≤ bnew) (hhi : bnew ≤ b * (1 + a / 8))
    (hx : ‖x - c‖ ≤ 2 * r) (he : ‖b • g + x - c‖ ≤ a * r) :
    ‖bnew • g + x - c‖ ≤ 2 * a * r := by
  have hbg : b * ‖g‖ ≤ 3 * r := by
    have hh := norm_sub_le (b • g + x - c) (x - c)
    have hid : (b • g + x - c) - (x - c) = b • g := by abel
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at hh
    have har := mul_le_mul_of_nonneg_right ha1 hr
    linarith
  have hdelta : bnew - b ≤ a * b / 8 := by nlinarith
  have hdelta0 : 0 ≤ bnew - b := sub_nonneg.mpr hlo
  have hnorm : ‖(bnew - b) • g‖ ≤ 3 * a * r / 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdelta0]
    have h1 := mul_le_mul_of_nonneg_right hdelta (norm_nonneg g)
    have h2 := mul_le_mul_of_nonneg_left hbg ha
    nlinarith
  have hh := norm_add_le (b • g + x - c) ((bnew - b) • g)
  have hid : (b • g + x - c) + (bnew - b) • g = bnew • g + x - c := by module
  rw [hid] at hh
  have har : 0 ≤ a * r := mul_nonneg ha hr
  linarith

lemma continued_residual (p : Public) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁)
    {τ r b : ℝ} (hτ : 0 < τ) (hr : 0 ≤ r) (hb : 0 < b) (hbt : b ≤ 1 / τ)
    (c x g : p.E) (hx : ‖x - c‖ ≤ 2 * r)
    (he : ‖b • g + x - c‖ ≤ continuationRatio p τ r * r) :
    ‖min (1 / τ) (b * (1 + continuationRatio p τ r / 8)) • g + x - c‖ ≤
      2 * continuationRatio p τ r * r := by
  have ha := (continuationRatio_pos p hM₀ hM₁ hτ hr).le
  have ha1 : continuationRatio p τ r ≤ 1 :=
    (continuationRatio_le p hM₀ hM₁ hτ hr).trans (by norm_num)
  apply continuation_residual c x g ha ha1 hr hb ?_ (min_le_right _ _) hx he
  exact le_min hbt (by nlinarith)

lemma residual_stop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c x g : E) {b t : ℝ} (hb : 0 < b)
    (he : ‖b • g + x - c‖ ≤ b * t / 3)
    (hms : ¬ ‖b • g + x - c‖ ≤ ‖x - c‖ / 2) : ‖g‖ ≤ t := by
  have hh := norm_sub_le (b • g + x - c) (x - c)
  have hid : (b • g + x - c) - (x - c) = b • g := by abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at hh
  have hn : ‖x - c‖ < 2 * ‖b • g + x - c‖ := by
    have ht := lt_of_not_ge hms
    linarith
  have hg : b * ‖g‖ ≤ b * t := by linarith
  exact (mul_le_mul_iff_right₀ hb).mp hg

lemma failed_cap_bound (p : Public) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hM₁ : 0 ≤ p.M₁) (hR : 0 < p.R)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) (hbt : b ≤ 1 / τ)
    (c x xs : p.E) (hmin : IsMinOn f Set.univ xs) (hcR : ‖c - xs‖ ≤ 4 * p.R)
    (hx : ‖x - c‖ ≤ 2 * radiusCap p τ)
    (he : ‖b • gradient f x + x - c‖ ≤ 2 * continuationRatio p τ (radiusCap p τ) * radiusCap p τ)
    (hfail : 2 * radiusCap p τ < ‖newtonPoint p b c x (gradient f x) (fderiv ℝ (gradient f) x) - c‖) :
    τ < 512 * p.M₀ * p.R := by
  have hr := radiusCap_pos p hM₀ hR hτ
  obtain ⟨z, hz⟩ := PointwiseHessianProx.proximal_exists hf hc (one_div_pos.mpr hτ) c
  have hcert := failed_radius_certificate p hf hc hM₀ hM₁ hT hτ hr hb hbt c x z hx he hz hfail
  have hroot := PointwiseHessianProx.root_radius
    (PointwiseHessianGeometry.gradient_monotone hf hc) (one_div_pos.mpr hτ).le
    c z xs (PointwiseHessianGeometry.minimizer_gradient hmin) hz
  have hcsq := pow_le_pow_left₀ (norm_nonneg _) hcR 2
  have hdist : ‖z - c‖ ≤ 4 * p.R := by
    nlinarith [sq_nonneg ‖z - xs‖, norm_nonneg (z - c)]
  have hcap : radiusCap p τ < 8 * p.R := by linarith
  by_cases hzero : p.M₀ = 0
  · simp only [radiusCap, hzero, ite_true] at hcap
    linarith
  · have hp : 0 < p.M₀ := lt_of_le_of_ne hM₀ (Ne.symm hzero)
    have hh : τ / (64 * p.M₀) < 8 * p.R := by
      simp only [radiusCap, hzero, ite_false] at hcap
      exact (min_lt_iff.mp hcap).resolve_left (by linarith)
    have ht := (div_lt_iff₀ (show 0 < 64 * p.M₀ by positivity)).mp hh
    nlinarith

lemma previous_cap_accept_bound (p : Public) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) (hM₀ : 0 ≤ p.M₀) (hR : 0 < p.R)
    {τ : ℝ} (hτ : 0 < τ) (c x z xs : p.E) (hmin : IsMinOn f Set.univ xs)
    (hcR : ‖c - xs‖ ≤ 4 * p.R) (hz : (2 / τ) • gradient f z + z - c = 0)
    (hcert : radiusCap p (τ / 2) / 2 < ‖z - c‖)
    (hres : ‖(1 / τ) • gradient f x + x - c‖ ≤ ‖x - c‖ / 2) :
    τ ≤ 1024 * p.M₀ * ‖x - c‖ := by
  have hm := PointwiseHessianGeometry.gradient_monotone hf hc
  have hroot := PointwiseHessianProx.root_radius hm (show 0 ≤ 2 / τ by positivity)
    c z xs (PointwiseHessianGeometry.minimizer_gradient hmin) hz
  have hcsq := pow_le_pow_left₀ (norm_nonneg _) hcR 2
  have hdist : ‖z - c‖ ≤ 4 * p.R := by
    nlinarith [sq_nonneg ‖z - xs‖, norm_nonneg (z - c)]
  have hcap : radiusCap p (τ / 2) < 8 * p.R := by linarith
  by_cases hzero : p.M₀ = 0
  · simp only [radiusCap, hzero, ite_true] at hcap
    linarith
  · have hMp : 0 < p.M₀ := lt_of_le_of_ne hM₀ (Ne.symm hzero)
    have hsmall : (τ / 2) / (64 * p.M₀) < 8 * p.R := by
      simp only [radiusCap, hzero, ite_false] at hcap
      exact (min_lt_iff.mp hcap).resolve_left (by linarith)
    have he : radiusCap p (τ / 2) / 2 = τ / (256 * p.M₀) := by
      simp only [radiusCap, hzero, ite_false, min_eq_right (show (τ / 2) / (64 * p.M₀) ≤ 16 * p.R by linarith)]
      ring
    rw [he] at hcert
    have hτr := (div_lt_iff₀ (show 0 < 256 * p.M₀ by positivity)).mp hcert
    obtain ⟨zn, hzn⟩ := PointwiseHessianProx.proximal_exists hf hc (one_div_pos.mpr hτ) c
    have hhalf := PointwiseHessianProx.radius_half hm (one_div_pos.mpr hτ) c zn z hzn
      (by simpa [div_eq_mul_inv] using hz)
    have hrel := PointwiseHessianProx.relative_radius hm (one_div_pos.mpr hτ).le c x zn hzn hres
    have hh : ‖z - c‖ ≤ 3 * ‖x - c‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hh hM₀
    nlinarith [mul_nonneg hM₀ (norm_nonneg (x - c))]

end LongTails.Proofs.PointwiseHessianTrial
