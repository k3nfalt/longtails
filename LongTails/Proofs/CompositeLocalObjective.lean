import LongTails.Proofs.CompositeCubicBridge
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.GdConvex
import LongTails.Proofs.CompositeCurvatureParameters

namespace LongTails.Proofs.CompositeLocalObjective

open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic
open LongTails.Proofs.CubicRegularization
open scoped RealInnerProductSpace

noncomputable def smooth {p : Params} (F : Problem p) (center x : p.E) : ℝ :=
  F.f x + cubicCoefficient p * cubic (x - center)

lemma smooth_contDiff {p : Params} (F : Problem p) (center : p.E) (hf : ContDiff ℝ 2 F.f) :
    ContDiff ℝ 2 (smooth F center) := by
  have hc : ContDiff ℝ 2 (fun x : p.E => x - center) := contDiff_id.sub contDiff_const
  exact hf.add (contDiff_const.mul (cubic_contDiff.comp hc))

lemma smooth_hasGradient {p : Params} (F : Problem p) (center x : p.E)
    (hf : Differentiable ℝ F.f) :
    HasGradientAt (smooth F center) (localGradient p center x (gradient F.f x)) x := by
  have hc := ((cubic_hasFDerivAt (x - center)).comp x
    ((hasFDerivAt_id x).sub_const center)).const_mul (cubicCoefficient p)
  have hg := (hf x).hasGradientAt.hasFDerivAt.add hc
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hg using 1
  · ext u; rfl
  · ext u
    simp [localGradient, cubicGradient, InnerProductSpace.toDual_apply_apply]
    ring

lemma localGradient_hasFDerivAt {p : Params} (F : Problem p) (center x : p.E)
    (hf : ContDiff ℝ 2 F.f) :
    HasFDerivAt (fun y => localGradient p center y (gradient F.f y))
      (localHessian p center x (fderiv ℝ (gradient F.f) x)) x := by
  have hg := ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
    (by norm_num) x).hasFDerivAt
  have hc := ((cubicGradient_hasFDerivAt (x - center)).comp x
    ((hasFDerivAt_id x).sub_const center)).const_smul (cubicCoefficient p)
  convert hg.add hc using 1
  · ext y
    simp [localGradient, cubicGradient, smul_smul, Function.comp_def]
  · ext v
    simp [localHessian, cubicHessian]

lemma smooth_convex {p : Params} (F : Problem p) (center : p.E)
    (hf : ConvexOn ℝ Set.univ F.f) (hγ : 0 ≤ cubicCoefficient p) :
    ConvexOn ℝ Set.univ (smooth F center) := by
  have hc : ConvexOn ℝ Set.univ (fun x : p.E => cubic (x - center)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := cubic_convex.2 (Set.mem_univ (x - center)) (Set.mem_univ (y - center)) ha hb hab
    have he : a • (x - center) + b • (y - center) = (a • x + b • y) - center := by
      calc
        _ = (a • x + b • y) - (a + b) • center := by module
        _ = _ := by rw [hab, one_smul]
    rw [he] at hh
    exact hh
  exact hf.add (hc.smul hγ)

lemma localHessian_lipschitz {p : Params} (F : Problem p) (center : p.E)
    (hγ : 0 ≤ cubicCoefficient p)
    (hH : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (x y : p.E) :
    ‖localHessian p center x (fderiv ℝ (gradient F.f) x) -
      localHessian p center y (fderiv ℝ (gradient F.f) y)‖ ≤ localHessianLip p * ‖x - y‖ := by
  have he : localHessian p center x (fderiv ℝ (gradient F.f) x) -
      localHessian p center y (fderiv ℝ (gradient F.f) y) =
      (fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y) +
        cubicCoefficient p • (cubicHessian (x - center) - cubicHessian (y - center)) := by
    simp only [localHessian, cubicHessian, smul_sub]
    abel
  rw [he]
  have hc := cubicHessian_lipschitz (x - center) (y - center)
  have hd : x - center - (y - center) = x - y := by abel
  rw [hd] at hc
  have hm := mul_le_mul_of_nonneg_left hc hγ
  have hn := norm_add_le (fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y)
    (cubicCoefficient p • (cubicHessian (x - center) - cubicHessian (y - center)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ] at hn
  have hf := hH x y
  dsimp [localHessianLip]
  nlinarith only [hm, hn, hf]

lemma smooth_gradient {p : Params} (F : Problem p) (center x : p.E)
    (hf : Differentiable ℝ F.f) :
    gradient (smooth F center) x = localGradient p center x (gradient F.f x) :=
  (smooth_hasGradient F center x hf).gradient

lemma smooth_hessian {p : Params} (F : Problem p) (center x : p.E)
    (hf : ContDiff ℝ 2 F.f) :
    fderiv ℝ (gradient (smooth F center)) x = localHessian p center x (fderiv ℝ (gradient F.f) x) := by
  have he : gradient (smooth F center) = fun y => localGradient p center y (gradient F.f y) :=
    funext (fun y => smooth_gradient F center y (hf.differentiable (by norm_num)))
  rw [he]
  exact (localGradient_hasFDerivAt F center x hf).fderiv

lemma localHessian_symmetric {p : Params} (F : Problem p) (center x : p.E)
    (hf : ContDiff ℝ 2 F.f) (u v : p.E) :
    ⟪u, localHessian p center x (fderiv ℝ (gradient F.f) x) v⟫ =
      ⟪localHessian p center x (fderiv ℝ (gradient F.f) x) u, v⟫ := by
  rw [← smooth_hessian F center x hf]
  exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
    (smooth_contDiff F center hf) x u v).symm

lemma localHessian_nonneg {p : Params} (F : Problem p) (center x : p.E)
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (u : p.E) :
    0 ≤ ⟪u, localHessian p center x (fderiv ℝ (gradient F.f) x) u⟫ := by
  have hsmooth := smooth_contDiff F center hf
  have hgd := (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hsmooth).differentiable
    (by norm_num)
  have hs : ∀ a b, smooth F center a + ⟪gradient (smooth F center) a, b - a⟫ +
      (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ smooth F center b := by
    intro a b
    have h := OracleTemplate.Gradient.convex_support (smooth_convex F center hconv hγ)
      (fun y => (hsmooth.differentiable (by norm_num) y).hasGradientAt) a b
    linarith
  have h := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound hgd hs x u
  rw [smooth_hessian F center x hf] at h
  simpa [real_inner_comm] using h

lemma smooth_bregman_lower {p : Params} (F : Problem p) (center x y : p.E)
    (hf : Differentiable ℝ F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) :
    smooth F center x + ⟪localGradient p center x (gradient F.f x), y - x⟫ +
      cubicCoefficient p * ‖y - x‖ ^ 3 / 6 ≤ smooth F center y := by
  have h := OracleTemplate.Gradient.convex_support hconv (fun z => (hf z).hasGradientAt) x y
  have hb := cubic_bregman_lower (y - center) (x - center)
  have hd : y - center - (x - center) = y - x := by abel
  rw [hd] at hb
  have hm := mul_le_mul_of_nonneg_left hb hγ
  simp only [smooth, localGradient, inner_add_left, real_inner_smul_left,
    cubicGradient] at hm ⊢
  nlinarith only [h, hm]

lemma composite_growth_at_minimizer {p : Params} (F : Problem p) (center : p.E)
    (hf : Differentiable ℝ F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (hψ : ConvexOn ℝ F.domain F.ψ)
    {x y : p.E} (hx : x ∈ F.domain) (hy : y ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, smooth F center x + F.ψ x ≤ smooth F center u + F.ψ u) :
    cubicCoefficient p * ‖y - x‖ ^ 3 / 6 ≤
      smooth F center y + F.ψ y - (smooth F center x + F.ψ x) := by
  have hb := smooth_bregman_lower F center x y hf hconv hγ
  have ho := CompositeExtrapolation.composite_optimality hψ hx
    (smooth_hasGradient F center x hf) hmin hy
  linarith

lemma snapshotMetric_lower {p : Params} (F : Problem p) (center snapshot : p.E) {Δ : ℝ}
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (d : p.E) :
    4096 * ((depth p : ℝ) + 1) ^ 2 * localHessianLip p *
      (Δ / localHessianLip p) ^ (1 / 3 : ℝ) * ‖d‖ ^ 2 ≤
      ⟪d, snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot) d⟫ := by
  have hn := localHessian_nonneg F center snapshot hf hconv hγ d
  have hm := mul_nonneg (by positivity : 0 ≤ 32 * ((depth p : ℝ) + 1)) hn
  simp only [snapshotMetric, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  linarith

lemma snapshotMetric_symmetric {p : Params} (F : Problem p) (center snapshot : p.E) (Δ : ℝ)
    (hf : ContDiff ℝ 2 F.f) (u v : p.E) :
    ⟪u, snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot) v⟫ =
      ⟪snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot) u, v⟫ := by
  simp only [snapshotMetric, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_add_left, inner_smul_right,
    real_inner_smul_left, localHessian_symmetric F center snapshot hf]

lemma snapshot_model_valid {p : Params} (F : Problem p) (center snapshot y gy : p.E) {Δ : ℝ}
    (hf : ContDiff ℝ 2 F.f) (hconv : ConvexOn ℝ Set.univ F.f)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hΔ : 0 < Δ) :
    (⟨y, gy, snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot),
      0, regularizerScale p⟩ : Model p).valid := by
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  let μ := 4096 * ((depth p : ℝ) + 1) ^ 2 * localHessianLip p *
    (Δ / localHessianLip p) ^ (1 / 3 : ℝ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hl := snapshotMetric_lower F center snapshot (Δ := Δ) hf hconv hγ.le
  refine ⟨lt_of_lt_of_le zero_lt_one (CompositeCurvatureParameters.scale_bounds p).1,
    le_rfl, snapshotMetric_symmetric F center snapshot Δ hf, ?_, Or.inr ⟨μ, hμ, hl⟩⟩
  intro d
  exact (mul_nonneg hμ.le (sq_nonneg ‖d‖)).trans (hl d)

lemma original_subgradient {p : Params} (F : Problem p) (center z r : p.E)
    (hf : Differentiable ℝ F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hψ : ConvexOn ℝ F.domain F.ψ) (hz : z ∈ F.domain)
    (hs : ∀ u ∈ F.domain, smooth F center z + F.ψ z + ⟪r, u - z⟫ ≤
      smooth F center u + F.ψ u) :
    ∀ u ∈ F.domain, F.f z + F.ψ z +
      ⟪r - (cubicCoefficient p * ‖z - center‖) • (z - center), u - z⟫ ≤ F.f u + F.ψ u := by
  let h := fun u => smooth F center u - ⟪r, u⟫
  let g := localGradient p center z (gradient F.f z) - r
  have hg : HasGradientAt h g z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (smooth_hasGradient F center z hf).hasFDerivAt.sub (innerSL ℝ r).hasFDerivAt using 1
    · rfl
    · ext d
      simp [g, InnerProductSpace.toDual_apply_apply]
  have hm : ∀ u ∈ F.domain, h z + F.ψ z ≤ h u + F.ψ u := by
    intro u hu
    have hv := hs u hu
    simp only [inner_sub_right] at hv
    dsimp only [h]
    linarith
  intro u hu
  have hp := CompositeExtrapolation.composite_optimality hψ hz hg hm hu
  have hc' := OracleTemplate.Gradient.convex_support hc (fun x => (hf x).hasGradientAt) z u
  simp only [g, localGradient, inner_sub_left, inner_add_left] at hp ⊢
  linarith

end LongTails.Proofs.CompositeLocalObjective
