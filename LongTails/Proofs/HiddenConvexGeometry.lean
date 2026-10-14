import LongTails.Algorithms.SafeguardedSimilarTriangles
import LongTails.Proofs.FrankWolfeDescent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.LocalHiddenConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ballProj_mem (x0 w : E) {r : ℝ} (hr : 0 ≤ r) : ballProj x0 r w ∈ closedBall x0 r := by
  rw [mem_closedBall, dist_eq_norm]
  unfold ballProj
  split_ifs with h
  · exact h
  · rw [not_le] at h
    have hpos : 0 < ‖w - x0‖ := hr.trans_lt h
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hr,
      abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']

lemma ballProj_margin (x0 w u : E) {r : ℝ} (hr : 0 ≤ r) (hu : ‖u - x0‖ ≤ r / 2) :
    r / 2 * ‖w - ballProj x0 r w‖ ≤ ⟪w - ballProj x0 r w, ballProj x0 r w - u⟫ := by
  unfold ballProj
  split_ifs with h
  · simp
  · rw [not_le] at h
    set s := ‖w - x0‖ with hs
    have hpos : 0 < s := hr.trans_lt h
    have hn : w - (x0 + (r / s) • (w - x0)) = ((s - r) / s) • (w - x0) := by
      rw [sub_div, div_self hpos.ne', sub_smul, one_smul]
      abel
    have hp : x0 + (r / s) • (w - x0) - u = (r / s) • (w - x0) - (u - x0) := by abel
    rw [hn, hp, inner_sub_right, inner_smul_left, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (sub_nonneg.mpr h.le) hpos.le)]
    simp only [RCLike.conj_to_real]
    have hcs : ⟪w - x0, u - x0⟫ ≤ s * (r / 2) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hu hpos.le)
    have hsr : 0 ≤ (s - r) / s := div_nonneg (sub_nonneg.mpr h.le) hpos.le
    have key : (s - r) / s * (r / s * s ^ 2) = (s - r) * r := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hcs hsr
    have h3 : (s - r) / s * (s * (r / 2)) = (s - r) * (r / 2) := by field_simp
    rw [← hs]
    nlinarith [key, h2, h3, mul_nonneg (sub_nonneg.mpr h.le) hr]

lemma norm_sub_le_of_mem_segment' {x y t : E} (ht : t ∈ segment ℝ x y) :
    ‖t - x‖ ≤ ‖y - x‖ := by
  rw [segment_eq_image_lineMap] at ht
  obtain ⟨θ, hθ, rfl⟩ := ht
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hθ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hθ.2

lemma taylor_bound {c : E → E} {J : E → E →L[ℝ] E} {S : Set E} {LJ : ℝ} (hLJ : 0 ≤ LJ)
    (hS : Convex ℝ S) (hd : ∀ x ∈ S, HasFDerivAt c (J x) x)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ‖J x - J y‖ ≤ LJ * ‖x - y‖) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2 := by
  let h : E → E := fun t => c t - J x t
  have hsub : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hder : ∀ t ∈ segment ℝ x y, HasFDerivWithinAt h (J t - J x) (segment ℝ x y) t :=
    fun t ht => ((hd t (hsub ht)).sub (J x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ t ∈ segment ℝ x y, ‖J t - J x‖ ≤ LJ * ‖y - x‖ := fun t ht =>
    (hl t (hsub ht) x hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment' ht) hLJ)
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : h y - h x = c y - c x - J x (y - x) := by
    simp only [h, map_sub]
    abel
  rw [he] at hmv
  calc _ ≤ LJ * ‖y - x‖ * ‖y - x‖ := hmv
    _ = LJ * ‖y - x‖ ^ 2 := by ring

open Classical in
noncomputable def corr (c : E → E) (J : E → E →L[ℝ] E) (y w : E) : E :=
  if h : ∃ v, J y v = c w - c y then Classical.choose h - (w - y) else 0

lemma corr_spec {c : E → E} {J : E → E →L[ℝ] E} {y w : E} (h : ∃ v, J y v = c w - c y) :
    J y (corr c J y w + (w - y)) = c w - c y := by
  unfold corr
  split
  · next h0 =>
    rw [sub_add_cancel]
    exact Classical.choose_spec h0
  · contradiction

lemma corr_apply {c : E → E} {J : E → E →L[ℝ] E} {y w : E} (h : ∃ v, J y v = c w - c y) :
    J y (corr c J y w) = c w - c y - J y (w - y) := by
  have hs := corr_spec h
  rw [map_add] at hs
  rw [← hs]
  abel

lemma exists_preimage [FiniteDimensional ℝ E] {T : E →L[ℝ] E} {μ : ℝ} (hμ : 0 < μ)
    (hT : ∀ v, μ * ‖v‖ ≤ ‖T v‖) (b : E) : ∃ v, T v = b := by
  have hinj : Function.Injective (T : E →ₗ[ℝ] E) := by
    intro v w hvw
    have h := hT (v - w)
    rw [map_sub] at h
    change T v = T w at hvw
    rw [hvw, sub_self, norm_zero] at h
    have : ‖v - w‖ = 0 := le_antisymm
      (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  exact LinearMap.surjective_of_injective hinj b

lemma corr_norm {c : E → E} {J : E → E →L[ℝ] E} {μ LJ : ℝ} {y w : E}
    (h : ∃ v, J y v = c w - c y) (hT : ∀ v, μ * ‖v‖ ≤ ‖J y v‖)
    (hb : ‖c w - c y - J y (w - y)‖ ≤ LJ * ‖w - y‖ ^ 2) :
    μ * ‖corr c J y w‖ ≤ LJ * ‖w - y‖ ^ 2 := by
  have := hT (corr c J y w)
  rw [corr_apply h] at this
  linarith

lemma corr_sub {c : E → E} {J : E → E →L[ℝ] E} {y y' w : E}
    (h : ∃ v, J y v = c w - c y) (h' : ∃ v, J y' v = c w - c y') :
    J y (corr c J y w - corr c J y' w) =
      -(c y - c y' - J y' (y - y')) - (J y - J y') (w - y) - (J y - J y') (corr c J y' w) := by
  have h1 := corr_apply h
  have h2 := corr_apply h'
  have h3 : J y (corr c J y' w) = J y' (corr c J y' w) + (J y - J y') (corr c J y' w) := by
    rw [sub_apply]
    abel
  rw [map_sub, h1, h3, h2]
  simp only [map_sub, sub_apply]
  abel

lemma corr_lipschitz {c : E → E} {J : E → E →L[ℝ] E} {μ LJ : ℝ} {y y' w : E}
    (h : ∃ v, J y v = c w - c y) (h' : ∃ v, J y' v = c w - c y')
    (hT : ∀ v, μ * ‖v‖ ≤ ‖J y v‖)
    (hb : ‖c y - c y' - J y' (y - y')‖ ≤ LJ * ‖y - y'‖ ^ 2)
    (hl : ‖J y - J y'‖ ≤ LJ * ‖y - y'‖) :
    μ * ‖corr c J y w - corr c J y' w‖ ≤
      LJ * ‖y - y'‖ * (‖y - y'‖ + ‖w - y‖ + ‖corr c J y' w‖) := by
  have hm := hT (corr c J y w - corr c J y' w)
  rw [corr_sub h h'] at hm
  have e1 := ContinuousLinearMap.le_opNorm (J y - J y') (w - y)
  have e2 := ContinuousLinearMap.le_opNorm (J y - J y') (corr c J y' w)
  have t := norm_sub_le (-(c y - c y' - J y' (y - y')) - (J y - J y') (w - y))
    ((J y - J y') (corr c J y' w))
  have t2 := norm_sub_le (-(c y - c y' - J y' (y - y'))) ((J y - J y') (w - y))
  rw [norm_neg] at t2
  have f1 := mul_le_mul_of_nonneg_right hl (norm_nonneg (w - y))
  have f2 := mul_le_mul_of_nonneg_right hl (norm_nonneg (corr c J y' w))
  nlinarith

variable [CompleteSpace E]

lemma gradient_pairing {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {S : Set E} {x : E}
    (hS : IsOpen S) (hxS : x ∈ S) (heq : ∀ z ∈ S, F z = H (c z))
    (hc : HasFDerivAt c (J x) x) (hH : DifferentiableAt ℝ H (c x))
    (hF : HasGradientAt F (gradient F x) x) (v : E) :
    ⟪gradient F x, v⟫ = ⟪gradient H (c x), J x v⟫ := by
  have hcomp : HasFDerivAt (H ∘ c) ((fderiv ℝ H (c x)).comp (J x)) x :=
    hH.hasFDerivAt.comp x hc
  have hev : (H ∘ c) =ᶠ[nhds x] F :=
    Filter.eventually_of_mem (hS.mem_nhds hxS) (fun z hz => (heq z hz).symm)
  have hF' : HasFDerivAt F ((fderiv ℝ H (c x)).comp (J x)) x := hcomp.congr_of_eventuallyEq hev.symm
  have huniq := hF.hasFDerivAt.unique hF'
  have := congrArg (fun T : E →L[ℝ] ℝ => T v) huniq
  simp only [toDual_apply_apply, ContinuousLinearMap.comp_apply] at this
  rw [this, hH.hasGradientAt.hasFDerivAt.fderiv]
  simp

lemma hidden_support {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E} {S U : Set E} {y w : E}
    (hS : IsOpen S) (hyS : y ∈ S) (hwS : w ∈ S) (heq : ∀ z ∈ S, F z = H (c z))
    (hHc : ConvexOn ℝ U H) (hyU : c y ∈ U) (hwU : c w ∈ U)
    (hc : HasFDerivAt c (J y) y) (hH : DifferentiableAt ℝ H (c y))
    (hF : HasGradientAt F (gradient F y) y) (hpre : ∃ v, J y v = c w - c y) :
    F y + ⟪gradient F y, w - y⟫ + ⟪gradient F y, corr c J y w⟫ ≤ F w := by
  have hsup := FrankWolfe.convex_support_on hHc hyU hwU hH.hasGradientAt
  rw [← corr_spec hpre, ← gradient_pairing hS hyS heq hc hH hF, inner_add_right] at hsup
  rw [heq y hyS, heq w hwS]
  linarith

end OracleTemplate.LocalHiddenConvex
