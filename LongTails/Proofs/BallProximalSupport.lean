import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.BallProximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma ball_support {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f)
    {x y : E} {t : ℝ} (ht : 0 < t) (hx : x ∈ C) (hy : y ∈ C)
    (hyt : ‖y - x‖ ≤ t)
    (hmin : ∀ z ∈ C, ‖z - x‖ ≤ t → f y ≤ f z) :
    ∃ g : E, (∀ z ∈ C, f y + ⟪g, z - y⟫ ≤ f z) ∧
      ∀ z : E, ‖z - x‖ ≤ t → 0 ≤ ⟪g, z - y⟫ := by
  let S : Set (E × ℝ) := Metric.ball x t ×ˢ Iio (f y)
  let T : Set (E × ℝ) := {p | p.1 ∈ C ∧ f p.1 ≤ p.2}
  have hS : Convex ℝ S := (convex_ball x t).prod (convex_Iio (f y))
  have hSo : IsOpen S := Metric.isOpen_ball.prod isOpen_Iio
  have hT : Convex ℝ T := hf.convex_epigraph
  have hdis : Disjoint S T := by
    rw [Set.disjoint_left]
    intro p hp hq
    have hp' : ‖p.1 - x‖ < t ∧ p.2 < f y := by
      simpa [S, Metric.mem_ball, dist_eq_norm] using hp
    have hm := hmin p.1 hq.1 (le_of_lt hp'.1)
    exact (not_lt_of_ge (hm.trans hq.2)) hp'.2
  obtain ⟨l, v, hlS, hlT⟩ := geometric_hahn_banach_open hS hSo hT hdis
  have hcl : ∀ p ∈ closure S, l p ≤ v := by
    exact closure_minimal (fun p hp => (hlS p hp).le) (isClosed_le l.continuous continuous_const)
  have hclosed : ∀ z : E, ‖z - x‖ ≤ t → (z, f y) ∈ closure S := by
    intro z hz
    simpa [S, closure_prod_eq, closure_ball x (ne_of_gt ht), closure_Iio,
      Metric.mem_closedBall, dist_eq_norm] using hz
  have hval : l (y, f y) = v :=
    le_antisymm (hcl _ (hclosed y hyt)) (hlT _ ⟨hy, le_rfl⟩)
  let b : ℝ := l (0, 1)
  have hexpand (z : E) (a : ℝ) : l (z, a) = l (z, 0) + a * b := by
    have he : (z, a) = (z, 0) + a • (0, (1 : ℝ)) := by simp
    rw [he, map_add, map_smul]
    rfl
  have hb : 0 < b := by
    have hs : (x, f y - 1) ∈ S := by simp [S, ht]
    have hl := lt_of_lt_of_le (hlS _ hs) (hlT (x, f x) ⟨hx, le_rfl⟩)
    rw [hexpand x (f y - 1), hexpand x (f x)] at hl
    have hm := hmin x hx (by simp [le_of_lt ht])
    nlinarith
  let a : StrongDual ℝ E := (-b⁻¹) • (l.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let g : E := (InnerProductSpace.toDual ℝ E).symm a
  have hg (z : E) : ⟪g, z⟫ = -b⁻¹ * l (z, 0) := by
    rw [show g = (InnerProductSpace.toDual ℝ E).symm a from rfl,
      InnerProductSpace.toDual_symm_apply]
    rfl
  have hgz (z : E) : b * ⟪g, z - y⟫ = l (y, 0) - l (z, 0) := by
    rw [hg, show (z - y, (0 : ℝ)) = (z, 0) - (y, 0) by simp, map_sub]
    field_simp
    ring
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    have hl := hlT (z, f z) ⟨hz, le_rfl⟩
    rw [← hval, hexpand y (f y), hexpand z (f z)] at hl
    have hg' := hgz z
    nlinarith
  · intro z hz
    have hl := hcl _ (hclosed z hz)
    rw [← hval, hexpand z (f y), hexpand y (f y)] at hl
    have hg' := hgz z
    nlinarith

omit [CompleteSpace E] in
lemma linear_ball_radial {x y g : E} {t : ℝ} (ht : 0 < t) (hg : g ≠ 0)
    (hyt : ‖y - x‖ ≤ t)
    (hmin : ∀ z : E, ‖z - x‖ ≤ t → 0 ≤ ⟪g, z - y⟫) :
    ‖x - y‖ = t ∧ g = (‖g‖ / t) • (x - y) := by
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hzn : ‖(x - (t / ‖g‖) • g) - x‖ ≤ t := by
    rw [show (x - (t / ‖g‖) • g) - x = -((t / ‖g‖) • g) by module,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ht hgn),
      div_mul_cancel₀ _ (ne_of_gt hgn)]
  have hm := hmin _ hzn
  rw [show x - (t / ‖g‖) • g - y = (x - y) - (t / ‖g‖) • g by module,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hm
  have hdiv : t / ‖g‖ * ‖g‖ ^ 2 = t * ‖g‖ := by field_simp
  rw [hdiv] at hm
  have hi := real_inner_le_norm g (x - y)
  have hyt' : ‖x - y‖ ≤ t := by simpa [norm_sub_rev] using hyt
  have hn : ‖x - y‖ = t := by nlinarith
  have hin : ⟪g, x - y⟫ = ‖g‖ * t := by rw [hn] at hi; nlinarith
  refine ⟨hn, ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have he : ‖g - (‖g‖ / t) • (x - y)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hin, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hgn ht), hn]
    field_simp
    ring
  nlinarith [norm_nonneg (g - (‖g‖ / t) • (x - y))]

lemma positive_radial_support {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f)
    {x y z : E} {t : ℝ} (ht : 0 < t) (hx : x ∈ C) (hy : y ∈ C)
    (hz : z ∈ C) (hgap : f z < f y) (hyt : ‖y - x‖ ≤ t)
    (hmin : ∀ w ∈ C, ‖w - x‖ ≤ t → f y ≤ f w) :
    ∃ c : ℝ, 0 < c ∧ ‖x - y‖ = t ∧
      ∀ w ∈ C, f y + ⟪c • (x - y), w - y⟫ ≤ f w := by
  obtain ⟨g, hsupport, hball⟩ := ball_support hf ht hx hy hyt hmin
  have hg : g ≠ 0 := by
    intro he
    have hs := hsupport z hz
    rw [he, inner_zero_left, add_zero] at hs
    exact (not_lt_of_ge hs) hgap
  obtain ⟨hn, he⟩ := linear_ball_radial ht hg hyt hball
  refine ⟨‖g‖ / t, div_pos (norm_pos_iff.mpr hg) ht, hn, ?_⟩
  intro w hw
  rw [← he]
  exact hsupport w hw

end OracleTemplate.BallProximal
