import LongTails.Proofs.ConstrainedSaddleGeometry
import LongTails.Setups.ConstrainedMinimaxSecondOrder
import LongTails.Proofs.PLMinimaxOracleGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

open Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedMinimaxValue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exists_max_of_quadratic_upper [FiniteDimensional ℝ E] {Y : Set E}
    (hY : IsClosed Y) {f : E → ℝ} (hc : Continuous f) {μ : ℝ} (hμ : 0 < μ)
    {y0 a : E} (hy0 : y0 ∈ Y)
    (hu : ∀ y ∈ Y, f y ≤ f y0 + ⟪a, y - y0⟫ - μ / 2 * ‖y - y0‖ ^ 2) :
    ∃ y ∈ Y, IsMaxOn f Y y := by
  let R := 2 * ‖a‖ / μ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRm : μ * R = 2 * ‖a‖ + μ := by dsimp [R]; field_simp
  have hK : IsCompact (Y ∩ closedBall y0 R) :=
    (isCompact_closedBall y0 R).inter_left hY
  have hyK : y0 ∈ Y ∩ closedBall y0 R := ⟨hy0, by simp [hR.le]⟩
  obtain ⟨y, hy, hm⟩ := hK.exists_isMaxOn ⟨y0, hyK⟩ hc.continuousOn
  refine ⟨y, hy.1, fun z hz => ?_⟩
  by_cases hzK : z ∈ closedBall y0 R
  · exact hm ⟨hz, hzK⟩
  · have hd : R < ‖z - y0‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hzK
    have hi := real_inner_le_norm a (z - y0)
    have hmd : 2 * ‖a‖ < μ * ‖z - y0‖ := by
      nlinarith [mul_lt_mul_of_pos_left hd hμ]
    have hprod := mul_le_mul_of_nonneg_right hmd.le (norm_nonneg (z - y0))
    have hf : f z ≤ f y0 := by nlinarith [hu z hz]
    exact hf.trans (hm hyK)

lemma max_variational [CompleteSpace E] {Y : Set E} (hY : Convex ℝ Y) {f : E → ℝ} {g y : E}
    (hy : y ∈ Y) (hm : IsMaxOn f Y y) (hg : HasGradientAt f g y) :
    ∀ v ∈ Y, ⟪g, v - y⟫ ≤ 0 := by
  intro v hv
  exact hm.isLocalMaxOn.hasFDerivWithinAt_nonpos hg.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hY.segment_subset hy hv))

lemma strongly_concave_gradient {Y : Set E} {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hc : ∀ y ∈ Y, ∀ z ∈ Y, f z ≤ f y + ⟪g y, z - y⟫ - μ / 2 * ‖z - y‖ ^ 2)
    {y z : E} (hy : y ∈ Y) (hz : z ∈ Y) :
    μ * ‖y - z‖ ^ 2 ≤ -⟪g y - g z, y - z⟫ := by
  have h1 := hc y hy z hz
  have h2 := hc z hz y hy
  have he : z - y = -(y - z) := by abel
  rw [he, inner_neg_right, norm_neg] at h1
  rw [inner_sub_left]
  linarith

lemma maximizer_growth {Y : Set E} {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hc : ∀ y ∈ Y, ∀ z ∈ Y, f z ≤ f y + ⟪g y, z - y⟫ - μ / 2 * ‖z - y‖ ^ 2)
    {y : E} (hy : y ∈ Y) (hv : ∀ z ∈ Y, ⟪g y, z - y⟫ ≤ 0) :
    ∀ z ∈ Y, f z + μ / 2 * ‖z - y‖ ^ 2 ≤ f y := by
  intro z hz
  linarith [hc y hy z hz, hv z hz]

lemma variational_stability {μ : ℝ} {y z a b c : E}
    (hmono : μ * ‖y - z‖ ^ 2 ≤ -⟪a - b, y - z⟫)
    (ha : ⟪a, z - y⟫ ≤ 0) (hc : ⟪c, y - z⟫ ≤ 0) :
    μ * ‖y - z‖ ≤ ‖b - c‖ := by
  have he : z - y = -(y - z) := by abel
  rw [he, inner_neg_right] at ha
  have hi := real_inner_le_norm (b - c) (y - z)
  simp only [inner_sub_left] at hmono hi
  by_cases hn : ‖y - z‖ = 0
  · simp [hn]
  · have hnpos := lt_of_le_of_ne (norm_nonneg (y - z)) (Ne.symm hn)
    have hh : (μ * ‖y - z‖) * ‖y - z‖ ≤ ‖b - c‖ * ‖y - z‖ := by
      nlinarith
    exact le_of_mul_le_mul_right hh hnpos

omit [InnerProductSpace ℝ E] in
lemma max_unique {Y : Set E} {f : E → ℝ} {μ : ℝ} (hμ : 0 < μ) {y z : E}
    (hy : y ∈ Y) (hz : z ∈ Y) (hm : IsMaxOn f Y z)
    (hg : ∀ v ∈ Y, f v + μ / 2 * ‖v - y‖ ^ 2 ≤ f y) : z = y := by
  have h1 := hg z hz
  have h2 : f y ≤ f z := hm hy
  have hp : μ / 2 * ‖z - y‖ ^ 2 ≤ 0 := by linarith
  have hs : ‖z - y‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (show μ / 2 * ‖z - y‖ ^ 2 ≤ μ / 2 * 0 by simpa using hp)
      (by linarith : 0 < μ / 2)
  have hn : ‖z - y‖ = 0 := by nlinarith [sq_nonneg ‖z - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

open LongTails.Setups.ConstrainedMinimaxSecondOrder

lemma attain {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (x : p.E) :
    ∃ y ∈ p.Y, IsMaxOn (fun y => f (WithLp.toLp 2 (x, y))) p.Y y := by
  rcases hv with ⟨hμ, _, _, _, _, _, hY, _, hy0⟩
  have hc : Continuous (fun y => f (WithLp.toLp 2 (x, y))) :=
    continuous_iff_continuousAt.mpr fun y =>
      (OracleTemplate.PLMinimax.joint_gradient_snd (H.hasGradient (WithLp.toLp 2 (x, y)))).continuousAt
  exact exists_max_of_quadratic_upper hY hc hμ hy0
    (fun y _ => H.strongly_concave x p.y0 y)

lemma value_eq {p : Params} {f : Space p → ℝ} {x : p.E} {y : p.F}
    (hy : y ∈ p.Y) (hm : IsMaxOn (fun y => f (WithLp.toLp 2 (x, y))) p.Y y) :
    value f x = f (WithLp.toLp 2 (x, y)) := by
  let : Nonempty p.Y := ⟨⟨y, hy⟩⟩
  unfold value
  apply le_antisymm
  · exact ciSup_le fun z : p.Y => hm z.2
  · have hb : BddAbove (Set.range (fun z : p.Y => f (WithLp.toLp 2 (x, z.1)))) := by
      refine ⟨f (WithLp.toLp 2 (x, y)), ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hm z.2
    exact le_ciSup hb (⟨y, hy⟩ : p.Y)

lemma le_value {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (x : p.E) {y : p.F} (hy : y ∈ p.Y) :
    f (WithLp.toLp 2 (x, y)) ≤ value f x := by
  obtain ⟨z, hz, hm⟩ := attain H hv x
  rw [value_eq hz hm]
  exact hm hy

lemma maximizers_distance {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) {x x' : p.E} {y y' : p.F} (hy : y ∈ p.Y) (hy' : y' ∈ p.Y)
    (hm : IsMaxOn (fun v => f (WithLp.toLp 2 (x, v))) p.Y y)
    (hm' : IsMaxOn (fun v => f (WithLp.toLp 2 (x', v))) p.Y y') :
    p.μ * ‖y - y'‖ ≤ p.L * ‖x - x'‖ := by
  have hY : Convex ℝ p.Y := hv.2.2.2.2.2.2.2.1
  have hn := strongly_concave_gradient
    (fun v (_ : v ∈ p.Y) w (_ : w ∈ p.Y) => H.strongly_concave x v w) hy hy'
  have h1 := max_variational hY hy hm
    (OracleTemplate.PLMinimax.joint_gradient_snd (H.hasGradient (WithLp.toLp 2 (x, y)))) y' hy'
  have h2 := max_variational hY hy' hm'
    (OracleTemplate.PLMinimax.joint_gradient_snd (H.hasGradient (WithLp.toLp 2 (x', y')))) y hy
  have hs := variational_stability hn h1 h2
  have hl := H.gradient_lipschitz (WithLp.toLp 2 (x, y')) (WithLp.toLp 2 (x', y'))
  have hp := WithLp.norm_snd_le p.E
    (gradient f (WithLp.toLp 2 (x, y')) - gradient f (WithLp.toLp 2 (x', y')))
  have he : ‖WithLp.toLp 2 (x, y') - WithLp.toLp 2 (x', y')‖ = ‖x - x'‖ := by
    rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_fst]
  rw [he] at hl
  exact hs.trans (hp.trans hl)

lemma primal_gradient_lipschitz {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hL : 0 ≤ p.L) (x x' : p.E) (y y' : p.F) :
    ‖(gradient f (WithLp.toLp 2 (x, y))).fst -
      (gradient f (WithLp.toLp 2 (x', y'))).fst‖ ≤ p.L * (‖x - x'‖ + ‖y - y'‖) := by
  have hp := WithLp.norm_fst_le p.E
    (gradient f (WithLp.toLp 2 (x, y)) - gradient f (WithLp.toLp 2 (x', y')))
  have hl := H.gradient_lipschitz (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (x', y'))
  have hn := OracleTemplate.PLMinimax.joint_norm_le
    (WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x', y'))
  exact hp.trans (hl.trans (mul_le_mul_of_nonneg_left hn hL))

lemma primal_upper {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hL : 0 ≤ p.L) (x x' : p.E) (y : p.F) :
    f (WithLp.toLp 2 (x', y)) ≤ f (WithLp.toLp 2 (x, y)) +
      ⟪(gradient f (WithLp.toLp 2 (x, y))).fst, x' - x⟫ + p.L / 2 * ‖x' - x‖ ^ 2 := by
  apply OracleTemplate.Gradient.smooth_upper_bound
    (fun x => OracleTemplate.PLMinimax.joint_gradient_fst (H.hasGradient (WithLp.toLp 2 (x, y))))
  intro a b
  simpa using primal_gradient_lipschitz H hL a b y y

lemma primal_lower {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hL : 0 ≤ p.L) (x x' : p.E) (y : p.F) :
    f (WithLp.toLp 2 (x, y)) +
      ⟪(gradient f (WithLp.toLp 2 (x, y))).fst, x' - x⟫ - p.L / 2 * ‖x' - x‖ ^ 2 ≤
        f (WithLp.toLp 2 (x', y)) := by
  have hh := OracleTemplate.Gradient.smooth_upper_bound
    (f := fun x => -f (WithLp.toLp 2 (x, y)))
    (oracle := fun x => -(gradient f (WithLp.toLp 2 (x, y))).fst) (L := p.L)
    (fun x => OracleTemplate.TwoSidedPL.hasGradientAt_neg'
      (OracleTemplate.PLMinimax.joint_gradient_fst (H.hasGradient (WithLp.toLp 2 (x, y)))))
    (fun a b => by
      rw [neg_sub_neg, norm_sub_rev]
      simpa using primal_gradient_lipschitz H hL a b y y) x x'
  simp only [inner_neg_left] at hh
  linarith

lemma value_remainder {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) {x : p.E} {y : p.F} (hy : y ∈ p.Y)
    (hm : IsMaxOn (fun v => f (WithLp.toLp 2 (x, v))) p.Y y) (h : p.E) :
    |value f (x + h) - value f x - ⟪(gradient f (WithLp.toLp 2 (x, y))).fst, h⟫| ≤
      (p.L + p.L ^ 2 / p.μ) * ‖h‖ ^ 2 := by
  have hμ : 0 < p.μ := hv.1
  have hL : 0 < p.L := hμ.trans_le hv.2.1
  obtain ⟨v, hvY, hvm⟩ := attain H hv (x + h)
  have hd := maximizers_distance H hv hy hvY hm hvm
  simp only [sub_add_cancel_left, norm_neg] at hd
  have hl : ‖(gradient f (WithLp.toLp 2 (x, v))).fst -
      (gradient f (WithLp.toLp 2 (x, y))).fst‖ ≤ p.L ^ 2 / p.μ * ‖h‖ := by
    have hh := primal_gradient_lipschitz H hL.le x x v y
    simp only [sub_self, norm_zero, zero_add, norm_sub_rev v y] at hh
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith [mul_le_mul_of_nonneg_left hd hL.le,
      mul_le_mul_of_nonneg_left hh hμ.le]
  have hi : ⟪(gradient f (WithLp.toLp 2 (x, v))).fst, h⟫ ≤
      ⟪(gradient f (WithLp.toLp 2 (x, y))).fst, h⟫ + p.L ^ 2 / p.μ * ‖h‖ ^ 2 := by
    have hi := real_inner_le_norm ((gradient f (WithLp.toLp 2 (x, v))).fst -
      (gradient f (WithLp.toLp 2 (x, y))).fst) h
    rw [inner_sub_left] at hi
    nlinarith [mul_le_mul_of_nonneg_right hl (norm_nonneg h)]
  have hu := primal_upper H hL.le x (x + h) v
  have hlo := primal_lower H hL.le x (x + h) y
  have hmax := le_value H hv (x + h) hy
  have hxy : f (WithLp.toLp 2 (x, v)) ≤ f (WithLp.toLp 2 (x, y)) := hm hvY
  rw [value_eq hy hm, value_eq hvY hvm] at *
  simp only [add_sub_cancel_left] at hu hlo
  have hp : 0 ≤ (p.L ^ 2 / p.μ) * ‖h‖ ^ 2 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖h‖]

lemma value_hasGradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) {x : p.E} {y : p.F} (hy : y ∈ p.Y)
    (hm : IsMaxOn (fun v => f (WithLp.toLp 2 (x, v))) p.Y y) :
    HasGradientAt (value f) (gradient f (WithLp.toLp 2 (x, y))).fst x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply OracleTemplate.PLMinimax.hasFDerivAt_of_quadratic_remainder
    (C := p.L + p.L ^ 2 / p.μ)
  intro h
  simpa [Real.norm_eq_abs] using value_remainder H hv hy hm h

lemma value_differentiable {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) : Differentiable ℝ (value f) := by
  intro x
  obtain ⟨y, hy, hm⟩ := attain H hv x
  exact (value_hasGradient H hv hy hm).differentiableAt

end LongTails.Proofs.ConstrainedMinimaxValue
