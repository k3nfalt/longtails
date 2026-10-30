import Mathlib.Analysis.Complex.ExponentialBounds
import LongTails.Algorithms.KnownValueNondual
import LongTails.Proofs.NondualProjection
import LongTails.Proofs.AdamNormalizedMoments
import LongTails.Proofs.SymmetricGeneralizedDescent

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.KnownValueNondualGeometry

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual

lemma initialBody_norm (p : Public) {u : Point p} (hu : u ∈ initialBody p) : ‖u‖ ≤ p.R :=
  (AdamNormalizedMoments.norm_le_coordinate_sum u).trans hu

lemma initialBody_closed (p : Public) : IsClosed (initialBody p) := by
  apply isClosed_le _ continuous_const
  fun_prop

lemma initialBody_compact (p : Public) : IsCompact (initialBody p) := by
  apply (isCompact_closedBall (0 : Point p) p.R).of_isClosed_subset (initialBody_closed p)
  intro u hu
  simpa only [mem_closedBall, dist_zero_right] using initialBody_norm p hu

lemma initialBody_convex (p : Public) : Convex ℝ (initialBody p) := by
  intro x hx y hy a b ha hb hab
  change ∑ i, |x i| ≤ p.R at hx
  change ∑ i, |y i| ≤ p.R at hy
  change ∑ i, |a * x i + b * y i| ≤ p.R
  calc
    _ ≤ ∑ i, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
    _ = a * (∑ i, |x i|) + b * (∑ i, |y i|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a * p.R + b * p.R := by gcongr
    _ = p.R := by rw [← add_mul, hab, one_mul]

lemma minimizer_displacement_mem (p : Public) (xstar : Point p)
    (hR : ∑ i, |p.x0 i - xstar i| ≤ p.R) : xstar - p.x0 ∈ initialBody p := by
  change ∑ i, |xstar i - p.x0 i| ≤ p.R
  simpa only [abs_sub_comm] using hR

lemma translated_body_distance (p : Public) (xstar : Point p)
    (hR : ‖p.x0 - xstar‖ ≤ p.R) {u : Point p} (hu : u ∈ initialBody p) :
    ‖p.x0 + u - xstar‖ ≤ 2 * p.R := by
  have he : p.x0 + u - xstar = (p.x0 - xstar) + u := by module
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [initialBody_norm p hu])

lemma selector_mem (p : Public) (hd : 0 < p.d) {K : Set (Point p)}
    (hne : K.Nonempty) (hco : IsCompact K) (hcv : Convex ℝ K) :
    selector p K - p.x0 ∈ K := by
  let : NeZero p.d := ⟨Nat.ne_of_gt hd⟩
  simp only [selector, dite_eq_right (Nat.ne_of_gt hd), add_sub_cancel_left]
  exact NondualProjection.center_mem hne hco hcv _

lemma selector_distance (p : Public) (hd : 0 < p.d) (xstar : Point p)
    (hR : ‖p.x0 - xstar‖ ≤ p.R) {K : Set (Point p)}
    (hne : K.Nonempty) (hco : IsCompact K) (hcv : Convex ℝ K)
    (hK : K ⊆ initialBody p) : ‖selector p K - xstar‖ ≤ 2 * p.R := by
  have h := translated_body_distance p xstar hR (hK (selector_mem p hd hne hco hcv))
  have he : p.x0 + (selector p K - p.x0) - xstar = selector p K - xstar := by module
  rwa [he] at h

lemma rootCut_closed (p : Public) (c : Control p) (hc : IsClosed c.body)
    (x : Point p) (value : ℝ) (g : Point p) : IsClosed (rootCut p c x value g) := by
  apply hc.inter
  apply isClosed_le _ continuous_const
  fun_prop

lemma rootCut_compact (p : Public) (c : Control p) (hc : IsCompact c.body)
    (x : Point p) (value : ℝ) (g : Point p) : IsCompact (rootCut p c x value g) :=
  hc.of_isClosed_subset (rootCut_closed p c hc.isClosed x value g) (fun _ hu => hu.1)

lemma rootCut_convex (p : Public) (c : Control p) (hc : Convex ℝ c.body)
    (x : Point p) (value : ℝ) (g : Point p) : Convex ℝ (rootCut p c x value g) := by
  apply hc.inter
  have he : {u : Point p | value + ⟪g, p.x0 + u - x⟫ +
      (if c.warm then warmScale p / (2 * p.L1) * ‖g‖ else 0) ≤ p.fstar} =
      {u : Point p | ⟪g, u⟫ ≤ p.fstar - value - ⟪g, p.x0 - x⟫ -
        (if c.warm then warmScale p / (2 * p.L1) * ‖g‖ else 0)} := by
    ext u
    have hv : p.x0 + u - x = (p.x0 - x) + u := by module
    simp only [mem_ofPred_eq, hv, inner_add_right]
    constructor <;> intro h <;> linarith
  rw [he]
  apply convex_halfSpace_le
  exact ⟨fun u v => inner_add_right _ _ _, fun a u => real_inner_smul_right _ _ _⟩

lemma warmScale_one_le (p : Public) : 1 ≤ warmScale p := by
  unfold warmScale
  have hn : 0 ≤ (⌈(p.L1 * p.R) ^ (1 / 3 : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

lemma rootCut_retains_minimizer (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hconv : ConvexOn ℝ univ f) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (c : Control p) (xstar x : Point p) (hmin : IsMinOn f univ xstar)
    (hval : f xstar = p.fstar) (hmem : xstar - p.x0 ∈ c.body)
    (hlarge : c.warm = true → 2 * p.L0 * Real.exp (warmScale p) / p.L1 ≤ ‖g x‖) :
    xstar - p.x0 ∈ rootCut p c x (f x) (g x) := by
  refine ⟨hmem, ?_⟩
  change f x + ⟪g x, p.x0 + (xstar - p.x0) - x⟫ +
    (if c.warm then warmScale p / (2 * p.L1) * ‖g x‖ else 0) ≤ p.fstar
  have he : p.x0 + (xstar - p.x0) - x = xstar - x := by module
  rw [he, ← hval]
  by_cases hw : c.warm = true
  · simp only [hw, ite_true]
    exact SymmetricGeneralizedDescent.warmup_root_cut hgrad hg hconv hL0 hL1 hgs
      xstar x hmin (warmScale_one_le p) (hlarge hw)
  · simp [hw]
    have h := OracleTemplate.Gradient.convex_support hconv hgrad x xstar
    linarith

lemma gap_le_gradient_distance (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (xstar x : Point p) : f x - f xstar ≤ ‖g x‖ * ‖x - xstar‖ := by
  have hc := OracleTemplate.Gradient.convex_support hconv hgrad x xstar
  have he : ⟪g x, xstar - x⟫ = -⟪g x, x - xstar⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at hc
  have hi := real_inner_le_norm (g x) (x - xstar)
  linarith

lemma small_gradient_accuracy (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hε : 0 < p.ε) (xstar x : Point p) (hdist : ‖x - xstar‖ ≤ 2 * p.R)
    (hsmall : 4 * p.R * ‖g x‖ ≤ p.ε / 2) : f x - f xstar ≤ p.ε := by
  have h := (gap_le_gradient_distance p hconv hgrad xstar x).trans
    (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  nlinarith

lemma warmup_failure_gradient (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R)
    (xstar x : Point p) (hval : f xstar = p.fstar) (hdist : ‖x - xstar‖ ≤ 2 * p.R)
    {Γ : ℝ} (hΓ : 4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p) ≤ Γ)
    (hfail : Γ < f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar) :
    2 * p.L0 * Real.exp (warmScale p) / p.L1 ≤ ‖g x‖ := by
  have hgap := (gap_le_gradient_distance p hconv hgrad xstar x).trans
    (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  rw [hval] at hgap
  have hD : 0 ≤ 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) := by positivity
  have he : 4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p) =
      2 * p.R * (2 * p.L0 * Real.exp (warmScale p) / p.L1) := by ring
  rw [he] at hΓ
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * p.R by positivity)).mp
  nlinarith only [hΓ, hfail, hD, hgap]

lemma failed_cut_retains_minimizer (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hconv : ConvexOn ℝ univ f) (hL0 : 0 < p.L0) (hL1 : 0 < p.L1) (hR : 0 < p.R)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (c : Control p) (xstar x : Point p) (hmin : IsMinOn f univ xstar)
    (hval : f xstar = p.fstar) (hmem : xstar - p.x0 ∈ c.body)
    (hdist : ‖x - xstar‖ ≤ 2 * p.R)
    (hΓ : c.warm = true → 4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p) ≤ c.target)
    (hfail : c.target < f x - 5 * ‖g x‖ ^ 2 / (24 * (p.L0 + p.L1 * ‖g x‖)) - p.fstar) :
    xstar - p.x0 ∈ rootCut p c x (f x) (g x) := by
  apply rootCut_retains_minimizer p hgrad hg hconv hL0 hL1 hgs c xstar x hmin hval hmem
  intro hw
  exact warmup_failure_gradient p hconv hgrad hL0 hL1 hR xstar x hval hdist (hΓ hw) hfail

lemma segment_distance (p : Public) (xstar z y x : Point p)
    (hz : ‖z - xstar‖ ≤ 2 * p.R) (hy : ‖y - xstar‖ ≤ 2 * p.R)
    (hx : x ∈ segment ℝ z y) : ‖x - xstar‖ ≤ 2 * p.R := by
  have h := (convex_closedBall xstar (2 * p.R)).segment_subset
    (show z ∈ closedBall xstar (2 * p.R) by simpa [mem_closedBall, dist_eq_norm] using hz)
    (show y ∈ closedBall xstar (2 * p.R) by simpa [mem_closedBall, dist_eq_norm] using hy) hx
  simpa [mem_closedBall, dist_eq_norm] using h

lemma segment_length (p : Public) (xstar z y : Point p)
    (hz : ‖z - xstar‖ ≤ 2 * p.R) (hy : ‖y - xstar‖ ≤ 2 * p.R) : ‖y - z‖ ≤ 4 * p.R := by
  have h := dist_triangle y xstar z
  simp only [dist_eq_norm] at h
  rw [norm_sub_rev xstar z] at h
  linarith

lemma small_curvature_initial_gap (p : Public) {f : Point p → ℝ} {g : Point p → Point p}
    (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hL0 : 0 < p.L0) (hL1 : 0 < p.L1)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar)
    (hdist : ‖p.x0 - xstar‖ ≤ p.R) (hB : p.L1 * p.R ≤ 1) :
    f p.x0 - f xstar ≤ 2 * p.L0 * p.R ^ 2 := by
  have hzero : g xstar = 0 := by
    apply (toDual ℝ (Point p)).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hgrad xstar).hasFDerivAt
  have h := SymmetricGeneralizedDescent.objective_upper hgrad hg hL0.le hL1 hgs xstar (p.x0 - xstar)
  simp only [add_sub_cancel, hzero, inner_zero_left, norm_zero, mul_zero, add_zero] at h
  have hexp : Real.exp (p.L1 * ‖p.x0 - xstar‖) ≤ 4 := by
    apply (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hdist hL1.le).trans hB)).trans
    have he := Real.exp_one_lt_d9
    norm_num at he
    linarith
  calc
    f p.x0 - f xstar ≤ p.L0 * Real.exp (p.L1 * ‖p.x0 - xstar‖) / 2 * ‖p.x0 - xstar‖ ^ 2 := by linarith
    _ ≤ p.L0 * 4 / 2 * p.R ^ 2 := by gcongr
    _ = _ := by ring

end LongTails.Proofs.KnownValueNondualGeometry
