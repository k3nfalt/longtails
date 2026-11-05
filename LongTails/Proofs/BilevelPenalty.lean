import LongTails.Proofs.BilevelGeometry
import LongTails.Algorithms.BilevelAccelerated
import LongTails.Proofs.GdConvex
import LongTails.Proofs.LoraObjective
import LongTails.Proofs.ThirdOrderTaylorBounds

set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelPenalty

open LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated BilevelGeometry
open scoped RealInnerProductSpace

noncomputable def innerObjective {p : Params} (I : Instance p) (x : p.X) (lam : ℝ) (y : p.Y) : ℝ :=
  I.g (x, y) + lam⁻¹ * I.f (x, y)

noncomputable def sliceGradient {p : Params} (f : p.X × p.Y → ℝ) (x : p.X) (y : p.Y) : p.Y :=
  lowerRestriction p (fderiv ℝ f (x, y))

lemma slice_hasGradientAt {p : Params} {f : p.X × p.Y → ℝ}
    (hf : Differentiable ℝ f) (x : p.X) (y : p.Y) :
    HasGradientAt (fun y => f (x, y)) (sliceGradient f x y) y := by
  apply hasFDerivAt_iff_hasGradientAt.mp
  exact (hf (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)

lemma sliceGradient_lipschitz {p : Params} {f : p.X × p.Y → ℝ}
    (hLip : ∀ z w, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ p.L * ‖z - w‖)
    (x : p.X) (y z : p.Y) : ‖sliceGradient f x y - sliceGradient f x z‖ ≤ p.L * ‖y - z‖ := by
  change ‖lowerRestriction p (fderiv ℝ f (x, y)) - lowerRestriction p (fderiv ℝ f (x, z))‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖lowerRestriction p‖ * ‖fderiv ℝ f (x, y) - fderiv ℝ f (x, z)‖ := (lowerRestriction p).le_opNorm _
    _ ≤ 1 * (p.L * ‖(x, y) - (x, z)‖) :=
      mul_le_mul (lowerRestriction_norm p) (hLip _ _) (norm_nonneg _) zero_le_one
    _ = _ := by simp

lemma lowerReply_decomposition {p : Params} (I : Instance p) (x : p.X) (y : p.Y) (lam : ℝ) :
    lowerReply p lam (firstOrderReply I (x, y)) =
      sliceGradient I.g x y + lam⁻¹ • sliceGradient I.f x y := by
  change lowerRestriction p (fderiv ℝ I.g (x, y) + lam⁻¹ • fderiv ℝ I.f (x, y)) = _
  simp only [map_add, map_smul, sliceGradient]

lemma inner_hasGradientAt {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g)
    (x : p.X) (lam : ℝ) (y : p.Y) :
    HasGradientAt (innerObjective I x lam) (lowerReply p lam (firstOrderReply I (x, y))) y := by
  unfold innerObjective
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (((hg (x, y)).hasFDerivAt).add
    ((hf (x, y)).hasFDerivAt.const_smul lam⁻¹)).comp y (hasFDerivAt_prodMk_right x y)
  simpa [lowerReply, firstOrderReply, innerObjective, Function.comp_def,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hd


lemma inner_lipschitz {p : Params} {I : Instance p}
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    {lam : ℝ} (ha : 0 ≤ lam⁻¹) (hb : lam⁻¹ ≤ 1) (x : p.X) (y z : p.Y) :
    ‖lowerReply p lam (firstOrderReply I (x, y)) - lowerReply p lam (firstOrderReply I (x, z))‖ ≤
      (2 * p.L) * ‖y - z‖ := by
  rw [lowerReply_decomposition, lowerReply_decomposition, add_sub_add_comm, ← smul_sub]
  calc
    _ ≤ ‖sliceGradient I.g x y - sliceGradient I.g x z‖ +
        ‖lam⁻¹ • (sliceGradient I.f x y - sliceGradient I.f x z)‖ := norm_add_le _ _
    _ = ‖sliceGradient I.g x y - sliceGradient I.g x z‖ +
        lam⁻¹ * ‖sliceGradient I.f x y - sliceGradient I.f x z‖ := by rw [norm_smul, Real.norm_of_nonneg ha]
    _ ≤ p.L * ‖y - z‖ + 1 * (p.L * ‖y - z‖) := by
      gcongr
      · exact sliceGradient_lipschitz hg1 x y z
      · exact sliceGradient_lipschitz hf1 x y z
    _ = _ := by ring

lemma slice_lower_support {p : Params} {f : p.X × p.Y → ℝ}
    (hf : Differentiable ℝ f)
    (hLip : ∀ z w, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ p.L * ‖z - w‖)
    (x : p.X) (y z : p.Y) :
    f (x, y) + ⟪sliceGradient f x y, z - y⟫ - p.L / 2 * ‖z - y‖ ^ 2 ≤ f (x, z) := by
  have hg : ∀ y, HasGradientAt (fun y => -f (x, y)) (-sliceGradient f x y) y :=
    fun y => by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      have hd := (hf (x, y)).hasFDerivAt.neg.comp y (hasFDerivAt_prodMk_right x y)
      simpa [sliceGradient, lowerRestriction_apply, map_neg, Function.comp_def, Pi.neg_apply] using hd
  have hl : ∀ y z, ‖-sliceGradient f x y - -sliceGradient f x z‖ ≤ p.L * ‖y - z‖ := by
    intro y z
    simpa only [neg_sub_neg, norm_sub_rev] using sliceGradient_lipschitz hLip x y z
  have hh := OracleTemplate.Gradient.smooth_upper_bound hg hl y z
  simp only [inner_neg_left] at hh
  linarith

lemma inner_quadratic_support {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (ha : 0 ≤ lam⁻¹) (hb : p.L * lam⁻¹ ≤ p.μ / 2)
    (x : p.X) (y z : p.Y) :
    innerObjective I x lam y + ⟪lowerReply p lam (firstOrderReply I (x, y)), z - y⟫ +
      (p.μ / 2) / 2 * ‖z - y‖ ^ 2 ≤ innerObjective I x lam z := by
  have hh := mul_le_mul_of_nonneg_left (slice_lower_support hf hf1 x y z) ha
  have hg := hsc x y z
  have hcoef := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖z - y‖)
  rw [lowerReply_decomposition, inner_add_left, inner_smul_left]
  simp only [conj_trivial, sliceGradient, lowerRestriction_inner, innerObjective] at *
  nlinarith

lemma support_distance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hsc : ∀ y z, f y + ⟪g y, z - y⟫ + μ / 2 * ‖z - y‖ ^ 2 ≤ f z)
    (u v : E) : μ * ‖u - v‖ ≤ ‖g u - g v‖ := by
  have h1 := hsc v u
  have h2 := hsc u v
  rw [show v - u = -(u - v) by abel, inner_neg_right, norm_neg] at h2
  have hi : μ * ‖u - v‖ ^ 2 ≤ ⟪g u - g v, u - v⟫ := by
    rw [inner_sub_left]
    linarith
  have hh := hi.trans (real_inner_le_norm (g u - g v) (u - v))
  by_cases he : ‖u - v‖ = 0
  · simp [he]
  · have hp := lt_of_le_of_ne (norm_nonneg (u - v)) (Ne.symm he)
    nlinarith

lemma inner_minimum_exists {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (ha : 0 ≤ lam⁻¹) (hb : p.L * lam⁻¹ ≤ p.μ / 2) (x : p.X) :
    ∃ y, ∀ z, innerObjective I x lam y ≤ innerObjective I x lam z := by
  have hd := fun y => (inner_hasGradientAt hf hg x lam y).hasFDerivAt
  apply BilevelMinimizers.exists_minimum_of_quadratic_support
    (show Continuous (innerObjective I x lam) from (show Differentiable ℝ (innerObjective I x lam) from fun y => (hd y).differentiableAt).continuous)
    ((InnerProductSpace.toDual ℝ p.Y) (lowerReply p lam (firstOrderReply I (x, 0)))) (half_pos hμ)
  intro z
  simpa using inner_quadratic_support hf hf1 hsc ha hb x 0 z

lemma inner_convex {p : Params} {I : Instance p} (hf : Differentiable ℝ I.f) (hμ : 0 ≤ p.μ)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (ha : 0 ≤ lam⁻¹) (hb : p.L * lam⁻¹ ≤ p.μ / 2) (x : p.X) :
    ConvexOn ℝ Set.univ (innerObjective I x lam) := by
  apply LoraObjective.support_convex (g := fun y => lowerReply p lam (firstOrderReply I (x, y)))
  intro y z
  have hh := inner_quadratic_support hf hf1 hsc ha hb x y z
  have hn : 0 ≤ (p.μ / 2) / 2 * ‖z - y‖ ^ 2 := by positivity
  linarith

lemma inner_stationary {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g)
    (x : p.X) (lam : ℝ) (ystar : p.Y)
    (hmin : ∀ y, innerObjective I x lam ystar ≤ innerObjective I x lam y) :
    lowerReply p lam (firstOrderReply I (x, ystar)) = 0 := by
  have hm : IsLocalMin (innerObjective I x lam) ystar := Filter.Eventually.of_forall hmin
  have hh := hm.hasFDerivAt_eq_zero (inner_hasGradientAt hf hg x lam ystar).hasFDerivAt
  apply (InnerProductSpace.toDual ℝ p.Y).injective
  simpa using hh

lemma derivative_taylor_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {A : E → E →L[ℝ] F} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x, HasFDerivAt f (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ L * ‖x - y‖) (x d : E) :
    ‖f (x + d) - f x - A x d‖ ≤ L * ‖d‖ ^ 2 := by
  let R : ℝ → F := fun t => f (x + t • d) - f x - t • A x d
  let D : ℝ → F := fun t => (A (x + t • d) - A x) d
  have hd : ∀ t, HasDerivAt R (D t) t := by
    intro t
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh := ((hf (x + t • d)).comp_hasDerivAt t hline).sub_const (f x)
    convert hh.sub ((hasDerivAt_id t).smul_const (A x d)) using 1
    · ext t
      rfl
    · simp [D]
  have hb : ∀ t, ‖D t‖ ≤ (L * ‖d‖ ^ 2) * |t| ^ 1 := by
    intro t
    have h1 := (A (x + t • d) - A x).le_opNorm d
    have h2 := hLip (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg d)
    dsimp [D]
    nlinarith only [h1, h3]
  have hh := ThirdOrderTaylorBounds.power_derivative_bound (mul_nonneg hL (sq_nonneg ‖d‖)) 1 hd hb 1
  simpa [R] using hh

lemma sliceGradient_norm {p : Params} {f : p.X × p.Y → ℝ}
    (hf0 : ∀ z, ‖fderiv ℝ f z‖ ≤ p.L) (x : p.X) (y : p.Y) :
    ‖sliceGradient f x y‖ ≤ p.L := by
  calc
    _ ≤ ‖lowerRestriction p‖ * ‖fderiv ℝ f (x, y)‖ := (lowerRestriction p).le_opNorm _
    _ ≤ 1 * p.L := mul_le_mul (lowerRestriction_norm p) (hf0 _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma base_residual_distance {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x : p.X) (y : p.Y) :
    p.μ * ‖y - lowerSolution I x‖ ≤ ‖sliceGradient I.g x y‖ := by
  have hs : ∀ u v, I.g (x, u) + ⟪sliceGradient I.g x u, v - u⟫ +
      p.μ / 2 * ‖v - u‖ ^ 2 ≤ I.g (x, v) := by
    intro u v
    simpa only [sliceGradient, lowerRestriction_inner] using hsc x u v
  have hh := support_distance hs y (lowerSolution I x)
  have hz : sliceGradient I.g x (lowerSolution I x) = 0 := lowerGradient_root hg hμ hsc x
  simpa [hz] using hh

lemma penalty_displacement {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (hlam : 0 < lam) (x : p.X) (ystar : p.Y)
    (hmin : ∀ y, innerObjective I x lam ystar ≤ innerObjective I x lam y) :
    lam * ‖ystar - lowerSolution I x‖ ≤ p.L / p.μ := by
  have hs := inner_stationary hf hg x lam ystar hmin
  rw [lowerReply_decomposition] at hs
  have hg0 : sliceGradient I.g x ystar = -(lam⁻¹ • sliceGradient I.f x ystar) :=
    eq_neg_of_add_eq_zero_left hs
  have hh := base_residual_distance hg hμ hsc x ystar
  rw [hg0, norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)] at hh
  have hn := sliceGradient_norm hf0 x ystar
  have hbound : p.μ * ‖ystar - lowerSolution I x‖ ≤ lam⁻¹ * p.L :=
    hh.trans (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hlam.le))
  apply (le_div_iff₀ hμ).mpr
  have hm := mul_le_mul_of_nonneg_left hbound hlam.le
  calc
    _ = lam * (p.μ * ‖ystar - lowerSolution I x‖) := by ring
    _ ≤ lam * (lam⁻¹ * p.L) := hm
    _ = p.L := by rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]

lemma initial_base_radius {p : Params} {I : Instance p}
    (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ) (hL : 0 ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hG : ‖gradient (fun y => I.g (p.x0, y)) p.y0‖ ≤ p.G)
    {R : ℝ} (x : p.X) (hx : ‖x - p.x0‖ ≤ R) :
    ‖p.y0 - lowerSolution I x‖ ≤ (p.G + p.L * R) / p.μ := by
  have hstart : ‖sliceGradient I.g p.x0 p.y0‖ ≤ p.G := by
    rwa [(slice_hasGradientAt hg p.x0 p.y0).gradient] at hG
  have hdiff : ‖sliceGradient I.g x p.y0 - sliceGradient I.g p.x0 p.y0‖ ≤ p.L * R := by
    have hh := lowerGradient_lipschitz hg1 (x, p.y0) (p.x0, p.y0)
    have hh' : ‖sliceGradient I.g x p.y0 - sliceGradient I.g p.x0 p.y0‖ ≤ p.L * ‖x - p.x0‖ := by
      simpa [sliceGradient, lowerGradient, lowerRestriction_apply] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hx hL)
  have hnorm : ‖sliceGradient I.g x p.y0‖ ≤ p.G + p.L * R := by
    have hh := norm_sub_le (sliceGradient I.g x p.y0 - sliceGradient I.g p.x0 p.y0)
      (-sliceGradient I.g p.x0 p.y0)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    linarith
  apply (le_div_iff₀ hμ).mpr
  have hh := (base_residual_distance hg hμ hsc x p.y0).trans hnorm
  nlinarith only [hh]

lemma initial_penalty_radius {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ) (hL : 0 ≤ p.L)
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hG : ‖gradient (fun y => I.g (p.x0, y)) p.y0‖ ≤ p.G)
    {lam R : ℝ} (hlam : 0 < lam) (x : p.X) (hx : ‖x - p.x0‖ ≤ R) (ystar : p.Y)
    (hmin : ∀ y, innerObjective I x lam ystar ≤ innerObjective I x lam y) :
    ‖p.y0 - ystar‖ ≤ (p.G + p.L * R + p.L / lam) / p.μ := by
  have hb := initial_base_radius hg hμ hL hsc hg1 hG x hx
  have hp := penalty_displacement hf hg hμ hf0 hsc hlam x ystar hmin
  have hp' : ‖lowerSolution I x - ystar‖ ≤ p.L / lam / p.μ := by
    rw [norm_sub_rev]
    apply (le_div_iff₀ hμ).mpr
    apply (le_div_iff₀ hlam).mpr
    have hh := (le_div_iff₀ hμ).mp hp
    nlinarith only [hh]
  calc
    _ ≤ ‖p.y0 - lowerSolution I x‖ + ‖lowerSolution I x - ystar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (p.G + p.L * R) / p.μ + p.L / lam / p.μ := add_le_add hb hp'
    _ = _ := by ring

lemma full_gradient_taylor {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hL : 0 ≤ p.L)
    (hg2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (x : p.X) (y z : p.Y) :
    ‖fderiv ℝ I.g (x, y) - fderiv ℝ I.g (x, z) -
      fderiv ℝ (fderiv ℝ I.g) (x, z) (0, y - z)‖ ≤ p.L * ‖y - z‖ ^ 2 := by
  have hgc : ContDiff ℝ 2 I.g := hg.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ I.g) := (contDiff_succ_iff_fderiv.mp hgc).2.2
  have hh := derivative_taylor_bound hL (fun w => (hd.differentiable (by norm_num) w).hasFDerivAt)
    hg2 (x, z) (0, y - z)
  simpa using hh

lemma scaled_remainder_norm {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hL : 0 ≤ p.L)
    (hg2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    {lam κ : ℝ} (hlam : 0 < lam) (x : p.X) (y z : p.Y)
    (hd : lam * ‖y - z‖ ≤ κ) :
    ‖lam • (fderiv ℝ I.g (x, y) - fderiv ℝ I.g (x, z)) -
      fderiv ℝ (fderiv ℝ I.g) (x, z) (0, lam • (y - z))‖ ≤ p.L * κ ^ 2 / lam := by
  have he : ((0 : p.X), lam • (y - z)) = lam • (0, y - z) := by simp
  rw [he, map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le]
  have ht := full_gradient_taylor hg hL hg2 x y z
  calc
    _ ≤ lam * (p.L * ‖y - z‖ ^ 2) := mul_le_mul_of_nonneg_left ht hlam.le
    _ ≤ p.L * κ ^ 2 / lam := by
      apply (le_div_iff₀ hlam).mpr
      have hs := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hlam.le (norm_nonneg (y - z))) hd 2) hL
      nlinarith only [hs]

lemma upperReply_inner (p : Params) (A : (p.X × p.Y) →L[ℝ] ℝ) (a : p.X) :
    ⟪upperReply p A, a⟫ = A (a, 0) := by
  exact DFunLike.congr_fun ((InnerProductSpace.toDual ℝ p.X).apply_symm_apply
    (A.comp (.inl ℝ p.X p.Y))) a

lemma implicit_cross_pairing {p : Params} {I : Instance p}
    (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a : p.X) (v : p.Y) :
    fderiv ℝ (fderiv ℝ I.g) (x, lowerSolution I x) (0, v) (a, 0) =
      -⟪lowerHessian I (x, lowerSolution I x) v, fderiv ℝ (lowerSolution I) x a⟫ := by
  have hh := BilevelImplicit.root_first_equation
    ((lowerGradient_contDiff hg).differentiable (by norm_num))
    ((lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num))
    (lowerGradient_root (hg.differentiable (by norm_num)) hμ hsc) x a
  rw [(lowerGradient_hasFDerivAt hg (x, lowerSolution I x)).fderiv] at hh
  have hp := congrArg (fun u : p.Y => ⟪u, v⟫) hh
  simp only [ContinuousLinearMap.comp_apply, lowerRestriction_inner, inner_zero_left] at hp
  have he : (a, fderiv ℝ (lowerSolution I) x a) =
      (a, (0 : p.Y)) + (0, fderiv ℝ (lowerSolution I) x a) := by simp
  rw [he, map_add, add_apply] at hp
  have hsym := hg.contDiffAt (x := (x, lowerSolution I x)) |>.isSymmSndFDerivAt (by norm_num)
  rw [hsym.eq (a, 0) (0, v), hsym.eq (0, fderiv ℝ (lowerSolution I) x a) (0, v)] at hp
  rw [lowerHessian_inner]
  linarith

noncomputable def penaltyRemainder {p : Params} (I : Instance p) (x : p.X)
    (y z : p.Y) (lam : ℝ) : (p.X × p.Y) →L[ℝ] ℝ :=
  lam • (fderiv ℝ I.g (x, y) - fderiv ℝ I.g (x, z)) -
    fderiv ℝ (fderiv ℝ I.g) (x, z) (0, lam • (y - z))

lemma penalty_residual_identity {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (hlam : lam ≠ 0) (x : p.X) (y : p.Y)
    (hmin : ∀ u, innerObjective I x lam y ≤ innerObjective I x lam u) :
    lowerHessian I (x, lowerSolution I x) (lam • (y - lowerSolution I x)) +
      sliceGradient I.f x (lowerSolution I x) =
      -lowerRestriction p (penaltyRemainder I x y (lowerSolution I x) lam) +
        (sliceGradient I.f x (lowerSolution I x) - sliceGradient I.f x y) := by
  have hz : sliceGradient I.g x (lowerSolution I x) = 0 := lowerGradient_root hg hμ hsc x
  have hs := congrArg (fun v : p.Y => lam • v) (inner_stationary hf hg x lam y hmin)
  rw [lowerReply_decomposition, smul_add, smul_smul, mul_inv_cancel₀ hlam, one_smul, smul_zero] at hs
  have hgy : lam • sliceGradient I.g x y = -sliceGradient I.f x y := eq_neg_of_add_eq_zero_left hs
  have he : lowerRestriction p (penaltyRemainder I x y (lowerSolution I x) lam) =
      -sliceGradient I.f x y - lowerHessian I (x, lowerSolution I x) (lam • (y - lowerSolution I x)) := by
    simp only [penaltyRemainder, map_sub, map_smul]
    change lam • (sliceGradient I.g x y - sliceGradient I.g x (lowerSolution I x)) -
      lowerHessian I (x, lowerSolution I x) (lam • (y - lowerSolution I x)) = _
    rw [hz, sub_zero, hgy]
    simp only [map_smul, map_sub]
  rw [he]
  abel

lemma penalty_error_pairing {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) (x a : p.X) (y : p.Y) (lam : ℝ) :
    ⟪upperReply p (fderiv ℝ I.f (x, y)) +
        lam • (upperReply p (fderiv ℝ I.g (x, y)) - upperReply p (fderiv ℝ I.g (x, lowerSolution I x))) -
        gradient (hyperObjective I) x, a⟫ =
      (fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, lowerSolution I x)) (a, 0) +
      penaltyRemainder I x y (lowerSolution I x) lam (a, 0) -
      ⟪lowerHessian I (x, lowerSolution I x) (lam • (y - lowerSolution I x)) +
        sliceGradient I.f x (lowerSolution I x), fderiv ℝ (lowerSolution I) x a⟫ := by
  have hc := BilevelImplicit.graph_composite_first hf
    ((lowerSolution_contDiff hg hμ hsc).differentiable (by norm_num)) x a
  change fderiv ℝ (hyperObjective I) x a = _ at hc
  rw [inner_sub_left, inner_add_left, inner_smul_left, inner_sub_left,
    upperReply_inner, upperReply_inner, upperReply_inner, inner_gradient_left, hc]
  simp only [conj_trivial, penaltyRemainder, sub_apply, smul_apply, smul_eq_mul,
    inner_add_left, sliceGradient, lowerRestriction_inner]
  rw [implicit_cross_pairing hg hμ hsc]
  have he : (a, fderiv ℝ (lowerSolution I) x a) =
      (a, (0 : p.Y)) + (0, fderiv ℝ (lowerSolution I) x a) := by simp
  rw [he, map_add]
  ring

lemma exact_penalty_bias {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hg2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam κ : ℝ} (hlam : 0 < lam) (hκ : 1 ≤ κ) (heq : p.μ * κ = p.L)
    (x : p.X) (y : p.Y) (hmin : ∀ u, innerObjective I x lam y ≤ innerObjective I x lam u) :
    ‖upperReply p (fderiv ℝ I.f (x, y)) +
        lam • (upperReply p (fderiv ℝ I.g (x, y)) - upperReply p (fderiv ℝ I.g (x, lowerSolution I x))) -
        gradient (hyperObjective I) x‖ ≤ 4 * p.L * κ ^ 3 / lam := by
  let z := lowerSolution I x
  let E := penaltyRemainder I x y z lam
  let R := lowerHessian I (x, z) (lam • (y - z)) + sliceGradient I.f x z
  have hgd := hg.differentiable (by norm_num)
  have hr : p.L / p.μ = κ := by rw [← heq]; field_simp
  have hdist : lam * ‖y - z‖ ≤ κ := by
    simpa [z, hr] using penalty_displacement hf hgd hμ hf0 hsc hlam x y hmin
  have hdist' : ‖y - z‖ ≤ κ / lam := (le_div_iff₀ hlam).mpr (by nlinarith only [hdist])
  have hE : ‖E‖ ≤ p.L * κ ^ 2 / lam := scaled_remainder_norm hg hL.le hg2 hlam x y z hdist
  have hR : ‖R‖ ≤ p.L * κ ^ 2 / lam + p.L * κ / lam := by
    have hid := penalty_residual_identity hf hgd hμ hsc hlam.ne' x y hmin
    change R = -lowerRestriction p E + (sliceGradient I.f x z - sliceGradient I.f x y) at hid
    rw [hid]
    calc
      _ ≤ ‖lowerRestriction p E‖ + ‖sliceGradient I.f x z - sliceGradient I.f x y‖ := by
        simpa using norm_add_le (-lowerRestriction p E) (sliceGradient I.f x z - sliceGradient I.f x y)
      _ ≤ ‖E‖ + p.L * ‖y - z‖ := by
        apply add_le_add
        · exact ((lowerRestriction p).le_opNorm E).trans (by simpa using mul_le_mul_of_nonneg_right (lowerRestriction_norm p) (norm_nonneg E))
        · simpa only [norm_sub_rev] using sliceGradient_lipschitz hf1 x z y
      _ ≤ p.L * κ ^ 2 / lam + p.L * (κ / lam) := by gcongr
      _ = _ := by ring
  have hn : ‖(InnerProductSpace.toDual ℝ p.X)
      (upperReply p (fderiv ℝ I.f (x, y)) +
        lam • (upperReply p (fderiv ℝ I.g (x, y)) - upperReply p (fderiv ℝ I.g (x, z))) -
        gradient (hyperObjective I) x)‖ ≤ 4 * p.L * κ ^ 3 / lam := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro a ha
    change ‖⟪_, a⟫‖ ≤ _
    rw [penalty_error_pairing hf hg hμ hsc, Real.norm_eq_abs]
    have hY : ‖fderiv ℝ (lowerSolution I) x a‖ ≤ κ := by
      have hh := (lowerSolution_derivative_bounds hg hμ hL.le hsc hg1 x a).1
      rw [ha, mul_one] at hh
      nlinarith
    have hF : |(fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, z)) (a, 0)| ≤ p.L * κ / lam := by
      have hh := (fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, z)).le_opNorm (a, 0)
      have hd := hf1 (x, y) (x, z)
      simp only [Prod.norm_mk, norm_zero, ha, max_eq_left zero_le_one, mul_one, Real.norm_eq_abs] at hh
      have hd' : ‖fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, z)‖ ≤ p.L * ‖y - z‖ := by simpa using hd
      have hb : p.L * ‖y - z‖ ≤ p.L * κ / lam := by
        calc
          _ ≤ p.L * (κ / lam) := mul_le_mul_of_nonneg_left hdist' hL.le
          _ = _ := by ring
      exact hh.trans (hd'.trans hb)
    have hEt : |E (a, 0)| ≤ p.L * κ ^ 2 / lam := by
      have hh := E.le_opNorm (a, 0)
      simpa [ha] using hh.trans (by simpa [ha] using hE)
    have hRt : |⟪R, fderiv ℝ (lowerSolution I) x a⟫| ≤
        (p.L * κ ^ 2 / lam + p.L * κ / lam) * κ := by
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hR hY (norm_nonneg _) (by positivity))
    change |(fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, z)) (a, 0) + E (a, 0) -
      ⟪R, fderiv ℝ (lowerSolution I) x a⟫| ≤ _
    calc
      _ ≤ |(fderiv ℝ I.f (x, y) - fderiv ℝ I.f (x, z)) (a, 0)| + |E (a, 0)| +
          |⟪R, fderiv ℝ (lowerSolution I) x a⟫| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ p.L * κ / lam + p.L * κ ^ 2 / lam + (p.L * κ ^ 2 / lam + p.L * κ / lam) * κ :=
        add_le_add (add_le_add hF hEt) hRt
      _ = p.L * (κ + 2 * κ ^ 2 + κ ^ 3) / lam := by ring
      _ ≤ 4 * p.L * κ ^ 3 / lam := by
        have h1 : κ ≤ κ ^ 3 := by simpa using pow_le_pow_right₀ hκ (show 1 ≤ 3 by omega)
        have h2 : κ ^ 2 ≤ κ ^ 3 := pow_le_pow_right₀ hκ (by omega)
        apply (div_le_div_iff_of_pos_right hlam).mpr
        nlinarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_le_mul_of_nonneg_left h2 hL.le]
  simpa only [LinearIsometryEquiv.norm_map] using hn

lemma upperReply_norm (p : Params) (A : (p.X × p.Y) →L[ℝ] ℝ) : ‖upperReply p A‖ ≤ ‖A‖ := by
  rw [upperReply, LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ p.X p.Y) (norm_nonneg A))

lemma upperReply_lipschitz {p : Params} {f : p.X × p.Y → ℝ}
    (hf1 : ∀ z w, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ p.L * ‖z - w‖)
    (x : p.X) (y z : p.Y) :
    ‖upperReply p (fderiv ℝ f (x, y)) - upperReply p (fderiv ℝ f (x, z))‖ ≤ p.L * ‖y - z‖ := by
  have he : upperReply p (fderiv ℝ f (x, y)) - upperReply p (fderiv ℝ f (x, z)) =
      upperReply p (fderiv ℝ f (x, y) - fderiv ℝ f (x, z)) := by
    simp [upperReply, ContinuousLinearMap.sub_comp]
  rw [he]
  exact (upperReply_norm p _).trans (by simpa using hf1 (x, y) (x, z))

lemma inner_residual_distance {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : Differentiable ℝ I.g)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam : ℝ} (ha : 0 ≤ lam⁻¹) (hb : p.L * lam⁻¹ ≤ p.μ / 2)
    (x : p.X) (ystar y : p.Y)
    (hmin : ∀ u, innerObjective I x lam ystar ≤ innerObjective I x lam u) :
    (p.μ / 2) * ‖y - ystar‖ ≤ ‖lowerReply p lam (firstOrderReply I (x, y))‖ := by
  have hh := support_distance (inner_quadratic_support hf hf1 hsc ha hb x) y ystar
  rw [inner_stationary hf hg x lam ystar hmin, sub_zero] at hh
  exact hh

lemma estimator_perturbation {p : Params} {I : Instance p} (hL : 0 ≤ p.L) (hμ : 0 < p.μ)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    {lam τ : ℝ} (hlam : 1 ≤ lam) (hτ : 0 ≤ τ) (x : p.X) (y z yh zh : p.Y)
    (hy : ‖yh - y‖ ≤ 2 * τ / p.μ) (hz : ‖zh - z‖ ≤ τ / p.μ) :
    ‖(upperReply p (fderiv ℝ I.f (x, yh)) +
        lam • (upperReply p (fderiv ℝ I.g (x, yh)) - upperReply p (fderiv ℝ I.g (x, zh)))) -
      (upperReply p (fderiv ℝ I.f (x, y)) +
        lam • (upperReply p (fderiv ℝ I.g (x, y)) - upperReply p (fderiv ℝ I.g (x, z))))‖ ≤
      5 * lam * p.L * τ / p.μ := by
  let F := fun u => upperReply p (fderiv ℝ I.f (x, u))
  let G := fun u => upperReply p (fderiv ℝ I.g (x, u))
  have hF : ‖F yh - F y‖ ≤ p.L * (2 * τ / p.μ) :=
    (upperReply_lipschitz hf1 x yh y).trans (mul_le_mul_of_nonneg_left hy hL)
  have hGy : ‖G yh - G y‖ ≤ p.L * (2 * τ / p.μ) :=
    (upperReply_lipschitz hg1 x yh y).trans (mul_le_mul_of_nonneg_left hy hL)
  have hGz : ‖G zh - G z‖ ≤ p.L * (τ / p.μ) :=
    (upperReply_lipschitz hg1 x zh z).trans (mul_le_mul_of_nonneg_left hz hL)
  have he : F yh + lam • (G yh - G zh) - (F y + lam • (G y - G z)) =
      (F yh - F y) + lam • ((G yh - G y) - (G zh - G z)) := by module
  change ‖F yh + lam • (G yh - G zh) - (F y + lam • (G y - G z))‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖F yh - F y‖ + ‖lam • ((G yh - G y) - (G zh - G z))‖ := norm_add_le _ _
    _ = ‖F yh - F y‖ + lam * ‖(G yh - G y) - (G zh - G z)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    _ ≤ ‖F yh - F y‖ + lam * (‖G yh - G y‖ + ‖G zh - G z‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ p.L * (2 * τ / p.μ) + lam * (p.L * (2 * τ / p.μ) + p.L * (τ / p.μ)) := by gcongr
    _ ≤ 5 * lam * p.L * τ / p.μ := by
      have hh := mul_le_mul_of_nonneg_right hlam (show 0 ≤ p.L * (2 * τ / p.μ) by positivity)
      calc
        _ ≤ lam * (p.L * (2 * τ / p.μ)) + lam * (p.L * (2 * τ / p.μ) + p.L * (τ / p.μ)) :=
          add_le_add (by simpa only [one_mul] using hh) le_rfl
        _ = _ := by ring

lemma estimate_error_of_residuals {p : Params} {I : Instance p}
    (hf : Differentiable ℝ I.f) (hg : ContDiff ℝ 3 I.g) (hμ : 0 < p.μ) (hL : 0 < p.L)
    (hf0 : ∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L)
    (hf1 : ∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖)
    (hg1 : ∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖)
    (hg2 : ∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖)
    (hsc : ∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z))
    {lam κ τ : ℝ} (hlam : 1 ≤ lam) (hcoef : p.L * lam⁻¹ ≤ p.μ / 2)
    (hκ : 1 ≤ κ) (heq : p.μ * κ = p.L) (hτ : 0 ≤ τ)
    (x : p.X) (ystar yh zh : p.Y)
    (hmin : ∀ u, innerObjective I x lam ystar ≤ innerObjective I x lam u)
    (hy : ‖lowerReply p lam (firstOrderReply I (x, yh))‖ ≤ τ)
    (hz : ‖lowerReply p 0 (firstOrderReply I (x, zh))‖ ≤ τ) :
    ‖upperReply p (fderiv ℝ I.f (x, yh)) +
      lam • (upperReply p (fderiv ℝ I.g (x, yh)) - upperReply p (fderiv ℝ I.g (x, zh))) -
      gradient (hyperObjective I) x‖ ≤ 4 * p.L * κ ^ 3 / lam + 5 * lam * p.L * τ / p.μ := by
  have hlam0 : 0 < lam := by linarith
  have hgd := hg.differentiable (by norm_num)
  have hdy : ‖yh - ystar‖ ≤ 2 * τ / p.μ := by
    have hh := (inner_residual_distance hf hgd hf1 hsc (inv_nonneg.mpr hlam0.le) hcoef x ystar yh hmin).trans hy
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [hh]
  have hdz : ‖zh - lowerSolution I x‖ ≤ τ / p.μ := by
    have hh := base_residual_distance hgd hμ hsc x zh
    have hr : ‖sliceGradient I.g x zh‖ ≤ τ := by simpa [lowerReply_decomposition] using hz
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [hh, hr]
  have hp := estimator_perturbation hL.le hμ hf1 hg1 hlam hτ x ystar (lowerSolution I x) yh zh hdy hdz
  have hb := exact_penalty_bias hf hg hμ hL hf0 hf1 hg1 hg2 hsc hlam0 hκ heq x ystar hmin
  have hh := norm_sub_le_norm_sub_add_norm_sub
    (upperReply p (fderiv ℝ I.f (x, yh)) + lam • (upperReply p (fderiv ℝ I.g (x, yh)) - upperReply p (fderiv ℝ I.g (x, zh))))
    (upperReply p (fderiv ℝ I.f (x, ystar)) + lam • (upperReply p (fderiv ℝ I.g (x, ystar)) - upperReply p (fderiv ℝ I.g (x, lowerSolution I x))))
    (gradient (hyperObjective I) x)
  exact hh.trans (by linarith)

end LongTails.Proofs.BilevelPenalty
