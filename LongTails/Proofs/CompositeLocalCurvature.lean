import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Calculus
import LongTails.Proofs.CurvatureMetric
import LongTails.Proofs.CompositeExtrapolation
import Mathlib.Tactic

namespace LongTails.Proofs.CompositeLocalCurvature

open Set
open scoped RealInnerProductSpace
open LongTails.Proofs.CurvatureMetric

lemma sublevel_chord {f : ℝ → ℝ} (hc : ConvexOn ℝ (Icc 0 1) f)
    {t s : ℝ} (ht : t ∈ Icc 0 1) (hft : f t ≤ f 0) (hs : s ∈ Icc 0 t) :
    f s ≤ f 0 := by
  have h := (hc.convex_le (f 0)).ordConnected.out
    (show 0 ∈ {x ∈ Icc 0 1 | f x ≤ f 0} from ⟨by norm_num, le_rfl⟩)
    (show t ∈ {x ∈ Icc 0 1 | f x ≤ f 0} from ⟨ht, hft⟩) hs
  exact h.2

lemma local_curvature_bootstrap {f f' f'' : ℝ → ℝ} {M : ℝ}
    (hc : ConvexOn ℝ (Icc 0 1) f)
    (hf : ∀ t ∈ Icc 0 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc 0 1, HasDerivAt f' (f'' t) t)
    (hM : 0 ≤ M) (hinit : f' 0 + M < 0)
    (hbound : ∀ t ∈ Icc 0 1, f t ≤ f 0 → ‖f'' t‖ ≤ M) :
    (∀ t ∈ Icc 0 1, f t ≤ f 0) ∧ f' 1 - f' 0 ≤ M := by
  have hgrowth (t : ℝ) (ht : t ∈ Icc 0 1) (hft : f t ≤ f 0) :
      ‖f' t - f' 0‖ ≤ M * t := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := 0) (b := t) (f := f') (f' := f'')
      (fun s hs => (hf' s ⟨hs.1, hs.2.trans ht.2⟩).hasDerivWithinAt)
      (fun s hs => hbound s ⟨hs.1, hs.2.le.trans ht.2⟩
        (sublevel_chord hc ht hft ⟨hs.1, hs.2.le⟩))
      t ⟨ht.1, le_rfl⟩
    simpa using h
  have hall : ∀ t ∈ Icc 0 1, f t ≤ f 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f' := f') (B := fun _ => f 0) (B' := fun _ => 0)
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      le_rfl (fun t => hasDerivAt_const t (f 0))
    intro t ht he
    have hg := hgrowth t ⟨ht.1, ht.2.le⟩ he.le
    have hab : f' t - f' 0 ≤ ‖f' t - f' 0‖ := le_abs_self _
    have hm : M * t ≤ M := by nlinarith [ht.2]
    linarith
  refine ⟨hall, ?_⟩
  have hg := hgrowth 1 (by norm_num) (hall 1 (by norm_num))
  have hab : f' 1 - f' 0 ≤ ‖f' 1 - f' 0‖ := le_abs_self _
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gradient_dual_bound (B : E →L[ℝ] E) (hB : IsUnit B)
    (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {g : ℝ → E} {A : ℝ → E →L[ℝ] E} {d : E} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ t ∈ Icc 0 1, HasDerivAt g (A t d) t)
    (hAs : ∀ t ∈ Icc 0 1, ∀ x y, ⟪x, A t y⟫ = ⟪A t x, y⟫)
    (hAp : ∀ t ∈ Icc 0 1, ∀ x, 0 ≤ ⟪x, A t x⟫)
    (hdom : ∀ t ∈ Icc 0 1, ∀ x, ⟪x, A t x⟫ ≤ L * ⟪x, B x⟫) :
    metricNorm B (Ring.inverse B (g 1 - g 0)) ≤ L * metricNorm B d := by
  let u := Ring.inverse B (g 1 - g 0)
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun t => ⟪u, g t⟫) ⟪u, A t d⟫ t := by
    simpa using (hasDerivAt_const t u).inner ℝ (hg t ht)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := 1) (f := fun t => ⟪u, g t⟫) (f' := fun t => ⟪u, A t d⟫)
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => dominated_cauchy (A t) B (hAs t ⟨ht.1, ht.2.le⟩)
      (hAp t ⟨ht.1, ht.2.le⟩) hp hL (hdom t ⟨ht.1, ht.2.le⟩) u d)
    1 (by norm_num)
  have he : ⟪u, g 1⟫ - ⟪u, g 0⟫ = metricNorm B u ^ 2 := by
    rw [metricNorm_sq B hp, ← inner_sub_right]
    exact congrArg (fun v => ⟪u, v⟫) (inverse_apply B hB (g 1 - g 0)).symm
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  change metricNorm B u ≤ L * metricNorm B d
  by_cases hu : metricNorm B u = 0
  · rw [hu]
    exact mul_nonneg hL (metricNorm_nonneg B d)
  · have hu0 : 0 < metricNorm B u := lt_of_le_of_ne (metricNorm_nonneg B u) (Ne.symm hu)
    apply (mul_le_mul_iff_right₀ hu0).mp
    nlinarith only [h]

lemma initial_prox_certificate {h ψ : E → ℝ} {C : Set E} {g : E → E}
    {A : E → E →L[ℝ] E} {B : E →L[ℝ] E} {x z : E}
    (hc : ConvexOn ℝ univ h) (hψ : ConvexOn ℝ C ψ) (hx : x ∈ C) (hz : z ∈ C)
    (hh : ∀ w, HasFDerivAt h (innerSL ℝ (g w)) w)
    (hg : ∀ w, HasFDerivAt g (A w) w)
    (hpos : ∀ w d, 0 ≤ ⟪d, A w d⟫)
    (hbound : ∀ w ∈ C, h w + ψ w ≤ h x + ψ x →
      ∀ d, ⟪d, A w d⟫ ≤ ⟪d, B d⟫ / 8)
    (he : 0 < ⟪z - x, B (z - x)⟫)
    (hprox : ⟪g x, z - x⟫ + ⟪z - x, B (z - x)⟫ + ψ z - ψ x ≤ 0) :
    h z + ψ z ≤ h x + ψ x ∧
      ⟪g z - g x, z - x⟫ ≤ ⟪z - x, B (z - x)⟫ / 8 := by
  let d := z - x
  let U : ℝ → ℝ := fun t => h (x + t • d) + ψ x + t * (ψ z - ψ x)
  let V : ℝ → ℝ := fun t => ⟪g (x + t • d), d⟫ + (ψ z - ψ x)
  let W : ℝ → ℝ := fun t => ⟪d, A (x + t • d) d⟫
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hd (t : ℝ) : HasDerivAt U (V t) t := by
    have h₁ := (hh (x + t • d)).comp_hasDerivAt t (hline t)
    have h₂ := (h₁.add_const (ψ x)).add ((hasDerivAt_id t).mul_const (ψ z - ψ x))
    convert h₂ using 1
    · ext t
      rfl
    · simp [V]
  have hd' (t : ℝ) : HasDerivAt V (W t) t := by
    have h₁ := (hg (x + t • d)).comp_hasDerivAt t (hline t)
    have h₂ := (h₁.inner ℝ (hasDerivAt_const t d)).add_const (ψ z - ψ x)
    convert h₂ using 1 <;> simp [V, W, real_inner_comm]
  have hcv : ConvexOn ℝ (Icc 0 1) U := by
    have h₀ := hc.comp_affineMap (AffineMap.lineMap x z)
    have h₁ := (convexOn_id (convex_univ : Convex ℝ (univ : Set ℝ))).comp_affineMap
      (AffineMap.lineMap (ψ x) (ψ z))
    simp only [preimage_univ] at h₀ h₁
    have h₂ := h₀.add h₁
    have hu : U = (h ∘ AffineMap.lineMap x z) + (id ∘ AffineMap.lineMap (ψ x) (ψ z)) := by
      ext t
      simp [U, d, AffineMap.lineMap_apply_module', add_comm]
      ring
    rw [hu]
    exact h₂.subset (subset_univ _) (convex_Icc 0 1)
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) (hu : U t ≤ U 0) :
      ‖W t‖ ≤ ⟪d, B d⟫ / 8 := by
    have hmem : x + t • d ∈ C := by
      have heq : x + t • d = (1 - t) • x + t • z := by dsimp [d]; module
      rw [heq]
      exact hψ.1 hx hz (by linarith [ht.2]) ht.1 (by ring)
    have hp := CompositeExtrapolation.segment_upper hψ hx hz ht.1 ht.2
    have hsub : h (x + t • d) + ψ (x + t • d) ≤ h x + ψ x := by
      simpa [U, d] using (show h (x + t • d) + ψ (x + t • d) ≤ U 0 by
        have hp' : ψ (x + t • d) ≤ ψ x + t * (ψ z - ψ x) := by
          dsimp [d]
          linarith
        dsimp [U] at hu ⊢
        linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos (x + t • d) d)]
    exact hbound _ hmem hsub d
  have hinit : V 0 + ⟪d, B d⟫ / 8 < 0 := by
    simp only [V, zero_smul, add_zero]
    dsimp [d]
    linarith
  have hr := local_curvature_bootstrap hcv (fun t _ => hd t) (fun t _ => hd' t)
    (by dsimp [d]; positivity) hinit hb
  have hlow := hr.1 1 (by norm_num)
  have hcert := hr.2
  constructor
  · simpa [U, d] using hlow
  · simpa [V, d, inner_sub_left] using hcert

lemma dual_gradient_on_tube (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {g : E → E} {A : E → E →L[ℝ] E} {x y z : E} {R L : ℝ}
    (hL : 0 ≤ L) (hg : ∀ w, HasFDerivAt g (A w) w)
    (hAs : ∀ w, ∀ u v, ⟪u, A w v⟫ = ⟪A w u, v⟫)
    (hAp : ∀ w u, 0 ≤ ⟪u, A w u⟫)
    (hdom : ∀ w, metricNorm B (w - z) ≤ R → ∀ u, ⟪u, A w u⟫ ≤ L * ⟪u, B u⟫)
    (hx : metricNorm B (x - z) ≤ R) (hy : metricNorm B (y - z) ≤ R) :
    metricNorm B (Ring.inverse B (g y - g x)) ≤ L * metricNorm B (y - x) := by
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have h := gradient_dual_bound B hB hp hL
    (g := fun t => g (x + t • (y - x))) (A := fun t => A (x + t • (y - x)))
    (fun t _ => (hg _).comp_hasDerivAt t (hline t))
    (fun t _ => hAs _) (fun t _ => hAp _)
    (fun t ht => hdom _ (metric_segment_bound B hs hp ht.1 ht.2 hx hy))
  simpa using h

lemma certificate_on_tube (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {g : E → E} {A : E → E →L[ℝ] E} {x y z : E} {R L : ℝ}
    (hL : 0 ≤ L) (hg : ∀ w, HasFDerivAt g (A w) w)
    (hAs : ∀ w, ∀ u v, ⟪u, A w v⟫ = ⟪A w u, v⟫)
    (hAp : ∀ w u, 0 ≤ ⟪u, A w u⟫)
    (hdom : ∀ w, metricNorm B (w - z) ≤ R → ∀ u, ⟪u, A w u⟫ ≤ L * ⟪u, B u⟫)
    (hx : metricNorm B (x - z) ≤ R) (hy : metricNorm B (y - z) ≤ R) :
    ⟪g y - g x, y - x⟫ ≤ L * metricNorm B (y - x) ^ 2 := by
  have hd := dual_gradient_on_tube B hB hs hp hL hg hAs hAp hdom hx hy
  have hc := (abs_le.mp (dual_cauchy B hB hs hp (g y - g x) (y - x))).2
  have hm := mul_le_mul_of_nonneg_right hd (metricNorm_nonneg B (y - x))
  nlinarith only [hc, hm]

lemma certified_trial_distance (B : E →L[ℝ] E) {x v z r : E} {s Δ Fx Fz : ℝ}
    (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) (hz : 0 ≤ Fz) (hx : Fx ≤ 2 * Δ)
    (hq : ⟪r, v - x⟫ ≤ 0)
    (hcert : Fz - Fx ≤ ⟪r, x + s • (v - x) - x⟫ -
      metricNorm B (x + s • (v - x) - z) ^ 2 / 2) :
    metricNorm B (x + s • (v - x) - z) ≤ 2 * Real.sqrt Δ := by
  have he : ⟪r, x + s • (v - x) - x⟫ = s * ⟪r, v - x⟫ := by
    simp only [add_sub_cancel_left, inner_smul_right]
  rw [he] at hcert
  have hn := mul_nonpos_of_nonneg_of_nonpos hs hq
  have hsq := Real.sq_sqrt hΔ
  have hp := metricNorm_nonneg B (x + s • (v - x) - z)
  have hroot := Real.sqrt_nonneg Δ
  nlinarith only [hcert, hn, hz, hx, hsq, hp, hroot]

lemma certified_neighbor (B : E →L[ℝ] E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {g : E → E} {A : E → E →L[ℝ] E} {ψ : E → ℝ}
    {yl yu zl zu : E} {R : ℝ} (hR : 0 ≤ R)
    (hg : ∀ w, HasFDerivAt g (A w) w)
    (hAs : ∀ w, ∀ u v, ⟪u, A w v⟫ = ⟪A w u, v⟫)
    (hAp : ∀ w u, 0 ≤ ⟪u, A w u⟫)
    (hdom : ∀ w, metricNorm B (w - zl) ≤ 4 * R →
      ∀ u, ⟪u, A w u⟫ ≤ (1 / 4 : ℝ) * ⟪u, B u⟫)
    (hlow : metricNorm B (yl - zl) ≤ 2 * R)
    (hnear : metricNorm B (yu - yl) ≤ R / 2)
    (hpu : ψ zu ≤ ψ zl + ⟪g yu + B (zu - yu), zl - zu⟫)
    (hpl : ψ zl ≤ ψ zu + ⟪g yl + B (zl - yl), zu - zl⟫) :
    ⟪g zu - g yu, zu - yu⟫ ≤ metricNorm B (zu - yu) ^ 2 / 4 ∧
      metricNorm B (Ring.inverse B (B (yu - zu) - B (yl - zl))) ≤
        (9 / 4 : ℝ) * metricNorm B (yu - yl) := by
  have hyl : metricNorm B (yl - zl) ≤ 4 * R := by linarith
  have hyu : metricNorm B (yu - zl) ≤ 4 * R := by
    have ht := metricNorm_add_le B hs hp (yu - yl) (yl - zl)
    have he : yu - yl + (yl - zl) = yu - zl := by abel
    rw [he] at ht
    linarith
  have hgrad := dual_gradient_on_tube B hB hs hp (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hg hAs hAp hdom hyl hyu
  have hz := proximal_gradient_stability B hB hs hp hpu hpl hgrad
  have hzu : metricNorm B (zu - zl) ≤ 4 * R := by linarith
  have hc := certificate_on_tube B hB hs hp (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hg hAs hAp hdom hyu hzu
  have hr := residual_stability B hB hs hp hz
  constructor <;> linarith

end LongTails.Proofs.CompositeLocalCurvature
