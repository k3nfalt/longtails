import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

open Set InnerProductSpace
open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_quadratic (μ : ℝ) (x : E) :
    HasGradientAt (fun v : E => μ / 2 * ‖v‖ ^ 2) (μ • x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2)
  change HasFDerivAt (fun v : E => μ / 2 * ‖v‖ ^ 2) ((toDual ℝ E) (μ • x)) x
  convert h using 1
  ext v
  simp only [toDual_apply_apply, real_inner_smul_left, smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

lemma gradient_neg_within {C : Set E} {f : E → ℝ} {g x : E}
    (hg : HasGradientWithinAt f g C x) :
    HasGradientWithinAt (fun v => -f v) (-g) C x := by
  change HasFDerivWithinAt _ ((toDual ℝ E) (-g)) C x
  convert hg.hasFDerivWithinAt.neg using 1; simp [map_neg]

lemma gradient_add_within {C : Set E} {f h : E → ℝ} {g q x : E}
    (hf : HasGradientWithinAt f g C x) (hh : HasGradientWithinAt h q C x) :
    HasGradientWithinAt (fun v => f v + h v) (g + q) C x := by
  change HasFDerivWithinAt _ ((toDual ℝ E) (g + q)) C x
  convert hf.hasFDerivWithinAt.add hh.hasFDerivWithinAt using 1; simp [map_add]

lemma gradient_comp_affine_within {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [CompleteSpace D] {C : Set D} {S : Set E}
    {f : D → ℝ} {g b : D} {x q : E} (T : E →L[ℝ] D)
    (hg : HasGradientWithinAt f g C (T x + b))
    (hmap : ∀ v ∈ S, T v + b ∈ C)
    (hip : ∀ v, ⟪g, T v⟫ = ⟪q, v⟫) :
    HasGradientWithinAt (fun v => f (T v + b)) q S x := by
  have h := hg.hasFDerivWithinAt.comp x
    (T.hasFDerivAt.add_const b).hasFDerivWithinAt hmap
  change HasFDerivWithinAt _ ((toDual ℝ E) q) S x
  convert h using 1
  · rfl
  · ext v
    simpa only [ContinuousLinearMap.comp_apply, toDual_apply_apply] using (hip v).symm

lemma convex_support_within {C : Set E} {f : E → ℝ} {g x y : E}
    (hc : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C)
    (hg : HasGradientWithinAt f g C x) :
    ⟪g, y - x⟫ ≤ f y - f x := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivWithinAt f ((toDual ℝ E) g) C
      ((AffineMap.lineMap x y) (0 : ℝ)) := by
    simpa using hg.hasFDerivWithinAt
  have hline : HasDerivWithinAt (f ∘ AffineMap.lineMap x y) ⟪g, y - x⟫
      ((AffineMap.lineMap x y) ⁻¹' C) (0 : ℝ) := by
    convert hd.comp_hasDerivWithinAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ))).hasDerivWithinAt
      (fun _ ht => ht) using 1 <;> rfl
  have h := hconv.le_slope_of_hasDerivWithinAt (x := 0) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hline
  simpa [slope_def_field] using h

lemma strong_support_within {C : Set E} {f : E → ℝ} {g x y : E} {μ : ℝ}
    (hc : StrongConvexOn C μ f) (hx : x ∈ C) (hy : y ∈ C)
    (hg : HasGradientWithinAt f g C x) :
    f x + ⟪g, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hgrad : HasGradientWithinAt (fun v => f v - μ / 2 * ‖v‖ ^ 2)
      (g - μ • x) C x := by
    have h := hg.hasFDerivWithinAt.sub (gradient_quadratic μ x).hasFDerivAt.hasFDerivWithinAt
    change HasFDerivWithinAt _ ((toDual ℝ E) (g - μ • x)) C x
    convert h using 1; simp [map_sub]
  have h := convex_support_within (strongConvexOn_iff_convex.mp hc) hx hy hgrad
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right] at h
  rw [norm_sub_sq_real]
  have heq : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  rw [heq]
  rw [real_inner_self_eq_norm_sq] at h
  simp only [inner_sub_right]
  nlinarith


omit [CompleteSpace E] in
lemma strong_convex_add_quadratic {C : Set E} {f : E → ℝ} {μ β k : ℝ}
    (hf : StrongConvexOn C μ f) (center : E) :
    StrongConvexOn C (μ + β) (fun x => f x + β / 2 * ‖x - center‖ ^ 2 + k) := by
  rw [strongConvexOn_iff_convex] at hf ⊢
  have hg : ConvexOn ℝ C (fun x => -β * ⟪x, center⟫ + β / 2 * ‖center‖ ^ 2 + k) := by
    refine ⟨hf.1, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    obtain rfl := eq_sub_of_add_eq hab
    exact le_of_eq (by ring)
  have he : (fun x => f x + β / 2 * ‖x - center‖ ^ 2 + k - (μ + β) / 2 * ‖x‖ ^ 2) =
      (fun x => (f x - μ / 2 * ‖x‖ ^ 2) + (-β * ⟪x, center⟫ + β / 2 * ‖center‖ ^ 2 + k)) := by
    funext x
    rw [norm_sub_sq_real]
    ring
  rw [he]
  exact hf.add hg

lemma gradient_translated_quadratic (β : ℝ) (center x : E) (C : Set E) :
    HasGradientWithinAt (fun u => β / 2 * ‖u - center‖ ^ 2) (β • (x - center)) C x := by
  have h := gradient_comp_affine_within (ContinuousLinearMap.id ℝ E)
    (f := fun u => β / 2 * ‖u‖ ^ 2) (b := -center) (S := C) (C := Set.univ)
    (x := x) (q := β • (x - center))
    (by simpa only [ContinuousLinearMap.id_apply, sub_eq_add_neg] using
      (hasGradientWithinAt_univ.mpr (gradient_quadratic β (x - center))))
    (fun _ _ => Set.mem_univ _)
    (by intro v; simp only [ContinuousLinearMap.id_apply, sub_eq_add_neg])
  simpa only [ContinuousLinearMap.id_apply, sub_eq_add_neg] using h

lemma minimizer_gradient_normal {C : Set E} {f : E → ℝ} {g x : E}
    (hc : Convex ℝ C) (hx : x ∈ C) (hmin : ∀ y ∈ C, f x ≤ f y)
    (hg : HasGradientWithinAt f g C x) : ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫ := by
  intro y hy
  have hm : IsMinOn f C x := hmin
  exact hm.isLocalMinOn.hasFDerivWithinAt_nonneg hg.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hc.segment_subset hx hy))

lemma smooth_upper_within {C : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hc : Convex ℝ C) (hg : ∀ x ∈ C, HasGradientWithinAt f (g x) C x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => ⟪g (x + t • d), d⟫
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ C := by
    intro t ht
    convert hc hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring) using 1
    dsimp [d]
    module
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt F (F' t) (Icc 0 1) t := by
    intro t ht
    have h := (hg _ (hmem t ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
      (((hasDerivAt_id t).smul_const d).const_add x).hasDerivWithinAt hmem
    convert h using 1 <;> simp [F, F', Function.comp_def]
  let B := fun t : ℝ => f x + t * ⟪g x, d⟫ + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪g x, d⟫ + L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪g x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ ⟪g x, d⟫ + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := (real_inner_le_norm (g (x + t • d) - g x) d).trans
      (mul_le_mul_of_nonneg_right (hlip _ (hmem t ⟨ht.1, ht.2.le⟩) _ hx) (norm_nonneg d))
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_sub_left] at h
    dsimp [F']
    nlinarith
  have hright : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    apply (hF t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
      (fun s hs => ⟨ht.1.trans hs.1, hs.2⟩)
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t ht => (hF t ht).continuousWithinAt) hright
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

end OracleTemplate.NearZeroSum
