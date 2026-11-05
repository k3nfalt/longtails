import LongTails.Algorithms.SymmetricThirdOrder
import LongTails.Proofs.ThirdOrderBregmanGeometry
import LongTails.Proofs.GuardedMetricSupport
import LongTails.Proofs.QuarticBregmanKernel
import LongTails.Proofs.HiddenDecompositionEnergy

namespace LongTails.Proofs.SymmetricThirdOrderGeometry

open LongTails.Algorithms.SymmetricThirdOrder
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma kernel_hasGradientAt (B : E →L[ℝ] E) (L δ : ℝ) (s : E)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    HasGradientAt (kernel B L δ) (kernelGradient B L δ s) s := by
  have hfour : HasFDerivAt (fun x : E => ‖x‖ ^ 4)
      ((4 * ‖s‖ ^ 2) • innerSL ℝ s) s := by
    convert hasFDerivAt_norm_rpow s (by norm_num : (1 : ℝ) < 4) using 1 <;> norm_num
  have hquad := ((hasFDerivAt_id s).inner ℝ B.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hnorm := (hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul (δ / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hquad.add (hfour.const_mul (2 * L))).add hnorm using 1
  · rfl
  · ext y
    simp [kernelGradient]
    rw [hB s y, real_inner_comm y (B s)]
    ring

lemma model_hasGradientAt {f : E → ℝ} (hf : Differentiable ℝ f)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ) (s : E)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    HasGradientAt (model f c B L δ) (modelGradient (gradient f) c B L δ s) s := by
  have hplus := (hf (c + s)).hasGradientAt.hasFDerivAt.comp s ((hasFDerivAt_id s).const_add c)
  have hminus := (hf (c - s)).hasGradientAt.hasFDerivAt.comp s ((hasFDerivAt_id s).const_sub c)
  have hk := (kernel_hasGradientAt B L δ s hB).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hplus.sub hminus).const_mul (1 / 2 : ℝ)).add hk using 1
  · rfl
  · ext y
    simp [modelGradient]

omit [FiniteDimensional ℝ E] in
lemma kernelGradient_hasFDerivAt (B : E →L[ℝ] E) (L δ : ℝ) (s : E) :
    HasFDerivAt (kernelGradient B L δ) (kernelHessian B L δ s) s := by
  have hc := ((hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul (8 * L)).add_const δ
  convert B.hasFDerivAt.add (hc.smul (hasFDerivAt_id s)) using 1
  · rfl
  · ext v
    simp [kernelHessian]
    module

omit [FiniteDimensional ℝ E] in
lemma modelGradient_hasFDerivAt {g : E → E} (hg : Differentiable ℝ g)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ) (s : E) :
    HasFDerivAt (modelGradient g c B L δ)
      (modelHessian (fderiv ℝ g) c B L δ s) s := by
  have hp := (hg (c + s)).hasFDerivAt.comp s ((hasFDerivAt_id s).const_add c)
  have hm := (hg (c - s)).hasFDerivAt.comp s ((hasFDerivAt_id s).const_sub c)
  convert ((hp.add hm).const_smul (1 / 2 : ℝ)).add
    (kernelGradient_hasFDerivAt B L δ s) using 1
  · rfl
  · ext v
    simp [modelHessian, sub_eq_add_neg]

omit [FiniteDimensional ℝ E] in
lemma kernelHessian_form (B : E →L[ℝ] E) (L δ : ℝ) (s v : E) :
    ⟪kernelHessian B L δ s v, v⟫ = ⟪B v, v⟫ +
      (8 * L * ‖s‖ ^ 2 + δ) * ‖v‖ ^ 2 + 16 * L * ⟪s, v⟫ ^ 2 := by
  change ⟪B v + (8 * L * ‖s‖ ^ 2 + δ) • v + (16 * L) • (⟪s, v⟫ • s), v⟫ = _
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

lemma modelHessian_relative {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫) (s v : E) :
    (1 / 2) * ⟪kernelHessian B L δ s v, v⟫ ≤
      ⟪modelHessian (fderiv ℝ (gradient f)) c B L δ s v, v⟫ ∧
    ⟪modelHessian (fderiv ℝ (gradient f)) c B L δ s v, v⟫ ≤
      (3 / 2) * ⟪kernelHessian B L δ s v, v⟫ := by
  have hp := abs_le.mp (ThirdOrderBregmanGeometry.hessian_form_remainder hf hL hT c s v)
  have hm := abs_le.mp (ThirdOrderBregmanGeometry.hessian_form_remainder hf hL hT c (-s) v)
  have ht := abs_le.mp (ThirdOrderBregmanGeometry.third_mixed_convex_bound hf hc hL hT c s v)
  have hb := hB v
  simp only [map_neg, neg_apply, inner_neg_left, norm_neg, ← sub_eq_add_neg] at hm
  simp only [modelHessian, add_apply, smul_apply, sub_apply, inner_add_left,
    real_inner_smul_left, inner_sub_left, kernelHessian_form]
  have hn₁ := mul_nonneg hL (mul_nonneg (sq_nonneg ‖s‖) (sq_nonneg ‖v‖))
  have hn₂ := mul_nonneg hL (sq_nonneg ⟪s, v⟫)
  have hn₃ := mul_nonneg hδ (sq_nonneg ‖v‖)
  constructor <;> nlinarith

lemma support_from_hessian {f : E → ℝ} {g : E → E} {H : E → E →L[ℝ] E}
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, 0 ≤ ⟪H x v, v⟫) (x y : E) :
    f x + ⟪g x, y - x⟫ ≤ f y := by
  let path := fun t : ℝ => x + t • (y - x)
  have hp (t : ℝ) : HasDerivAt path (y - x) t := by
    convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (y - x)) using 1
    · rfl
    · simp
  have hd (t : ℝ) : HasDerivAt (fun r => f (path r)) ⟪g (path t), y - x⟫ t := by
    simpa only [Function.comp_def, innerSL_apply_apply, InnerProductSpace.toDual_apply_apply] using
      (hf (path t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hd' (t : ℝ) : HasDerivAt (fun r => ⟪g (path r), y - x⟫)
      ⟪H (path t) (y - x), y - x⟫ t := by
    simpa using HasDerivAt.inner ℝ ((hg (path t)).comp_hasDerivAt t (hp t))
      (hasDerivAt_const t (y - x))
  have hh := GuardedMetricSupport.scalar_support hd hd' (m := 0) (fun t _ => hH (path t) (y - x))
  simpa [path] using hh

lemma relative_support {q ρ : E → ℝ} {g k : E → E} {H K : E → E →L[ℝ] E}
    (hq : ∀ x, HasGradientAt q (g x) x) (hρ : ∀ x, HasGradientAt ρ (k x) x)
    (hg : ∀ x, HasFDerivAt g (H x) x) (hk : ∀ x, HasFDerivAt k (K x) x)
    (α : ℝ) (hHK : ∀ x v, α * ⟪K x v, v⟫ ≤ ⟪H x v, v⟫) (x y : E) :
    q x + ⟪g x, y - x⟫ + α * (ρ y - ρ x - ⟪k x, y - x⟫) ≤ q y := by
  have hdiff (z : E) : HasGradientAt (fun w => q w - α * ρ w) (g z - α • k z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hq z).hasFDerivAt.sub ((hρ z).hasFDerivAt.const_mul α) using 1
    ext v
    simp
  have hder (z : E) : HasFDerivAt (fun w => g w - α • k w) (H z - α • K z) z :=
    (hg z).sub ((hk z).const_smul α)
  have hh := support_from_hessian hdiff hder (fun z v => by
    simpa only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left, sub_nonneg]
      using hHK z v) x y
  simp only [inner_sub_left, real_inner_smul_left] at hh
  linarith

omit [FiniteDimensional ℝ E] in
lemma kernel_contDiff (B : E →L[ℝ] E) (L δ : ℝ) : ContDiff ℝ 3 (kernel B L δ) := by
  have hfour : ContDiff ℝ 3 (fun x : E => ‖x‖ ^ 4) := by
    convert (contDiff_norm_sq ℝ (E := E) (n := 3)).pow 2 using 1
    funext x
    ring
  have hquad : ContDiff ℝ 3 (fun x : E => ⟪x, B x⟫) := contDiff_id.inner ℝ B.contDiff
  exact ((contDiff_const.mul hquad).add (contDiff_const.mul hfour)).add
    (contDiff_const.mul (contDiff_norm_sq ℝ))

omit [FiniteDimensional ℝ E] in
lemma model_contDiff {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ) : ContDiff ℝ 3 (model f c B L δ) := by
  have hp : ContDiff ℝ 3 (fun s => f (c + s)) := hf.comp (contDiff_const.add contDiff_id)
  have hm : ContDiff ℝ 3 (fun s => f (c - s)) := hf.comp (contDiff_const.sub contDiff_id)
  exact (contDiff_const.mul (hp.sub hm)).add (kernel_contDiff B L δ)

lemma kernel_gradient (B : E →L[ℝ] E) (L δ : ℝ)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    gradient (kernel B L δ) = kernelGradient B L δ := by
  funext s
  exact (kernel_hasGradientAt B L δ s hB).gradient

lemma model_gradient {f : E → ℝ} (hf : Differentiable ℝ f)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    gradient (model f c B L δ) = modelGradient (gradient f) c B L δ := by
  funext s
  exact (model_hasGradientAt hf c B L δ s hB).gradient

lemma model_relative_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫) (x y : E) :
    (1 / 2) * ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) (y - x) x ≤
      ThirdOrderBregmanGeometry.translatedGap (model f c B L δ) (y - x) x ∧
    ThirdOrderBregmanGeometry.translatedGap (model f c B L δ) (y - x) x ≤
      (3 / 2) * ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) (y - x) x := by
  have hd := hf.differentiable (by norm_num)
  have hg := (GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)
  have hlo := relative_support (model_hasGradientAt hd c B L δ · hsym)
    (kernel_hasGradientAt B L δ · hsym) (modelGradient_hasFDerivAt hg c B L δ)
    (kernelGradient_hasFDerivAt B L δ) (1 / 2)
    (fun s v => (modelHessian_relative hf hc hL hδ hT c B hB s v).1) x y
  have hhi := relative_support (kernel_hasGradientAt B L δ · hsym)
    (model_hasGradientAt hd c B L δ · hsym) (kernelGradient_hasFDerivAt B L δ)
    (modelGradient_hasFDerivAt hg c B L δ) (2 / 3)
    (fun s v => by have hh := (modelHessian_relative hf hc hL hδ hT c B hB s v).2; linarith) x y
  simp only [ThirdOrderBregmanGeometry.translatedGap, add_sub_cancel,
    kernel_gradient B L δ hsym, model_gradient hd c B L δ hsym]
  constructor <;> linarith

lemma kernel_gap_identity (B : E →L[ℝ] E) (L δ : ℝ)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (x s : E) :
    ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) s x =
      (1 / 2) * ⟪s, B s⟫ + 2 * L *
        (‖x + s‖ ^ 4 - ‖x‖ ^ 4 - 4 * ‖x‖ ^ 2 * ⟪x, s⟫) + δ / 2 * ‖s‖ ^ 2 := by
  rw [ThirdOrderBregmanGeometry.translatedGap, kernel_gradient B L δ hB]
  simp only [kernel, kernelGradient, map_add, inner_add_left, inner_add_right,
    real_inner_smul_left, norm_add_sq_real]
  rw [hB x s, real_inner_comm s (B x)]
  ring

lemma kernel_gap_lower (B : E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, 0 ≤ ⟪v, B v⟫) (x s : E) :
    δ / 2 * ‖s‖ ^ 2 + (2 / 3) * L * ‖s‖ ^ 4 ≤
      ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) s x := by
  rw [kernel_gap_identity B L δ hsym]
  have hq := mul_le_mul_of_nonneg_left (QuarticBregmanKernel.quartic_support x s) hL
  have hb := hB s
  nlinarith

lemma kernel_gap_reverse (B : E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, 0 ≤ ⟪v, B v⟫) (x s : E) :
    ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) (-s) (x + s) ≤
      4 * ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) s x := by
  rw [kernel_gap_identity B L δ hsym, kernel_gap_identity B L δ hsym]
  simp only [add_neg_cancel_right, map_neg, inner_neg_left, inner_neg_right, neg_neg, norm_neg]
  have hq := mul_le_mul_of_nonneg_left (QuarticBregmanKernel.quartic_reverse x s) hL
  have hb := hB s
  have hd := mul_nonneg hδ (sq_nonneg ‖s‖)
  nlinarith

lemma model_strong_support {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫) (x y : E) :
    model f c B L δ x + ⟪gradient (model f c B L δ) x, y - x⟫ +
      δ / 4 * ‖y - x‖ ^ 2 ≤ model f c B L δ y := by
  have hpos (v : E) : 0 ≤ ⟪v, B v⟫ := by
    rw [real_inner_comm]
    exact (ThirdOrderBregmanGeometry.convex_hessian_nonneg hf hc c v).trans (hB v)
  have hq := (model_relative_gap hf hc hL hδ hT c B hsym hB x y).1
  have hk := kernel_gap_lower B (δ := δ) hL hsym hpos x (y - x)
  have hn := mul_nonneg hL (pow_nonneg (norm_nonneg (y - x)) 4)
  simp only [ThirdOrderBregmanGeometry.translatedGap, add_sub_cancel] at hq hk
  nlinarith

lemma model_convex {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫) :
    ConvexOn ℝ Set.univ (model f c B L δ) := by
  apply OracleTemplate.HiddenDecompositionEnergy.convex_of_gradient_support
    (G := gradient (model f c B L δ))
  intro x y
  have hh := model_strong_support hf hc hL hδ hT c B hsym hB x y
  have hn := mul_nonneg hδ (sq_nonneg ‖y - x‖)
  linarith

lemma symmetric_value_error {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (c s : E) :
    |(1 / 2) * (f (c + s) - f (c - s)) +
      (1 / 2) * ⟪fderiv ℝ (gradient f) c s, s⟫ - (f (c + s) - f c)| ≤ L * ‖s‖ ^ 4 := by
  have hp := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT c s 1
  have hm := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT c s (-1)
  norm_num only [one_smul, neg_one_smul, one_pow, abs_one, abs_neg,
    mul_one, mul_neg, neg_mul, ← sub_eq_add_neg] at hp hm
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  obtain ⟨hm₁, hm₂⟩ := abs_le.mp hm
  apply abs_le.mpr
  constructor <;> linarith

lemma model_value_bounds {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L δ : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c s : E) (B : E →L[ℝ] E) :
    f (c + s) - f c + (1 / 2) * (⟪B s, s⟫ - ⟪fderiv ℝ (gradient f) c s, s⟫) +
      L * ‖s‖ ^ 4 + δ / 2 * ‖s‖ ^ 2 ≤ model f c B L δ s ∧
    model f c B L δ s ≤ f (c + s) - f c +
      (1 / 2) * (⟪B s, s⟫ - ⟪fderiv ℝ (gradient f) c s, s⟫) +
      3 * L * ‖s‖ ^ 4 + δ / 2 * ‖s‖ ^ 2 := by
  have hh := abs_le.mp (symmetric_value_error hf hL hT c s)
  simp only [model, kernel]
  rw [real_inner_comm s (B s)]
  constructor <;> linarith

lemma model_initial_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L δ β R Δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hβ : 0 ≤ β)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c x₀ xstar s : E) (B : E →L[ℝ] E)
    (hB : ∀ v, 0 ≤ ⟪B v, v⟫ - ⟪fderiv ℝ (gradient f) c v, v⟫)
    (hBupper : ∀ v, ⟪B v, v⟫ - ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ β * ‖v‖ ^ 2)
    (hmin : ∀ x, f xstar ≤ f x) (hgap : f x₀ - f xstar ≤ Δ)
    (hdist : ‖x₀ - c‖ ≤ R) :
    model f c B L δ (x₀ - c) - model f c B L δ s ≤
      Δ + 3 * L * R ^ 4 + (β + δ) / 2 * R ^ 2 := by
  have hu := (model_value_bounds hf (δ := δ) hL hT c (x₀ - c) B).2
  have hl := (model_value_bounds hf (δ := δ) hL hT c s B).1
  have hb := hB s
  have hbu := hBupper (x₀ - c)
  have hm := hmin (c + s)
  have hn₄ := mul_nonneg hL (pow_nonneg (norm_nonneg s) 4)
  have hn₂ := mul_nonneg hδ (sq_nonneg ‖s‖)
  have hp₂ : ‖x₀ - c‖ ^ 2 ≤ R ^ 2 := by gcongr
  have hp₄ : ‖x₀ - c‖ ^ 4 ≤ R ^ 4 := by gcongr
  have hm₄ := mul_le_mul_of_nonneg_left hp₄ hL
  have hm₂ := mul_le_mul_of_nonneg_left hp₂ (add_nonneg hβ hδ)
  have he : c + (x₀ - c) = x₀ := by abel
  rw [he] at hu
  nlinarith

lemma symmetric_hessian_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (c s : E) :
    ‖(1 / 2 : ℝ) • (fderiv ℝ (gradient f) (c + s) + fderiv ℝ (gradient f) (c - s)) -
      fderiv ℝ (gradient f) c‖ ≤ L * ‖s‖ ^ 2 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H c
  have hp : ‖H (c + s) - H c - T s‖ ≤ L * ‖s‖ ^ 2 := by
    simpa only [add_sub_cancel_left] using ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT c (c + s)
  have hm : ‖H (c - s) - H c + T s‖ ≤ L * ‖s‖ ^ 2 := by
    have he : c - s - c = -s := by abel
    simpa only [he, map_neg, sub_neg_eq_add, norm_neg] using
      ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL hT c (c - s)
  have he : (1 / 2 : ℝ) • (H (c + s) + H (c - s)) - H c =
      (1 / 2 : ℝ) • ((H (c + s) - H c - T s) + (H (c - s) - H c + T s)) := by module
  change ‖(1 / 2 : ℝ) • (H (c + s) + H (c - s)) - H c‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(1 / 2 : ℝ)‖ * ‖(H (c + s) - H c - T s) + (H (c - s) - H c + T s)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (1 / 2 : ℝ) * (‖H (c + s) - H c - T s‖ + ‖H (c - s) - H c + T s‖) := by
      have ht := ContinuousLinearMap.opNorm_add_le (H (c + s) - H c - T s) (H (c - s) - H c + T s)
      have hehalf : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hehalf]
      linarith
    _ ≤ L * ‖s‖ ^ 2 := by linarith

lemma symmetric_gradient_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (c s : E) :
    ‖(1 / 2 : ℝ) • (gradient f (c + s) - gradient f (c - s)) -
      fderiv ℝ (gradient f) c s‖ ≤ L * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f)
  let F := fun v => (1 / 2 : ℝ) • (gradient f (c + v) - gradient f (c - v)) - H c v
  let D := fun v => (1 / 2 : ℝ) • (H (c + v) + H (c - v)) - H c
  have hg := (GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)
  have hd (v : E) : HasFDerivAt F (D v) v := by
    have hp := (hg (c + v)).hasFDerivAt.comp v ((hasFDerivAt_id v).const_add c)
    have hm := (hg (c - v)).hasFDerivAt.comp v ((hasFDerivAt_id v).const_sub c)
    convert ((hp.sub hm).const_smul (1 / 2 : ℝ)).sub (H c).hasFDerivAt using 1
    · rfl
    · ext w
      simp [D, H, sub_eq_add_neg]
  have hbound : ∀ v ∈ segment ℝ (0 : E) s, ‖D v‖ ≤ L * ‖s‖ ^ 2 := by
    intro v hv
    have hn : ‖v‖ ≤ ‖s‖ := by
      simpa only [sub_zero] using OracleTemplate.LocalHiddenConvex.norm_sub_le_of_mem_segment' hv
    exact (symmetric_hessian_remainder hf hL hT c v).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hL)
  have hh := (convex_segment (0 : E) s).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => (hd v).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ (0 : E) s) (right_mem_segment ℝ (0 : E) s)
  simpa only [F, map_zero, add_zero, sub_zero, sub_self, smul_zero, pow_succ, mul_assoc] using hh

lemma model_gradient_mismatch {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c s : E) (B : E →L[ℝ] E) (hB : ‖B - fderiv ℝ (gradient f) c‖ ≤ δ / 16) :
    ‖gradient f (c + s) + (δ + 8 * L * ‖s‖ ^ 2) • s -
      modelGradient (gradient f) c B L δ s‖ ≤
        (3 / 16 : ℝ) * (δ + 8 * L * ‖s‖ ^ 2) * ‖s‖ := by
  let H := fderiv ℝ (gradient f) c
  have he : gradient f (c + s) + (δ + 8 * L * ‖s‖ ^ 2) • s -
      modelGradient (gradient f) c B L δ s =
      ((1 / 2 : ℝ) • (gradient f (c + s) - gradient f (c - s)) - H s) + (H - B) s := by
    simp only [modelGradient, kernelGradient, sub_apply]
    module
  have hBs : ‖(H - B) s‖ ≤ δ / 16 * ‖s‖ := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
    simpa only [norm_sub_rev] using hB
  have hr := symmetric_gradient_remainder hf hL hT c s
  rw [he]
  have hh := norm_add_le ((1 / 2 : ℝ) • (gradient f (c + s) - gradient f (c - s)) - H s) ((H - B) s)
  have hn := norm_nonneg s
  have hLn : 0 ≤ L * ‖s‖ ^ 3 := mul_nonneg hL (pow_nonneg hn _)
  have hδn := mul_nonneg hδ hn
  change ‖(1 / 2 : ℝ) • (gradient f (c + s) - gradient f (c - s)) - H s‖ ≤ _ at hr
  nlinarith

lemma model_outer_residual {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L δ a : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c s n : E) (B : E →L[ℝ] E) (hB : ‖B - fderiv ℝ (gradient f) c‖ ≤ δ / 16)
    (hinner : ‖modelGradient (gradient f) c B L δ s + n‖ ≤ 35 * a) :
    ‖gradient f (c + s) + n + (δ + 8 * L * ‖s‖ ^ 2) • s‖ ≤
      (3 / 16 : ℝ) * (δ + 8 * L * ‖s‖ ^ 2) * ‖s‖ + 35 * a := by
  have he : gradient f (c + s) + n + (δ + 8 * L * ‖s‖ ^ 2) • s =
      (gradient f (c + s) + (δ + 8 * L * ‖s‖ ^ 2) • s - modelGradient (gradient f) c B L δ s) +
      (modelGradient (gradient f) c B L δ s + n) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (model_gradient_mismatch hf hL hδ hT c s B hB) hinner)

end LongTails.Proofs.SymmetricThirdOrderGeometry
