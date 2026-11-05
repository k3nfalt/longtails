import LongTails.Proofs.SymmetricThirdOrderSmoothness
import LongTails.Proofs.SymmetricThirdOrderInner
import LongTails.Proofs.SymmetricThirdOrderExecution
import LongTails.Proofs.SymmetricThirdOrderTuning
import LongTails.Proofs.SymmetricThirdOrderHessian

namespace LongTails.Proofs.SymmetricThirdOrderRound

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderGeometry
open LongTails.Proofs.SymmetricThirdOrderSmoothness
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_translate (q : E → ℝ) (c : E) :
    gradient (fun v => q (v - c)) = fun v => gradient q (v - c) := by
  funext v
  simp only [gradient, fderiv_comp_sub]

lemma hessian_translate (q : E → ℝ) (c : E) :
    fderiv ℝ (gradient (fun v => q (v - c))) = fun v => fderiv ℝ (gradient q) (v - c) := by
  rw [gradient_translate]
  funext v
  exact fderiv_comp_sub c

lemma third_translate (q : E → ℝ) (c v : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun v => q (v - c)))) v =
      fderiv ℝ (fderiv ℝ (gradient q)) (v - c) := by
  rw [hessian_translate]
  exact fderiv_comp_sub c

omit [FiniteDimensional ℝ E] in
lemma convex_translate {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q) (c : E) :
    ConvexOn ℝ Set.univ (fun v => q (v - c)) := by
  simpa [Function.comp_def, Pi.sub_apply] using hq.comp_affineMap ((AffineMap.id ℝ E) - AffineMap.const ℝ E c)

lemma translated_model_third_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c : E) (B : E →L[ℝ] E) (δ : ℝ)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun v => model f c B L δ (v - c)))) x -
      fderiv ℝ (fderiv ℝ (gradient (fun v => model f c B L δ (v - c)))) y‖ ≤
        49 * L * ‖x - y‖ := by
  rw [third_translate, third_translate]
  simpa only [sub_sub_sub_cancel_right] using model_third_lipschitz hf hL hT c B δ hsym (x - c) (y - c)

omit [FiniteDimensional ℝ E] in
lemma model_minimizer_exists {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (C : Set E) (hC : IsCompact C) (hne : C.Nonempty)
    (c : E) (B : E →L[ℝ] E) (L δ : ℝ) :
    ∃ u ∈ C, ∀ v ∈ C, model f c B L δ (u - c) ≤ model f c B L δ (v - c) := by
  exact hC.exists_isMinOn hne
    (((model_contDiff hf c B L δ).continuous.comp (continuous_id.sub continuous_const)).continuousOn)

lemma inner_uniform_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ a D : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (fallback c : E) (B : E →L[ℝ] E) (G : ℕ → E → E)
    (hC : IsCompact C) (hconv : Convex ℝ C) (hx : fallback ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (hgap0 : ∀ v ∈ C, model f c B L δ (fallback - c) - model f c B L δ (v - c) ≤ D)
    (k : ℕ) (htune : (6 / 7 : ℝ) ^ k * (8 * D) ≤ a ^ 2 / δ)
    (herr : ∀ j < k + 1,
      ‖G j (innerIterate C fallback c B L δ G j) - gradient (model f c B L δ)
        (innerIterate C fallback c B L δ G j - c)‖ ≤ a) :
    ∀ v ∈ C, δ * (model f c B L δ (innerIterate C fallback c B L δ G (k + 1) - c) -
      model f c B L δ (v - c)) ≤ 16 * a ^ 2 := by
  obtain ⟨u, hu, hmin⟩ := model_minimizer_exists hf C hC ⟨fallback, hx⟩ c B L δ
  have hi := SymmetricThirdOrderInner.initial_bregman_bound hf hc hL hδ.le hT C hconv c fallback u B
    hx hu hsym hB hmin
  have hinit : (6 / 7 : ℝ) ^ k *
      ThirdOrderBregmanGeometry.translatedGap (kernel B L δ) (u - fallback) (fallback - c) ≤ a ^ 2 / δ := by
    apply le_trans _ htune
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hg := hgap0 u hu
    linarith
  have hgap := SymmetricThirdOrderInner.innerIterate_gap hf hc hL hδ hT C fallback c u B G
    hC hconv hx hu hsym hB hmin k herr hinit
  intro v hv
  have hm := hmin v hv
  have hh : model f c B L δ (innerIterate C fallback c B L δ G (k + 1) - c) -
      model f c B L δ (v - c) ≤ 16 * a ^ 2 / δ := by linarith
  have hh' := (le_div_iff₀ hδ).mp hh
  nlinarith

lemma model_cleanup_accuracy {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 < a)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (fallback c y : E) (B H : E →L[ℝ] E) (g : E)
    (hC : IsCompact C) (hconv : Convex ℝ C) (hy : y ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (hBerr : ‖B - fderiv ℝ (gradient f) c‖ ≤ δ / 16)
    (hHsym : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫) (hHpos : ∀ v, 0 ≤ ⟪v, H v⟫)
    (hgap : ∀ v ∈ C, δ * (model f c B L δ (y - c) - model f c B L δ (v - c)) ≤ 16 * a ^ 2)
    (hg : ‖g - modelGradient (gradient f) c B L δ (y - c)‖ ≤ a)
    (hHerr : ‖H - modelHessian (fderiv ℝ (gradient f)) c B L δ (y - c)‖ ≤ δ / 8)
    (htune : 262144 * L * a ^ 2 ≤ δ ^ 3) :
    let z := cleanupPoint C fallback y H δ g
    let n := -g - H (z - y) - δ • (z - y)
    ‖gradient f z + n + (δ + 8 * L * ‖z - c‖ ^ 2) • (z - c)‖ ≤
      (3 / 16 : ℝ) * (δ + 8 * L * ‖z - c‖ ^ 2) * ‖z - c‖ + 35 * a ∧
      ∀ v ∈ C, ⟪n, v - z⟫ ≤ 0 := by
  let q := fun v => model f c B L δ (v - c)
  have hq : ContDiff ℝ 3 q := (model_contDiff hf c B L δ).comp (contDiff_id.sub contDiff_const)
  have hqc : ConvexOn ℝ Set.univ q := convex_translate (model_convex hf hc hL.le hδ.le hT c B hsym hB) c
  have hqg : gradient q = fun v => modelGradient (gradient f) c B L δ (v - c) := by
    rw [show q = (fun v => model f c B L δ (v - c)) from rfl, gradient_translate,
      model_gradient (hf.differentiable (by norm_num)) c B L δ hsym]
  have hqh : fderiv ℝ (gradient q) y = modelHessian (fderiv ℝ (gradient f)) c B L δ (y - c) := by
    rw [show q = (fun v => model f c B L δ (v - c)) from rfl, hessian_translate,
      model_hessian_identity hf c B L δ hsym]
  have hclean := SymmetricThirdOrderMinimizers.cleanupPoint_accuracy hq hqc
    (show 0 < 49 * L by positivity) ha hδ
    (translated_model_third_lipschitz hf hL.le hT c B δ hsym)
    C fallback y H g hC ⟨y, hy⟩ hconv hy hHsym hHpos hgap
    (by rwa [hqg]) (by rwa [hqh]) (by nlinarith [mul_nonneg hL.le (sq_nonneg a)])
  dsimp only at hclean ⊢
  constructor
  · have hi : ‖modelGradient (gradient f) c B L δ (cleanupPoint C fallback y H δ g - c) +
        (-g - H (cleanupPoint C fallback y H δ g - y) - δ • (cleanupPoint C fallback y H δ g - y))‖ ≤ 35 * a := by
      have hh := hclean.1
      rw [hqg] at hh
      convert hh using 1
      congr 1
      abel
    have hh := model_outer_residual hf hL.le hδ.le hT c (cleanupPoint C fallback y H δ g - c)
      (-g - H (cleanupPoint C fallback y H δ g - y) - δ • (cleanupPoint C fallback y H δ g - y)) B hBerr hi
    simpa only [add_sub_cancel] using hh
  · exact hclean.2

omit [FiniteDimensional ℝ E] in
lemma paired_gradient_error (g : E → E) (c y gp gm : E) (B : E →L[ℝ] E)
    (L δ a : ℝ) (hp : ‖gp - g y‖ ≤ a) (hm : ‖gm - g (c - (y - c))‖ ≤ a) :
    ‖(1 / 2 : ℝ) • (gp + gm) + kernelGradient B L δ (y - c) -
      modelGradient g c B L δ (y - c)‖ ≤ a := by
  have he : (1 / 2 : ℝ) • (gp + gm) + kernelGradient B L δ (y - c) -
      modelGradient g c B L δ (y - c) =
      (1 / 2 : ℝ) • ((gp - g y) + (gm - g (c - (y - c)))) := by
    simp only [modelGradient, add_sub_cancel]
    module
  rw [he, norm_smul]
  have hh := norm_add_le (gp - g y) (gm - g (c - (y - c)))
  norm_num only [Real.norm_eq_abs, abs_div, abs_one, abs_two]
  linarith

omit [FiniteDimensional ℝ E] in
lemma paired_hessian_error (H : E → E →L[ℝ] E) (c y : E)
    (B Hp Hm : E →L[ℝ] E) (L δ ε : ℝ)
    (hp : ‖Hp - H y‖ ≤ ε) (hm : ‖Hm - H (c - (y - c))‖ ≤ ε) :
    ‖(1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ (y - c) -
      modelHessian H c B L δ (y - c)‖ ≤ ε := by
  have he : (1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ (y - c) -
      modelHessian H c B L δ (y - c) =
      (1 / 2 : ℝ) • ((Hp - H y) - (Hm - H (c - (y - c)))) := by
    simp only [modelHessian, add_sub_cancel]
    module
  rw [he]
  have hs := ContinuousLinearMap.opNorm_smul_le (1 / 2 : ℝ)
    ((Hp - H y) - (Hm - H (c - (y - c))))
  have hh := norm_sub_le (Hp - H y) (Hm - H (c - (y - c)))
  have hehalf : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hehalf] at hs
  linarith

lemma center_initial_gap {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ σ R Δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hδσ : 288 * σ ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c x0 xstar v : E) (A : E →L[ℝ] E)
    (herr : ‖A - fderiv ℝ (gradient f) c‖ ≤ 9 * σ)
    (hmin : ∀ x, f xstar ≤ f x) (hgap : f x0 - f xstar ≤ Δ)
    (hdist : ‖x0 - c‖ ≤ R) :
    model f c (shiftedHessian A (9 * σ)) L δ (x0 - c) -
      model f c (shiftedHessian A (9 * σ)) L δ (v - c) ≤ Δ + 3 * L * R ^ 4 + δ * R ^ 2 := by
  have hpos := ThirdOrderBregmanGeometry.convex_hessian_nonneg hf hc c
  have hi := SymmetricThirdOrderHessian.shiftedHessian_interval hpos herr
  have hh := model_initial_gap hf hL hδ (show 0 ≤ 18 * σ by positivity) hT c x0 xstar (v - c)
    (shiftedHessian A (9 * σ)) (fun w => (hi w).1) (fun w => by have := (hi w).2; nlinarith)
    hmin hgap hdist
  have hcoeff : (18 * σ + δ) / 2 ≤ δ := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg R)
  linarith

lemma clipped_model_hessian_error {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ ε : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (c y : E) (B Hp Hm : E →L[ℝ] E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hB : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫)
    (hp : ‖Hp - fderiv ℝ (gradient f) y‖ ≤ ε)
    (hm : ‖Hm - fderiv ℝ (gradient f) (c - (y - c))‖ ≤ ε) :
    ‖shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ (y - c)) 0 -
      modelHessian (fderiv ℝ (gradient f)) c B L δ (y - c)‖ ≤ 2 * ε := by
  have hq := model_contDiff hf c B L δ
  have hqc := model_convex hf hc hL hδ hT c B hsym hB
  have hpos := ThirdOrderBregmanGeometry.convex_hessian_nonneg hq hqc (y - c)
  rw [model_hessian_identity hf c B L δ hsym] at hpos
  exact SymmetricThirdOrderHessian.shiftedHessian_cleanup_error hpos
    (paired_hessian_error (fderiv ℝ (gradient f)) c y B Hp Hm L δ ε hp hm)

omit [FiniteDimensional ℝ E] in
lemma kernelHessian_symmetric (B : E →L[ℝ] E) (L δ : ℝ) (s : E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (x y : E) :
    ⟪x, kernelHessian B L δ s y⟫ = ⟪kernelHessian B L δ s x, y⟫ := by
  simp only [kernelHessian, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hsym x y]
  have hxs : ⟪x, s⟫ = ⟪s, x⟫ := real_inner_comm _ _
  rw [hxs]
  ring

omit [FiniteDimensional ℝ E] in
lemma cleanupHessian_symmetric (B Hp Hm : E →L[ℝ] E) (L δ : ℝ) (s : E)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hp : ∀ x y : E, ⟪x, Hp y⟫ = ⟪Hp x, y⟫)
    (hm : ∀ x y : E, ⟪x, Hm y⟫ = ⟪Hm x, y⟫) (x y : E) :
    ⟪x, shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ s) 0 y⟫ =
      ⟪shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ s) 0 x, y⟫ := by
  apply SymmetricThirdOrderHessian.shiftedHessian_symmetric
  intro v w
  simp only [add_apply, smul_apply, sub_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hp v w, hm v w, kernelHessian_symmetric B L δ s hB v w]

lemma estimated_round_accuracy {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L δ σ R Δ a : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hσ : 0 ≤ σ) (ha : 0 < a) (hδσ : 288 * σ ≤ δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (x0 xstar c : E) (A B : E →L[ℝ] E) (G : ℕ → E → E)
    (hC : IsCompact C) (hconv : Convex ℝ C) (hx : x0 ∈ C)
    (hAsym : ∀ x y : E, ⟪x, A y⟫ = ⟪A x, y⟫)
    (hAerr : ‖A - fderiv ℝ (gradient f) c‖ ≤ 9 * σ)
    (hBdef : B = shiftedHessian A (9 * σ))
    (hmin : ∀ x, f xstar ≤ f x) (hgap : f x0 - f xstar ≤ Δ) (hdist : ‖x0 - c‖ ≤ R)
    (k : ℕ) (htune : (6 / 7 : ℝ) ^ k * (8 * (Δ + 3 * L * R ^ 4 + δ * R ^ 2)) ≤ a ^ 2 / δ)
    (hG : ∀ j < k + 1,
      ‖G j (innerIterate C x0 c B L δ G j) - modelGradient (gradient f) c B L δ
        (innerIterate C x0 c B L δ G j - c)‖ ≤ a)
    (y : E) (hydef : y = innerIterate C x0 c B L δ G (k + 1))
    (g : E) (Hp Hm : E →L[ℝ] E)
    (hg : ‖g - modelGradient (gradient f) c B L δ (y - c)‖ ≤ a)
    (hpsym : ∀ x y : E, ⟪x, Hp y⟫ = ⟪Hp x, y⟫)
    (hmsym : ∀ x y : E, ⟪x, Hm y⟫ = ⟪Hm x, y⟫)
    (hp : ‖Hp - fderiv ℝ (gradient f) y‖ ≤ 9 * σ)
    (hm : ‖Hm - fderiv ℝ (gradient f) (c - (y - c))‖ ≤ 9 * σ)
    (hcleanup : 262144 * L * a ^ 2 ≤ δ ^ 3) :
    let H := shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ (y - c)) 0
    let z := cleanupPoint C x0 y H δ g
    let n := -g - H (z - y) - δ • (z - y)
    ‖gradient f z + n + (δ + 8 * L * ‖z - c‖ ^ 2) • (z - c)‖ ≤
      (3 / 16 : ℝ) * (δ + 8 * L * ‖z - c‖ ^ 2) * ‖z - c‖ + 35 * a ∧
      ∀ v ∈ C, ⟪n, v - z⟫ ≤ 0 := by
  have hHtrue := ThirdOrderBregmanGeometry.convex_hessian_nonneg hf hc c
  have hBsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫ := by
    rw [hBdef]
    exact SymmetricThirdOrderHessian.shiftedHessian_symmetric A (9 * σ) hAsym
  have hBlower : ∀ v, ⟪fderiv ℝ (gradient f) c v, v⟫ ≤ ⟪B v, v⟫ := by
    intro v
    rw [hBdef]
    have hh := (SymmetricThirdOrderHessian.shiftedHessian_interval hHtrue hAerr v).1
    linarith
  have hBerr : ‖B - fderiv ℝ (gradient f) c‖ ≤ δ / 16 := by
    rw [hBdef]
    have hh := SymmetricThirdOrderHessian.shiftedHessian_center_error hHtrue hAerr
    linarith
  have hy : y ∈ C := by
    rw [hydef]
    exact SymmetricThirdOrderInner.innerIterate_mem C x0 c B L δ G hC hx (k + 1)
  have hgap0 : ∀ v ∈ C, model f c B L δ (x0 - c) - model f c B L δ (v - c) ≤
      Δ + 3 * L * R ^ 4 + δ * R ^ 2 := by
    intro v _
    rw [hBdef]
    exact center_initial_gap hf hc hL.le hδ.le hσ hδσ hT c x0 xstar v A hAerr hmin hgap hdist
  have hinner := inner_uniform_gap hf hc hL.le hδ hT C x0 c B G hC hconv hx hBsym hBlower
    hgap0 k htune (by rwa [model_gradient (hf.differentiable (by norm_num)) c B L δ hBsym])
  rw [← hydef] at hinner
  apply model_cleanup_accuracy hf hc hL hδ ha hT C x0 c y B _ g hC hconv hy
    hBsym hBlower hBerr (cleanupHessian_symmetric B Hp Hm L δ (y - c) hBsym hpsym hmsym)
    (fun v => by
      simpa only [real_inner_comm] using
        (SymmetricThirdOrderHessian.shiftedHessian_nonneg
          ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B L δ (y - c)) 0 v))
    hinner hg _ hcleanup
  have hh := clipped_model_hessian_error hf hc hL.le hδ.le hT c y B Hp Hm hBsym hBlower hp hm
  linarith

end LongTails.Proofs.SymmetricThirdOrderRound
