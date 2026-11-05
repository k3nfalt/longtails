import LongTails.Proofs.SymmetricThirdOrderGeometry
import LongTails.Proofs.SymmetricThirdOrderCleanup
import LongTails.Proofs.HessianAdaptiveCubicModel

namespace LongTails.Proofs.SymmetricThirdOrderMinimizers

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderGeometry
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma proxObjective_hasGradientAt (c y : E) (B : E →L[ℝ] E) (L δ : ℝ) (g v : E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    HasGradientAt (proxObjective c y B L δ g)
      (g + 2 • (kernelGradient B L δ (v - c) - kernelGradient B L δ (y - c))) v := by
  have hg := (innerSL ℝ g).hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const y)
  have hk := (kernel_hasGradientAt B L δ (v - c) hsym).hasFDerivAt.comp v
    ((hasFDerivAt_id v).sub_const c)
  have hy := (innerSL ℝ (kernelGradient B L δ (y - c))).hasFDerivAt.comp v
    ((hasFDerivAt_id v).sub_const y)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hg.add ((hk.sub hy).const_mul 2) using 1
  · rfl
  · ext w
    simp

lemma cleanupObjective_hasGradientAt (y : E) (B : E →L[ℝ] E) (δ : ℝ) (g v : E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    HasGradientAt (cleanupObjective y B δ g) (g + B (v - y) + δ • (v - y)) v := by
  have hg := (innerSL ℝ g).hasFDerivAt.comp v ((hasFDerivAt_id v).sub_const y)
  have hk := (kernel_hasGradientAt B 0 δ (v - y) hsym).hasFDerivAt.comp v
    ((hasFDerivAt_id v).sub_const y)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hg.add hk using 1
  · rfl
  · ext w
    simp [kernelGradient, add_assoc]

omit [FiniteDimensional ℝ E] in
lemma proxPoint_spec (C : Set E) (fallback c y : E) (B : E →L[ℝ] E) (L δ : ℝ) (g : E)
    (hC : IsCompact C) (hne : C.Nonempty) :
    proxPoint C fallback c y B L δ g ∈ C ∧
      IsMinOn (proxObjective c y B L δ g) C (proxPoint C fallback c y B L δ g) := by
  apply HessianAdaptiveCubicModel.minimize_spec C fallback _ hC hne
  apply Continuous.continuousOn
  unfold proxObjective kernel
  fun_prop

omit [FiniteDimensional ℝ E] in
lemma cleanupPoint_spec (C : Set E) (fallback y : E) (B : E →L[ℝ] E) (δ : ℝ) (g : E)
    (hC : IsCompact C) (hne : C.Nonempty) :
    cleanupPoint C fallback y B δ g ∈ C ∧
      IsMinOn (cleanupObjective y B δ g) C (cleanupPoint C fallback y B δ g) := by
  apply HessianAdaptiveCubicModel.minimize_spec C fallback _ hC hne
  apply Continuous.continuousOn
  unfold cleanupObjective kernel
  fun_prop

lemma constrained_min_variational {C : Set E} (hC : Convex ℝ C) {φ : E → ℝ}
    {x g : E} (hx : x ∈ C) (hmin : IsMinOn φ C x) (hg : HasGradientAt φ g x) :
    ∀ v ∈ C, 0 ≤ ⟪g, v - x⟫ := by
  intro v hv
  exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hg.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx hv))

lemma proxPoint_variational (C : Set E) (fallback c y : E) (B : E →L[ℝ] E)
    (L δ : ℝ) (g : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    ∀ v ∈ C, 0 ≤ ⟪g + 2 • (kernelGradient B L δ (proxPoint C fallback c y B L δ g - c) -
      kernelGradient B L δ (y - c)), v - proxPoint C fallback c y B L δ g⟫ := by
  have hm := proxPoint_spec C fallback c y B L δ g hC hne
  exact constrained_min_variational hconv hm.1 hm.2
    (proxObjective_hasGradientAt c y B L δ g _ hsym)

lemma cleanupPoint_variational (C : Set E) (fallback y : E) (B : E →L[ℝ] E)
    (δ : ℝ) (g : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    ∀ v ∈ C, 0 ≤ ⟪g + B (cleanupPoint C fallback y B δ g - y) +
      δ • (cleanupPoint C fallback y B δ g - y), v - cleanupPoint C fallback y B δ g⟫ := by
  have hm := cleanupPoint_spec C fallback y B δ g hC hne
  exact constrained_min_variational hconv hm.1 hm.2
    (cleanupObjective_hasGradientAt y B δ g _ hsym)

lemma kernelGradient_strong_monotone (B : E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (hB : ∀ v, 0 ≤ ⟪v, B v⟫) (x y : E) :
    δ * ‖x - y‖ ^ 2 ≤ ⟪kernelGradient B L δ x - kernelGradient B L δ y, x - y⟫ := by
  have hp := kernel_gap_lower B (δ := δ) hL hsym hB x (y - x)
  have hm := kernel_gap_lower B (δ := δ) hL hsym hB y (x - y)
  simp only [ThirdOrderBregmanGeometry.translatedGap, add_sub_cancel,
    kernel_gradient B L δ hsym] at hp hm
  rw [norm_sub_rev y x] at hp
  have he : ⟪kernelGradient B L δ x, y - x⟫ = -⟪kernelGradient B L δ x, x - y⟫ := by
    rw [show y - x = -(x - y) by abel, inner_neg_right]
  rw [he] at hp
  simp only [inner_sub_left]
  have hn := mul_nonneg hL (pow_nonneg (norm_nonneg (x - y)) 4)
  linarith

omit [FiniteDimensional ℝ E] in
lemma variational_unique {C : Set E} {G : E → E} {δ : ℝ} (hδ : 0 < δ)
    (hmono : ∀ x ∈ C, ∀ y ∈ C, δ * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C)
    (hxi : ∀ v ∈ C, 0 ≤ ⟪G x, v - x⟫)
    (hyi : ∀ v ∈ C, 0 ≤ ⟪G y, v - y⟫) : x = y := by
  have hm := hmono x hx y hy
  have hhx := hxi y hy
  have hhy := hyi x hx
  rw [show y - x = -(x - y) by abel, inner_neg_right] at hhx
  simp only [inner_sub_left] at hm
  have hn : ‖x - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

lemma prox_min_unique {C : Set E} (hconv : Convex ℝ C) (c y : E)
    (B : E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (g : E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (hB : ∀ v, 0 ≤ ⟪v, B v⟫)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C)
    (hmu : IsMinOn (proxObjective c y B L δ g) C u)
    (hmv : IsMinOn (proxObjective c y B L δ g) C v) : u = v := by
  let G := fun z => g + 2 • (kernelGradient B L δ (z - c) - kernelGradient B L δ (y - c))
  apply variational_unique (G := G) (δ := 2 * δ) (by positivity) ?_ hu hv
    (constrained_min_variational hconv hu hmu (proxObjective_hasGradientAt c y B L δ g u hsym))
    (constrained_min_variational hconv hv hmv (proxObjective_hasGradientAt c y B L δ g v hsym))
  intro x _ z _
  have hh := kernelGradient_strong_monotone B (δ := δ) hL hsym hB (x - c) (z - c)
  have he : (x - c) - (z - c) = x - z := by abel
  rw [he] at hh
  have hg : G x - G z = (2 : ℝ) •
      (kernelGradient B L δ (x - c) - kernelGradient B L δ (z - c)) := by
    dsimp [G]
    module
  rw [hg, real_inner_smul_left]
  linarith

lemma cleanup_min_unique {C : Set E} (hconv : Convex ℝ C) (y : E)
    (B : E →L[ℝ] E) {δ : ℝ} (hδ : 0 < δ) (g : E)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (hB : ∀ v, 0 ≤ ⟪v, B v⟫)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C)
    (hmu : IsMinOn (cleanupObjective y B δ g) C u)
    (hmv : IsMinOn (cleanupObjective y B δ g) C v) : u = v := by
  let G := fun z => g + B (z - y) + δ • (z - y)
  apply variational_unique (G := G) hδ ?_ hu hv
    (constrained_min_variational hconv hu hmu (cleanupObjective_hasGradientAt y B δ g u hsym))
    (constrained_min_variational hconv hv hmv (cleanupObjective_hasGradientAt y B δ g v hsym))
  intro x _ z _
  have hg : G x - G z = B (x - z) + δ • (x - z) := by
    dsimp [G]
    simp only [map_sub]
    module
  rw [hg, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hh := hB (x - z)
  rw [real_inner_comm] at hh
  linarith

lemma continuous_proxPoint {X : Type*} [TopologicalSpace X]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (c y g : X → E) (B : X → E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hc : Continuous c) (hy : Continuous y) (hg : Continuous g) (hB : Continuous B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫)
    (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫) :
    Continuous (fun p => proxPoint C fallback (c p) (y p) (B p) L δ (g p)) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let m : X → C := fun p => ⟨proxPoint C fallback (c p) (y p) (B p) L δ (g p),
    (proxPoint_spec C fallback _ _ _ _ _ _ hC hne).1⟩
  have hm : Continuous m := by
    apply HessianAdaptiveCubicModel.continuous_unique_minimizer
      (fun p (x : C) => proxObjective (c p) (y p) (B p) L δ (g p) x) m
    · unfold Function.uncurry proxObjective kernel kernelGradient
      fun_prop
    · intro p z
      exact (proxPoint_spec C fallback _ _ _ _ _ _ hC hne).2 z.property
    · intro p z hz
      apply Subtype.ext
      apply prox_min_unique hconv (c p) (y p) (B p) hL hδ (g p)
        (hsym p) (hpos p) z.property (m p).property
      · intro v hv
        exact hz ⟨v, hv⟩
      · exact (proxPoint_spec C fallback _ _ _ _ _ _ hC hne).2
  exact continuous_subtype_val.comp hm

lemma continuous_cleanupPoint {X : Type*} [TopologicalSpace X]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (y g : X → E) (B : X → E →L[ℝ] E) {δ : ℝ} (hδ : 0 < δ)
    (hy : Continuous y) (hg : Continuous g) (hB : Continuous B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫)
    (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫) :
    Continuous (fun p => cleanupPoint C fallback (y p) (B p) δ (g p)) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let m : X → C := fun p => ⟨cleanupPoint C fallback (y p) (B p) δ (g p),
    (cleanupPoint_spec C fallback _ _ _ _ hC hne).1⟩
  have hm : Continuous m := by
    apply HessianAdaptiveCubicModel.continuous_unique_minimizer
      (fun p (x : C) => cleanupObjective (y p) (B p) δ (g p) x) m
    · unfold Function.uncurry cleanupObjective kernel
      fun_prop
    · intro p z
      exact (cleanupPoint_spec C fallback _ _ _ _ hC hne).2 z.property
    · intro p z hz
      apply Subtype.ext
      apply cleanup_min_unique hconv (y p) (B p) hδ (g p)
        (hsym p) (hpos p) z.property (m p).property
      · intro v hv
        exact hz ⟨v, hv⟩
      · exact (cleanupPoint_spec C fallback _ _ _ _ hC hne).2
  exact continuous_subtype_val.comp hm

lemma cleanupPoint_accuracy {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L a δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (C : Set E) (fallback y : E) (B : E →L[ℝ] E) (g : E)
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) (hy : y ∈ C)
    (hsym : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) (hpos : ∀ v, 0 ≤ ⟪v, B v⟫)
    (hgap : ∀ v ∈ C, δ * (f y - f v) ≤ 16 * a ^ 2)
    (hg : ‖g - gradient f y‖ ≤ a) (hB : ‖B - fderiv ℝ (gradient f) y‖ ≤ δ / 8)
    (htune : 4096 * L * a ^ 2 ≤ δ ^ 3) :
    let z := cleanupPoint C fallback y B δ g
    ‖gradient f z - g - B (z - y) - δ • (z - y)‖ ≤ 35 * a ∧
      ∀ v ∈ C, ⟪-g - B (z - y) - δ • (z - y), v - z⟫ ≤ 0 := by
  let z := cleanupPoint C fallback y B δ g
  have hz : z ∈ C := (cleanupPoint_spec C fallback y B δ g hC hne).1
  have he : y + (z - y) = z := by abel
  have hvi : ∀ v ∈ C, 0 ≤ ⟪g + B (z - y) + δ • (z - y), v - (y + (z - y))⟫ := by
    rw [he]
    exact cleanupPoint_variational C fallback y B δ g hC hne hconv hsym
  have hs := SymmetricThirdOrderCleanup.quadratic_variational_descent hy hvi
  have hps : 0 ≤ ⟪B (z - y), z - y⟫ := by
    simpa only [real_inner_comm] using hpos (z - y)
  have hshort := SymmetricThirdOrderCleanup.cleanup_short_step hf hc hL.le ha hδ hT hconv
    y (z - y) g B hy (by rwa [he]) hgap hg hB hps htune hs
  have hn : δ * ‖z - y‖ ≤ 16 * a := by
    have hh := (lt_div_iff₀ hδ).mp hshort
    nlinarith
  have hr := SymmetricThirdOrderCleanup.cleanup_residual hf hc hL ha.le hδ hT
    y (z - y) g B (by rw [he]; exact hgap z hz) hg hB htune hn hs
  have hnormal := SymmetricThirdOrderCleanup.quadratic_variational_normal hvi
  rw [he] at hr hnormal
  exact ⟨hr, hnormal⟩

lemma measurable_proxPoint {X : Type*} [MeasurableSpace X]
    [MeasurableSpace E] [BorelSpace E]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (c y g : X → E) (B : X → E →L[ℝ] E) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hc : Measurable c) (hy : Measurable y) (hg : Measurable g) (hB : Measurable B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫)
    (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫) :
    Measurable (fun p => proxPoint C fallback (c p) (y p) (B p) L δ (g p)) := by
  let S := {v : E × E × E × (E →L[ℝ] E) |
    (∀ x y, ⟪x, v.2.2.2 y⟫ = ⟪v.2.2.2 x, y⟫) ∧ ∀ x, 0 ≤ ⟪x, v.2.2.2 x⟫}
  let φ : S → E := fun v => proxPoint C fallback v.val.1 v.val.2.1 v.val.2.2.2 L δ v.val.2.2.1
  have hφ : Continuous φ := continuous_proxPoint C fallback hC hne hconv
    (fun v : S => v.val.1) (fun v : S => v.val.2.1)
    (fun v : S => v.val.2.2.1) (fun v : S => v.val.2.2.2) hL hδ
    continuous_subtype_val.fst continuous_subtype_val.snd.fst
    continuous_subtype_val.snd.snd.fst continuous_subtype_val.snd.snd.snd
    (fun v => v.property.1) (fun v => v.property.2)
  let ψ : X → S := fun x => ⟨(c x, y x, g x, B x), hsym x, hpos x⟩
  have hψ : Measurable ψ := (hc.prodMk (hy.prodMk (hg.prodMk hB))).subtype_mk
  exact hφ.measurable.comp hψ

lemma measurable_cleanupPoint {X : Type*} [MeasurableSpace X]
    [MeasurableSpace E] [BorelSpace E]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (y g : X → E) (B : X → E →L[ℝ] E) {δ : ℝ} (hδ : 0 < δ)
    (hy : Measurable y) (hg : Measurable g) (hB : Measurable B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫)
    (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫) :
    Measurable (fun p => cleanupPoint C fallback (y p) (B p) δ (g p)) := by
  let S := {v : E × E × (E →L[ℝ] E) |
    (∀ x y, ⟪x, v.2.2 y⟫ = ⟪v.2.2 x, y⟫) ∧ ∀ x, 0 ≤ ⟪x, v.2.2 x⟫}
  let φ : S → E := fun v => cleanupPoint C fallback v.val.1 v.val.2.2 δ v.val.2.1
  have hφ : Continuous φ := continuous_cleanupPoint C fallback hC hne hconv
    (fun v : S => v.val.1) (fun v : S => v.val.2.1) (fun v : S => v.val.2.2) hδ
    continuous_subtype_val.fst continuous_subtype_val.snd.fst continuous_subtype_val.snd.snd
    (fun v => v.property.1) (fun v => v.property.2)
  let ψ : X → S := fun x => ⟨(y x, g x, B x), hsym x, hpos x⟩
  have hψ : Measurable ψ := (hy.prodMk (hg.prodMk hB)).subtype_mk
  exact hφ.measurable.comp hψ

omit [FiniteDimensional ℝ E] in
lemma projectPoint_mem (C : Set E) (fallback v : E) (hC : IsCompact C) (hne : C.Nonempty) :
    projectPoint C fallback v ∈ C := (cleanupPoint_spec C fallback v 0 1 0 hC hne).1

lemma projectPoint_distance (C : Set E) (fallback v xstar : E)
    (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C) (hx : xstar ∈ C) :
    ‖projectPoint C fallback v - xstar‖ ≤ ‖v - xstar‖ := by
  let p := projectPoint C fallback v
  have hh := cleanupPoint_variational C fallback v 0 1 0 hC hne hconv
    (by intros; simp) xstar hx
  change 0 ≤ ⟪(0 : E) + (0 : E →L[ℝ] E) (p - v) + (1 : ℝ) • (p - v), xstar - p⟫ at hh
  simp only [zero_apply, zero_add, one_smul] at hh
  have he : v - xstar = (v - p) + (p - xstar) := by abel
  have hi : ⟪p - v, xstar - p⟫ = ⟪v - p, p - xstar⟫ := by
    rw [show p - v = -(v - p) by abel, show xstar - p = -(p - xstar) by abel]
    simp only [inner_neg_left, inner_neg_right, neg_neg]
  rw [hi] at hh
  have hn := norm_add_sq_real (v - p) (p - xstar)
  rw [← he] at hn
  change ‖p - xstar‖ ≤ ‖v - xstar‖
  nlinarith [sq_nonneg ‖v - p‖, norm_nonneg (p - xstar), norm_nonneg (v - xstar)]

lemma measurable_projectPoint {X : Type*} [MeasurableSpace X]
    [MeasurableSpace E] [BorelSpace E]
    (C : Set E) (fallback : E) (hC : IsCompact C) (hne : C.Nonempty) (hconv : Convex ℝ C)
    (v : X → E) (hv : Measurable v) : Measurable (fun x => projectPoint C fallback (v x)) := by
  exact measurable_cleanupPoint C fallback hC hne hconv v (fun _ => 0) (fun _ => 0)
    (by norm_num : (0 : ℝ) < 1) hv measurable_const measurable_const
    (by intros; simp) (by intros; simp)

end LongTails.Proofs.SymmetricThirdOrderMinimizers
