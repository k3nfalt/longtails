import LongTails.Proofs.GeneralNormClipping
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open MeasureTheory Set Filter Metric
open scoped RealInnerProductSpace Convolution ContDiff Topology

namespace LongTails.Proofs.WeakGradientConvolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma translated_support_subset {κ : E → ℝ} {η : ℝ} {U : Set E} (x : E)
    (hκ : tsupport κ ⊆ closedBall 0 η) (hx : closedBall x η ⊆ U) :
    tsupport (fun z => κ (x - z)) ⊆ U := by
  apply subset_trans ?_ hx
  apply closure_minimal ?_ isClosed_closedBall
  intro z hz
  have h := hκ (subset_tsupport κ hz)
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev z x] using h

lemma indicator_bump_tendsto {C : Set E} {f : E → ℝ} {x : E}
    (hf : ContinuousAt f x) (hC : C ∈ 𝓝 x)
    (hm : AEStronglyMeasurable (C.indicator f) volume)
    {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      C.indicator f) x) atTop (𝓝 (f x)) := by
  have he : C.indicator f =ᶠ[𝓝 x] f := by
    filter_upwards [hC] with z hz
    exact Set.indicator_of_mem hz f
  have ht : Tendsto (C.indicator f) (𝓝 x) (𝓝 (f x)) := hf.tendsto.congr' he.symm
  exact ContDiffBump.convolution_tendsto_right hφ (Eventually.of_forall (fun _ => hm))
    (ht.comp tendsto_snd) tendsto_const_nhds

lemma indicator_bump_tendsto_right {C : Set E} {f : E → ℝ} {x : E}
    (hf : ContinuousAt f x) (hC : C ∈ 𝓝 x)
    (hm : AEStronglyMeasurable (C.indicator f) volume)
    {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => (C.indicator f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (φ n).normed volume) x) atTop (𝓝 (f x)) := by
  have he (n : ℕ) : (C.indicator f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (φ n).normed volume) x = ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        C.indicator f) x := by
    rw [convolution_def, convolution_lsmul_swap]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm]
  simp_rw [he]
  exact indicator_bump_tendsto hf hC hm hφ

lemma translated_kernel_weak_identity {U : Set E} {f κ : E → ℝ} {g : E → E}
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (hw : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : E, (∫ z, f z * (fderiv ℝ ψ z) v) = -∫ z, ⟪g z, v⟫ * ψ z)
    (x : E) (hs : tsupport (fun z => κ (x - z)) ⊆ U) (v : E) :
    (∫ z, f z * (fderiv ℝ κ (x - z)) v) = ∫ z, κ (x - z) * ⟪g z, v⟫ := by
  let ψ := fun z => κ (x - z)
  have hψ : ContDiff ℝ ∞ ψ := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (z : E) : (fderiv ℝ ψ z) v = -(fderiv ℝ κ (x - z)) v := by
    have h := (hκ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
    simp only [Function.comp_def, Pi.sub_apply, id_eq] at h
    dsimp only [ψ]
    rw [h.fderiv]
    simp
  have h := hw ψ hψ hψc hs v
  simp_rw [hd, mul_neg, integral_neg] at h
  have he : (∫ z, ⟪g z, v⟫ * ψ z) = ∫ z, κ (x - z) * ⟪g z, v⟫ := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact mul_comm _ _
  rw [he] at h
  linarith only [h]

lemma indicator_weak_identity {U C : Set E} {f : E → ℝ} {g : E → E}
    (hUC : U ⊆ C)
    (hw : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : E, (∫ z, f z * (fderiv ℝ ψ z) v) = -∫ z, ⟪g z, v⟫ * ψ z)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) (v : E) :
    (∫ z, C.indicator f z * (fderiv ℝ ψ z) v) = -∫ z, ⟪g z, v⟫ * ψ z := by
  have he (z : E) : C.indicator f z * (fderiv ℝ ψ z) v = f z * (fderiv ℝ ψ z) v := by
    by_cases hz : z ∈ C
    · rw [Set.indicator_of_mem hz]
    · have hn : z ∉ tsupport ψ := fun h => hz (hUC (hs h))
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp
  simp_rw [he]
  exact hw ψ hψ hc hs v

lemma integrable_smul_of_local_support {U : Set E} {κ : E → ℝ} {g : E → E}
    (hg : LocallyIntegrableOn g U volume) (hκ : Continuous κ)
    (hc : HasCompactSupport κ) (hs : tsupport κ ⊆ U) :
    Integrable (fun z => κ z • g z) := by
  have hgi : Integrable ((tsupport κ).indicator g) :=
    (integrable_indicator_iff hc.isCompact.measurableSet).mpr
      (hg.integrableOn_compact_subset hs hc.isCompact)
  have h := hgi.smul_of_top_right (hκ.memLp_top_of_hasCompactSupport hc volume)
  have he : (fun z => κ z • (tsupport κ).indicator g z) = fun z => κ z • g z := by
    funext z
    by_cases hz : z ∈ tsupport κ
    · rw [Set.indicator_of_mem hz]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  change Integrable (fun z => κ z • (tsupport κ).indicator g z) at h
  rw [he] at h
  exact h

lemma convolution_hasGradientAt_of_weak {U : Set E} {f κ : E → ℝ} {g : E → E}
    (hf : LocallyIntegrable f volume) (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (hw : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : E, (∫ z, f z * (fderiv ℝ ψ z) v) = -∫ z, ⟪g z, v⟫ * ψ z)
    (x : E) (hs : tsupport (fun z => κ (x - z)) ⊆ U)
    (hg : Integrable (fun z => κ (x - z) • g z)) :
    HasGradientAt (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ)
      (∫ z, κ (x - z) • g z) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hκ.of_le (by simp)) x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext v
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hc.fderiv ℝ)
    (hκ.continuous_fderiv (by simp)), convolution_def]
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.mul_apply']
  rw [translated_kernel_weak_identity hκ hc hw x hs v]
  have hi := (innerSL ℝ v).integral_comp_comm hg
  simpa only [innerSL_apply_apply, inner_smul_right, real_inner_comm v] using hi.symm

lemma probability_density_of_integral_one {κ : E → ℝ} (hi : Integrable κ)
    (hn : ∀ z, 0 ≤ κ z) (h1 : (∫ z, κ z) = 1) :
    IsProbabilityMeasure (volume.withDensity (fun z => ENNReal.ofReal (κ z))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn), h1]
  norm_num

lemma integral_density_eq {κ : E → ℝ} (hκ : Measurable κ) (hn : ∀ z, 0 ≤ κ z)
    (G : E → E) :
    (∫ z, G z ∂volume.withDensity (fun z => ENNReal.ofReal (κ z))) = ∫ z, κ z • G z := by
  rw [integral_withDensity_eq_integral_toReal_smul hκ.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hn _)]

lemma averaging_preserves_second_moment {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {Q : Measure Z} {P : Measure Ω} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {G : Z × Ω → E} (hG : Measurable G) {B : ℝ}
    (hi : ∀ᵐ z ∂Q, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ᵐ z ∂Q, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ‖∫ z, G (z, ξ) ∂Q‖ ^ 2) P ∧
      (∫ ξ, ‖∫ z, G (z, ξ) ∂Q‖ ^ 2 ∂P) ≤ B := by
  have hm : StronglyMeasurable (fun z => ∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) :=
    (hG.norm.pow_const 2).stronglyMeasurable.integral_prod_right'
  have hmi : Integrable (fun z => ∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) Q := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards [hb] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ξ => sq_nonneg _))]
    exact hz
  have h2 : Integrable (fun zξ : Z × Ω => ‖G zξ‖ ^ 2) (Q.prod P) := by
    apply (integrable_prod_iff (hG.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨hi, ?_⟩
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hmi
  have h1 : Integrable G (Q.prod P) := by
    apply ((integrable_const (1 : ℝ)).add h2).mono' hG.aestronglyMeasurable
    filter_upwards [] with zξ
    change ‖G zξ‖ ≤ 1 + ‖G zξ‖ ^ 2
    nlinarith [sq_nonneg (‖G zξ‖ - 1)]
  have hj : ∀ᵐ ξ ∂P, ‖∫ z, G (z, ξ) ∂Q‖ ^ 2 ≤ ∫ z, ‖G (z, ξ)‖ ^ 2 ∂Q := by
    filter_upwards [h1.prod_left_ae, h2.prod_left_ae] with ξ hξ hξ2
    exact OracleTemplate.GeneralNormClipping.norm_integral_sq_le hξ hξ2
  have hai : Integrable (fun ξ => ‖∫ z, G (z, ξ) ∂Q‖ ^ 2) P := by
    apply h2.integral_prod_right.mono'
      (hG.stronglyMeasurable.integral_prod_left'.norm.pow 2).aestronglyMeasurable
    filter_upwards [hj] with ξ hξ
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using hξ
  refine ⟨hai, ?_⟩
  calc
    _ ≤ ∫ ξ, ∫ z, ‖G (z, ξ)‖ ^ 2 ∂Q ∂P := integral_mono_ae hai h2.integral_prod_right hj
    _ = ∫ z, ∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P ∂Q := (integral_integral_swap h2).symm
    _ ≤ ∫ _z, B ∂Q := integral_mono_ae hmi (integrable_const B) hb
    _ = B := by simp

lemma nonnegative_limit_integral_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ n, Integrable (f n) P) (hn : ∀ n, 0 ≤ᵐ[P] f n)
    (hb : ∀ n, (∫ ξ, f n ξ ∂P) ≤ B)
    (ht : ∀ᵐ ξ ∂P, Tendsto (fun n => f n ξ) atTop (𝓝 (g ξ))) :
    Integrable g P ∧ (∫ ξ, g ξ ∂P) ≤ B := by
  have hg : 0 ≤ᵐ[P] g := by
    filter_upwards [ht, ae_all_iff.mpr hn] with ξ hξ hξn
    exact ge_of_tendsto hξ (Eventually.of_forall hξn)
  have he : (∫⁻ ξ, ENNReal.ofReal (g ξ) ∂P) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (f n ξ)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ht] with ξ hξ
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hξ).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (f n ξ) ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le' (Frequently.of_forall (fun n => ?_))
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hn n)]
        exact ENNReal.ofReal_le_ofReal (hb n)
  have hgi : Integrable g P :=
    ⟨aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable) ht,
      (hasFiniteIntegral_iff_ofReal hg).mpr (lt_of_le_of_lt he ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hgi hg] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

lemma second_moment_limit_bound {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] {P : Measure Ω} {f : ℕ → Ω → V} {g : Ω → V} {B : ℝ}
    (hB : 0 ≤ B) (hi : ∀ n, Integrable (fun ξ => ‖f n ξ‖ ^ 2) P)
    (hb : ∀ n, (∫ ξ, ‖f n ξ‖ ^ 2 ∂P) ≤ B)
    (ht : ∀ᵐ ξ ∂P, Tendsto (fun n => f n ξ) atTop (𝓝 (g ξ))) :
    Integrable (fun ξ => ‖g ξ‖ ^ 2) P ∧ (∫ ξ, ‖g ξ‖ ^ 2 ∂P) ≤ B := by
  apply nonnegative_limit_integral_bound hB hi
    (fun n => Eventually.of_forall (fun ξ => sq_nonneg ‖f n ξ‖)) hb
  filter_upwards [ht] with ξ hξ
  exact hξ.norm.pow 2

lemma nonnegative_fiber_integral_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure X} {Q : Measure Y} [SFinite P] [SFinite Q]
    {f : X × Y → ℝ} {H : X → ℝ} (hm : StronglyMeasurable f)
    (hn : ∀ z, 0 ≤ f z) (hi : ∀ᵐ x ∂P, Integrable (fun y => f (x, y)) Q)
    (hH : Integrable H P) (hb : ∀ᵐ x ∂P, (∫ y, f (x, y) ∂Q) ≤ H x) :
    Integrable f (P.prod Q) ∧ (∫ z, f z ∂P.prod Q) ≤ ∫ x, H x ∂P := by
  have hI : Integrable (fun x => ∫ y, f (x, y) ∂Q) P := by
    apply hH.mono' hm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => hn (x, y)))]
    exact hx
  have hf : Integrable f (P.prod Q) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨hi, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hI
  refine ⟨hf, ?_⟩
  rw [integral_prod f hf]
  exact integral_mono_ae hI hH hb

lemma convolution_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {F : E × Ω → ℝ} {κ : E → ℝ} (hF : Measurable F) (hκ : Measurable κ) :
    StronglyMeasurable (fun xξ : E × Ω =>
      ((fun z => F (z, xξ.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) xξ.1) := by
  have hm : Measurable (fun w : (E × Ω) × E => F (w.2, w.1.2) * κ (w.1.1 - w.2)) :=
    (hF.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
      (hκ.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))
  simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using
    hm.stronglyMeasurable.integral_prod_right'

lemma kernel_average_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {G : E × Ω → E} {κ : E → ℝ} (hG : Measurable G) (hκ : Measurable κ) :
    StronglyMeasurable (fun xξ : E × Ω => ∫ z, κ (xξ.1 - z) • G (z, xξ.2)) := by
  have hm : Measurable (fun w : (E × Ω) × E => κ (w.1.1 - w.2) • G (w.2, w.1.2)) :=
    (hκ.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).smul
      (hG.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'

lemma kernel_average_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : E × Ω → E} {κ : E → ℝ} {U : Set E}
    (hG : Measurable G) (hκ : Measurable κ) (hκi : Integrable κ)
    (hκn : ∀ z, 0 ≤ κ z) (hκ1 : (∫ z, κ z) = 1) (hs : Function.support κ ⊆ U)
    {B : ℝ} (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ‖∫ z, κ z • G (z, ξ)‖ ^ 2) P ∧
      (∫ ξ, ‖∫ z, κ z • G (z, ξ)‖ ^ 2 ∂P) ≤ B := by
  let Q := volume.withDensity (fun z => ENNReal.ofReal (κ z))
  let : IsProbabilityMeasure Q := probability_density_of_integral_one hκi hκn hκ1
  have hU : ∀ᵐ z ∂Q, z ∈ U := by
    apply (ae_withDensity_iff hκ.ennreal_ofReal).mpr
    filter_upwards [] with z hz
    apply hs
    change κ z ≠ 0
    intro he
    simp [he] at hz
  have h := averaging_preserves_second_moment (Q := Q) hG
    (hU.mono (fun z hz => hi z hz)) (hU.mono (fun z hz => hb z hz))
  have he (ξ : Ω) : (∫ z, G (z, ξ) ∂Q) = ∫ z, κ z • G (z, ξ) :=
    integral_density_eq hκ hκn (fun z => G (z, ξ))
  simpa only [he] using h

lemma convolution_gradient_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : E × Ω → ℝ} {G : E × Ω → E}
    {κ : E → ℝ} {U : Set E} (hG : Measurable G)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (hκn : ∀ z, 0 ≤ κ z)
    (hκ1 : (∫ z, κ z) = 1)
    (hF : ∀ᵐ ξ ∂P, LocallyIntegrable (fun z => F (z, ξ)) volume ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : E, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : E) (hs : tsupport (fun z => κ (x - z)) ⊆ U)
    {B : ℝ} (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ‖gradient
      ((fun z => F (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) x‖ ^ 2) P ∧
      (∫ ξ, ‖gradient ((fun z => F (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) x‖ ^ 2 ∂P) ≤ B := by
  have hkt : Continuous (fun z => κ (x - z)) := hκ.continuous.comp (continuous_const.sub continuous_id)
  have hkc : HasCompactSupport (fun z => κ (x - z)) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hki : Integrable (fun z => κ (x - z)) := hkt.integrable_of_hasCompactSupport hkc
  have hk1 : (∫ z, κ (x - z)) = 1 := (integral_sub_left_eq_self κ volume x).trans hκ1
  have hav := kernel_average_second_moment hG hkt.measurable hki (fun z => hκn (x - z)) hk1
    (fun z hz => hs (subset_tsupport _ hz)) hi hb
  have he : (fun ξ => ‖gradient ((fun z => F (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) x‖ ^ 2)
      =ᵐ[P] (fun ξ => ‖∫ z, κ (x - z) • G (z, ξ)‖ ^ 2) := by
    filter_upwards [hF] with ξ hξ
    have hgi := integrable_smul_of_local_support hξ.2.1 hkt hkc hs
    rw [(convolution_hasGradientAt_of_weak hξ.1 hκ hc hξ.2.2 x hs hgi).gradient]
  refine ⟨hav.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact hav.2

lemma convolution_hasGradientAt_kernel {f κ : E → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (x : E) :
    HasGradientAt (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ)
      (∫ z, f z • gradient κ (x - z)) x := by
  have hgc : Continuous (gradient κ) := by
    change Continuous (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ κ z))
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hκ.continuous_fderiv (by simp))
  have hgs : HasCompactSupport (gradient κ) := by
    exact (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
  have hgi : Integrable (fun z => f z • gradient κ (x - z)) :=
    hgs.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hgc x
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hκ.of_le (by simp)) x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext v
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hc.fderiv ℝ)
    (hκ.continuous_fderiv (by simp)), convolution_def]
  have he := (innerSL ℝ v).integral_comp_comm hgi
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.mul_apply']
  simp only [innerSL_apply_apply] at he
  rw [real_inner_comm, ← he]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [real_inner_smul_right]
  congr 1
  rw [← inner_gradient_left]
  exact real_inner_comm _ _

lemma convolution_kernel_gradient_continuous {f κ : E → ℝ} (hf : LocallyIntegrable f volume)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) :
    Continuous (fun x => ∫ z, f z • gradient κ (x - z)) := by
  have hgc : Continuous (gradient κ) := by
    change Continuous (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ κ z))
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hκ.continuous_fderiv (by simp))
  have hgs : HasCompactSupport (gradient κ) :=
    (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
  exact hgs.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hgc

lemma convolution_vector_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {F : E × Ω → ℝ} {K : E → E} (hF : Measurable F) (hK : Measurable K) :
    StronglyMeasurable (fun xξ : E × Ω => ∫ z, F (z, xξ.2) • K (xξ.1 - z)) := by
  have hm : Measurable (fun w : (E × Ω) × E => F (w.2, w.1.2) • K (w.1.1 - w.2)) :=
    (hF.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).smul
      (hK.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'


lemma normed_mollification_uniform_error {f : E → ℝ} {M : NNReal} (hL : LipschitzWith M f)
    (φ : ContDiffBump (0 : E)) (x : E) :
    |(f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ.normed volume) x - f x| ≤ (M : ℝ) * φ.rOut := by
  have hh := φ.dist_normed_convolution_le (μ := volume) hL.continuous.aestronglyMeasurable
    (fun y hy => (hL.dist_le_mul y x).trans
      (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le M.coe_nonneg))
  have he : (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] φ.normed volume) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
    rw [convolution_def, convolution_lsmul_swap]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm]
  rw [he]
  simpa only [Real.dist_eq] using hh

end LongTails.Proofs.WeakGradientConvolution
