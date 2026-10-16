import LongTails.Proofs.WeakGradientConvolution
import LongTails.Proofs.MollifiedSecantMoments

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Convolution ContDiff Topology

namespace LongTails.Proofs.WeakGradientSegments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_segment_square {f : E → ℝ} {g : E → E}
    (hg : Continuous g) (hd : ∀ x, HasGradientAt f (g x) x) (x y : E) :
    (f y - f x) ^ 2 ≤ ‖y - x‖ ^ 2 *
      (∫ t in (0 : ℝ)..1, ‖g (x + t • (y - x))‖ ^ 2) := by
  let c := fun t : ℝ => x + t • (y - x)
  let v := fun t : ℝ => ⟪g (c t), y - x⟫
  have hv : Continuous v := by dsimp [v, c]; fun_prop
  have hder (t : ℝ) : HasDerivAt (fun s => f (c s)) (v t) t := by
    have hc : HasDerivAt c (y - x) t := by
      simpa [c] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact (hd (c t)).hasFDerivAt.comp_hasDerivAt t hc
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hv.intervalIntegrable 0 1)
  have he : (∫ t in (0 : ℝ)..1, v t) = f y - f x := by
    simpa [c] using hf
  have hs := LongTails.Proofs.SphereOddMoments.interval_square_bound hv (by norm_num : (0 : ℝ) ≤ 1)
  rw [he] at hs
  simp only [sub_zero, one_mul] at hs
  have hb (t : ℝ) : v t ^ 2 ≤ ‖y - x‖ ^ 2 * ‖g (c t)‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (abs_real_inner_le_norm (g (c t)) (y - x))
    simpa only [sq_abs, mul_pow, mul_comm, v] using h
  have hg2 : Continuous (fun t : ℝ => ‖y - x‖ ^ 2 * ‖g (c t)‖ ^ 2) := by
    dsimp [c]; fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((hv.pow 2).intervalIntegrable 0 1) (hg2.intervalIntegrable 0 1) (fun t _ => hb t)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hs.trans hm


lemma smooth_stochastic_segment_square [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E × Ω → ℝ} {G : E × Ω → E}
    (hF : Measurable F) (hG : Measurable G)
    (hs : ∀ᵐ ξ ∂P, Continuous (fun z => G (z, ξ)) ∧
      ∀ z, HasGradientAt (fun w => F (w, ξ)) (G (z, ξ)) z)
    (x y : E) {B : ℝ}
    (hi : ∀ t ∈ Ioc (0 : ℝ) 1, Integrable (fun ξ => ‖G (x + t • (y - x), ξ)‖ ^ 2) P)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, (∫ ξ, ‖G (x + t • (y - x), ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => (F (y, ξ) - F (x, ξ)) ^ 2) P ∧
      (∫ ξ, (F (y, ξ) - F (x, ξ)) ^ 2 ∂P) ≤ ‖y - x‖ ^ 2 * B := by
  let Q : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsProbabilityMeasure Q := ⟨by simp [Q, Real.volume_Ioc]⟩
  let V := fun z : ℝ × Ω => ‖G (x + z.1 • (y - x), z.2)‖ ^ 2
  have hV : Measurable V := by
    apply Measurable.pow_const
    apply Measurable.norm
    apply hG.comp
    exact (measurable_const.add (measurable_fst.smul measurable_const)).prodMk measurable_snd
  have hi' : ∀ᵐ t ∂Q, Integrable (fun ξ => V (t, ξ)) P := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb' : ∀ᵐ t ∂Q, (∫ ξ, V (t, ξ) ∂P) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht
  have hJ := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hV.stronglyMeasurable (fun z => sq_nonneg _) hi' (integrable_const B) hb'
  have hJb : (∫ z, V z ∂Q.prod P) ≤ B := by simpa using hJ.2
  have hbound : ∀ᵐ ξ ∂P, (F (y, ξ) - F (x, ξ)) ^ 2 ≤
      ‖y - x‖ ^ 2 * ∫ t, V (t, ξ) ∂Q := by
    filter_upwards [hs] with ξ hξ
    simpa only [V, Q, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      smooth_segment_square hξ.1 hξ.2 x y
  have hm : Measurable (fun ξ => (F (y, ξ) - F (x, ξ)) ^ 2) :=
    ((hF.comp (measurable_const.prodMk measurable_id)).sub
      (hF.comp (measurable_const.prodMk measurable_id))).pow_const 2
  have hL : Integrable (fun ξ => (F (y, ξ) - F (x, ξ)) ^ 2) P := by
    apply (hJ.1.integral_prod_right.const_mul (‖y - x‖ ^ 2)).mono' hm.aestronglyMeasurable
    filter_upwards [hbound] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F (y, ξ) - F (x, ξ)))]
    exact hξ
  refine ⟨hL, ?_⟩
  have hh := integral_mono_ae hL (hJ.1.integral_prod_right.const_mul (‖y - x‖ ^ 2)) hbound
  rw [integral_const_mul, ← integral_prod_symm V hJ.1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hJb (sq_nonneg _))


section FiniteDimensional

open LongTails.Proofs.WeakGradientConvolution

variable {d : ℕ}
local notation "H" => EuclideanSpace ℝ (Fin d)

lemma mollified_segment_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {κ : H → ℝ} {U : Set H} (hFm : Measurable F) (hG : Measurable G)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (hκn : ∀ z, 0 ≤ κ z)
    (hκ1 : (∫ z, κ z) = 1)
    (hF : ∀ᵐ ξ ∂P, LocallyIntegrable (fun z => F (z, ξ)) volume ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x y : H) {B : ℝ}
    (hs : ∀ t ∈ Ioc (0 : ℝ) 1, tsupport (fun z => κ (x + t • (y - x) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    let Fκ := fun z ξ => ((fun w => F (w, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) z
    Integrable (fun ξ => (Fκ y ξ - Fκ x ξ) ^ 2) P ∧
      (∫ ξ, (Fκ y ξ - Fκ x ξ) ^ 2 ∂P) ≤ ‖y - x‖ ^ 2 * B := by
  let Fκ := fun yξ : H × Ω => ((fun z => F (z, yξ.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) yξ.1
  let Gκ := fun yξ : H × Ω => ∫ z, F (z, yξ.2) • gradient κ (yξ.1 - z)
  have hgc : Continuous (gradient κ) := by
    change Continuous (fun z => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ κ z))
    exact (InnerProductSpace.toDual ℝ H).symm.continuous.comp (hκ.continuous_fderiv (by simp))
  have hFκ : Measurable Fκ := (convolution_joint_measurable hFm hκ.continuous.measurable).measurable
  have hGκ : Measurable Gκ := (convolution_vector_joint_measurable hFm hgc.measurable).measurable
  have hSκ : ∀ᵐ ξ ∂P, Continuous (fun y => Gκ (y, ξ)) ∧
      ∀ y, HasGradientAt (fun z => Fκ (z, ξ)) (Gκ (y, ξ)) y := by
    filter_upwards [hF] with ξ hξ
    exact ⟨convolution_kernel_gradient_continuous hξ.1 hκ hc,
      fun y => convolution_hasGradientAt_kernel hξ.1 hκ hc y⟩
  have hM (y : H) (hy : tsupport (fun z => κ (y - z)) ⊆ U) :
      Integrable (fun ξ => ‖Gκ (y, ξ)‖ ^ 2) P ∧ (∫ ξ, ‖Gκ (y, ξ)‖ ^ 2 ∂P) ≤ B := by
    have h := convolution_gradient_second_moment hG hκ hc hκn hκ1 hF y hy hi hb
    have he : (fun ξ => ‖Gκ (y, ξ)‖ ^ 2) =ᵐ[P]
        (fun ξ => ‖gradient (fun z => Fκ (z, ξ)) y‖ ^ 2) := by
      filter_upwards [hSκ] with ξ hξ
      rw [(hξ.2 y).gradient]
    refine ⟨h.1.congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    exact h.2
  exact smooth_stochastic_segment_square hFκ hGκ hSκ x y
    (fun t ht => (hM _ (hs t ht)).1) (fun t ht => (hM _ (hs t ht)).2)


lemma weak_segment_square_of_bumps {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x y : H) {B : ℝ} (hB : 0 ≤ B) (hx : C ∈ 𝓝 x) (hy : C ∈ 𝓝 y)
    (φ : ℕ → ContDiffBump (0 : H))
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hs : ∀ n, ∀ t ∈ Ioc (0 : ℝ) 1,
      tsupport (fun z => (φ n).normed volume (x + t • (y - x) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => (F (y, ξ) - F (x, ξ)) ^ 2) P ∧
      (∫ ξ, (F (y, ξ) - F (x, ξ)) ^ 2 ∂P) ≤ ‖y - x‖ ^ 2 * B := by
  let F0 := fun zξ : H × Ω => C.indicator (fun z => F (z, zξ.2)) zξ.1
  have hF0m : Measurable F0 := by
    change Measurable ((Prod.fst ⁻¹' C).indicator F)
    exact hFm.indicator (hC.measurableSet.preimage measurable_fst)
  have hF0 : ∀ᵐ ξ ∂P, LocallyIntegrable (fun z => F0 (z, ξ)) volume ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F0 (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z := by
    filter_upwards [hF] with ξ hξ
    refine ⟨?_, hξ.2.1, ?_⟩
    · exact ((integrable_indicator_iff hC.measurableSet).mpr
        (hξ.1.integrableOn_compact hC)).locallyIntegrable
    · exact indicator_weak_identity hUC hξ.2.2
  let a := fun n ξ =>
    ((fun z => F0 (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume) y -
      ((fun z => F0 (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume) x
  have hm (n : ℕ) := mollified_segment_square hF0m hG (φ n).contDiff_normed
    (φ n).hasCompactSupport_normed (φ n).nonneg_normed (φ n).integral_normed hF0
    x y (hs n) hi hb
  have ht : ∀ᵐ ξ ∂P, Filter.Tendsto (fun n => a n ξ ^ 2) Filter.atTop
      (𝓝 ((F (y, ξ) - F (x, ξ)) ^ 2)) := by
    filter_upwards [hF] with ξ hξ
    have hmi : AEStronglyMeasurable (C.indicator (fun t => F (t, ξ))) volume :=
      ((hFm.comp (measurable_id.prodMk measurable_const)).indicator hC.measurableSet).aestronglyMeasurable
    have hp := indicator_bump_tendsto_right (hξ.1.continuousAt hy) hy hmi hφ
    have hn := indicator_bump_tendsto_right (hξ.1.continuousAt hx) hx hmi hφ
    exact (hp.sub hn).pow 2
  exact nonnegative_limit_integral_bound (mul_nonneg (sq_nonneg _) hB)
    (fun n => (hm n).1) (fun n => Filter.Eventually.of_forall (fun ξ => sq_nonneg (a n ξ)))
    (fun n => (hm n).2) ht

lemma weak_segment_square_interior {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x y : H) {B : ℝ} (hB : 0 ≤ B) {η : ℝ} (hη : 0 < η)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (x + t • (y - x)) η ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => (F (y, ξ) - F (x, ξ)) ^ 2) P ∧
      (∫ ξ, (F (y, ξ) - F (x, ξ)) ^ 2 ∂P) ≤ ‖y - x‖ ^ 2 * B := by
  obtain ⟨φ, hφ, hφη⟩ := MollifiedSecantMoments.shrinking_bumps (d := d) hη
  have hxU : closedBall x η ⊆ U := by simpa using hs 0 (by norm_num)
  have hyU : closedBall y η ⊆ U := by simpa using hs 1 (by norm_num)
  apply weak_segment_square_of_bumps hC hUC hFm hG hF x y hB
    (Filter.mem_of_superset (closedBall_mem_nhds _ hη) (hxU.trans hUC))
    (Filter.mem_of_superset (closedBall_mem_nhds _ hη) (hyU.trans hUC)) φ hφ _ hi hb
  intro n t ht
  have hk : tsupport ((φ n).normed volume) ⊆ closedBall (0 : H) η := by
    rw [(φ n).tsupport_normed_eq]
    exact closedBall_subset_closedBall (hφη n)
  exact translated_support_subset _ hk (hs t (Ioc_subset_Icc_self ht))

lemma weak_pair_square_on_convex {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U Q : Set H} (hC : IsCompact C) (hUC : U ⊆ C) (hQ : Convex ℝ Q)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {B D η : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hη : 0 < η)
    (hmargin : ∀ x ∈ Q, closedBall x η ⊆ U)
    (hdiam : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {x y : H} (hx : x ∈ Q) (hy : y ∈ Q) :
    Integrable (fun ξ => (F (x, ξ) - F (y, ξ)) ^ 2) P ∧
      (∫ ξ, (F (x, ξ) - F (y, ξ)) ^ 2 ∂P) ≤ D ^ 2 * B := by
  have hh := weak_segment_square_interior hC hUC hFm hG hF y x hB hη
    (fun t ht => hmargin _ (hQ.add_smul_sub_mem hy hx ht)) hi hb
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hD).mpr (hdiam x hx y hy)) hB

lemma antipodal_segment_margin (x u : H) (hu : ‖u‖ = 1)
    {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) {t : ℝ} (ht : t ∈ Icc 0 1) :
    closedBall (x - r • u + t • ((x + r • u) - (x - r • u))) ((R - r) / 2) ⊆ ball x R := by
  have he : x - r • u + t • ((x + r • u) - (x - r • u)) = x + ((2 * t - 1) * r) • u := by
    module
  rw [he]
  apply MollifiedSecantMoments.shifted_closedBall_subset_ball
  have ht' : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, hu, mul_one]
  nlinarith [mul_le_mul_of_nonneg_right ht' hr]

lemma weak_antipodal_square_interior {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x u : H) (hu : ‖u‖ = 1) {r R B : ℝ}
    (hr : 0 < r) (hR : r < R) (hB : 0 ≤ B) (hU : ball x R ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ((F (x + r • u, ξ) - F (x - r • u, ξ)) / (2 * r)) ^ 2) P ∧
      (∫ ξ, ((F (x + r • u, ξ) - F (x - r • u, ξ)) / (2 * r)) ^ 2 ∂P) ≤ B := by
  have hm := weak_segment_square_interior hC hUC hFm hG hF (x - r • u) (x + r • u) hB
    (show 0 < (R - r) / 2 by linarith)
    (fun t ht => (antipodal_segment_margin x u hu hr.le hR ht).trans hU) hi hb
  have he : (x + r • u) - (x - r • u) = (2 * r) • u := by module
  have hn : ‖(x + r • u) - (x - r • u)‖ = 2 * r := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * r), hu, mul_one]
  have hf : (fun ξ => ((F (x + r • u, ξ) - F (x - r • u, ξ)) / (2 * r)) ^ 2) =
      fun ξ => (F (x + r • u, ξ) - F (x - r • u, ξ)) ^ 2 / (2 * r) ^ 2 := by
    funext ξ
    exact div_pow _ _ _
  rw [hf]
  refine ⟨hm.1.div_const _, ?_⟩
  rw [integral_div]
  apply (div_le_iff₀ (by positivity : 0 < (2 * r) ^ 2)).mpr
  rw [hn] at hm
  nlinarith only [hm.2]

lemma weak_antipodal_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x u : H) (hu : ‖u‖ = 1) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ((F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ)) ^ 2) P ∧
      (∫ ξ, ((F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ)) ^ 2 ∂P) ≤ B := by
  obtain ⟨ρ, hρ0, hργ, hρ⟩ := MollifiedSecantMoments.inner_radius_sequence hγ
  let a := fun n ξ => (F (x + ρ n • u, ξ) - F (x - ρ n • u, ξ)) / (2 * ρ n)
  have hm (n : ℕ) := weak_antipodal_square_interior hC hUC hFm hG hF x u hu
    (hρ0 n) (hργ n) hB hU hi hb
  have hmem (r : ℝ) (hr0 : 0 ≤ r) (hrγ : r ≤ γ) :
      x + r • u ∈ C ∧ x - r • u ∈ C := by
    constructor
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
  have ht : ∀ᵐ ξ ∂P, Filter.Tendsto (fun n => a n ξ ^ 2) Filter.atTop
      (𝓝 (((F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ)) ^ 2)) := by
    filter_upwards [hF] with ξ hξ
    have hp : Filter.Tendsto (fun n => x + ρ n • u) Filter.atTop
        (nhdsWithin (x + γ • u) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.add (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem _ (hρ0 n).le (hργ n).le).1)⟩
    have hn : Filter.Tendsto (fun n => x - ρ n • u) Filter.atTop
        (nhdsWithin (x - γ • u) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.sub (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem _ (hρ0 n).le (hργ n).le).2)⟩
    have hpF := Filter.Tendsto.comp (hξ.1 _ (hmem γ hγ.le le_rfl).1) hp
    have hnF := Filter.Tendsto.comp (hξ.1 _ (hmem γ hγ.le le_rfl).2) hn
    exact ((hpF.sub hnF).div (tendsto_const_nhds.mul hρ) (by positivity)).pow 2
  exact nonnegative_limit_integral_bound hB (fun n => (hm n).1)
    (fun n => Filter.Eventually.of_forall (fun ξ => sq_nonneg (a n ξ))) (fun n => (hm n).2) ht

section Spherical

open OracleTemplate.ZerothOrder
variable [NeZero d]
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma weak_spherical_coarse_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ B * ‖v‖ ^ (2 * k) := by
  let a := fun z : S × Ω =>
    (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
  have ha : Measurable a := by
    have hp : Continuous (fun u : S => x + γ • (u : H)) := by fun_prop
    have hn : Continuous (fun u : S => x - γ • (u : H)) := by fun_prop
    exact ((hFm.comp ((hp.measurable.comp measurable_fst).prodMk measurable_snd)).sub
      (hFm.comp ((hn.measurable.comp measurable_fst).prodMk measurable_snd))).div_const _
  have hf (u : S) := weak_antipodal_square hC hUC hFm hG hF x u
    (by simpa only [mem_sphere_zero_iff_norm] using u.property) hγ hB hU hCU hi hb
  have hJ := nonnegative_fiber_integral_bound (P := Q) (ha.pow_const 2).stronglyMeasurable
    (fun z => sq_nonneg _) (Filter.Eventually.of_forall (fun u => (hf u).1))
    (integrable_const B) (Filter.Eventually.of_forall (fun u => (hf u).2))
  have hJb : (∫ z, a z ^ 2 ∂(Q).prod P) ≤ B := by simpa using hJ.2
  have hw : Measurable (fun z : S × Ω => ⟪(z.1 : H), v⟫ ^ (2 * k)) := by
    have hc : Continuous (fun u : S => ⟪(u : H), v⟫) := by fun_prop
    exact (hc.measurable.comp measurable_fst).pow_const _
  have hwb (u : S) : |⟪(u : H), v⟫| ^ (2 * k) ≤ ‖v‖ ^ (2 * k) := by
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
    simpa only [hu, one_mul] using abs_real_inner_le_norm (u : H) v
  have hwi : Integrable (fun z : S × Ω => a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) := by
    apply hJ.1.mul_bdd hw.aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, abs_pow] using hwb z.1
  refine ⟨hwi, ?_⟩
  have hp (z : S × Ω) : a z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k) ≤ a z ^ 2 * ‖v‖ ^ (2 * k) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (le_abs_self _).trans (by simpa only [abs_pow] using hwb z.1)
  have hh := integral_mono hwi (hJ.1.mul_const _) hp
  rw [integral_mul_const] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hJb (pow_nonneg (norm_nonneg _) _))

lemma weak_spherical_directional_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  by_cases hd : 1 < d
  · exact MollifiedSecantMoments.weak_secant_directional_moment hC hUC hFm hG hF x hγ hB hU hCU
      hi hb ⟨0, Nat.zero_lt_of_lt hd⟩ ⟨1, hd⟩ (by intro h; have := congrArg Fin.val h; simp at this) v k
  · have hd1 : d = 1 := by have := NeZero.ne d; omega
    have hh := weak_spherical_coarse_moment hC hUC hFm hG hF x hγ hB hU hCU hi hb v k
    refine ⟨hh.1, ?_⟩
    have hdR : (d : ℝ) = 1 := by exact_mod_cast hd1
    rw [hdR]
    simp only [one_pow, one_mul]
    have h8 : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
    have hf : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k)
    have hc : (1 : ℝ) ≤ 5 * 8 ^ k * (k.factorial : ℝ) := by nlinarith
    have hb' := mul_le_mul_of_nonneg_right hc hB
    have hv' := mul_le_mul_of_nonneg_right hb' (pow_nonneg (norm_nonneg v) (2 * k))
    exact hh.2.trans (by simpa only [one_mul] using hv')

end Spherical

end FiniteDimensional

end LongTails.Proofs.WeakGradientSegments
