import LongTails.Proofs.DirectionalSphericalMoments

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Convolution ContDiff Topology

namespace LongTails.Proofs.MollifiedSecantMoments

open OracleTemplate.ZerothOrder LongTails.Proofs.WeakGradientConvolution
  LongTails.Proofs.SphericalSecantMoments

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma mollified_secant_weighted_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {κ : H → ℝ} {U : Set H} (hFm : Measurable F) (hG : Measurable G)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (hκn : ∀ z, 0 ≤ κ z)
    (hκ1 : (∫ z, κ z) = 1)
    (hF : ∀ᵐ ξ ∂P, LocallyIntegrable (fun z => F (z, ξ)) volume ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hs : ∀ u : S, tsupport (fun z => κ (x + γ • (u : H) - z)) ⊆ U ∧
      tsupport (fun z => κ (x - γ • (u : H) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    let Fκ := fun y ξ => ((fun z => F (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) y
    Integrable (fun z : S × Ω =>
      ((Fκ (x + γ • (z.1 : H)) z.2 - Fκ (x - γ • (z.1 : H)) z.2) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((Fκ (x + γ • (z.1 : H)) z.2 - Fκ (x - γ • (z.1 : H)) z.2) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
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
  exact smooth_secant_weighted_moment hFκ hGκ hSκ x hγ hB
    (Filter.Eventually.of_forall (fun u => ⟨(hM _ (hs u).1).1, (hM _ (hs u).2).1⟩))
    (Filter.Eventually.of_forall (fun u => ⟨(hM _ (hs u).1).2, (hM _ (hs u).2).2⟩)) i j hij k

lemma mollified_secant_directional_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {κ : H → ℝ} {U : Set H} (hFm : Measurable F) (hG : Measurable G)
    (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (hκn : ∀ z, 0 ≤ κ z)
    (hκ1 : (∫ z, κ z) = 1)
    (hF : ∀ᵐ ξ ∂P, LocallyIntegrable (fun z => F (z, ξ)) volume ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hs : ∀ u : S, tsupport (fun z => κ (x + γ • (u : H) - z)) ⊆ U ∧
      tsupport (fun z => κ (x - γ • (u : H) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    let Fκ := fun y ξ => ((fun z => F (z, ξ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] κ) y
    Integrable (fun z : S × Ω =>
      ((Fκ (x + γ • (z.1 : H)) z.2 - Fκ (x - γ • (z.1 : H)) z.2) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((Fκ (x + γ • (z.1 : H)) z.2 - Fκ (x - γ • (z.1 : H)) z.2) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
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
  exact LongTails.Proofs.DirectionalSphericalMoments.smooth_secant_directional_moment hFκ hGκ hSκ x hγ hB
    (Filter.Eventually.of_forall (fun u => ⟨(hM _ (hs u).1).1, (hM _ (hs u).2).1⟩))
    (Filter.Eventually.of_forall (fun u => ⟨(hM _ (hs u).1).2, (hM _ (hs u).2).2⟩)) i j hij v k

omit [NeZero d] in
lemma shrinking_bumps {η : ℝ} (hη : 0 < η) :
    ∃ φ : ℕ → ContDiffBump (0 : H),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) ∧ ∀ n, (φ n).rOut ≤ η := by
  let φ : ℕ → ContDiffBump (0 : H) := fun n =>
    { rIn := (η / (n + 2 : ℝ)) / 2
      rOut := η / (n + 2 : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have h : 0 < η / (n + 2 : ℝ) := by positivity
        linarith }
  refine ⟨φ, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.const_div_atTop ht η
  · intro n
    change η / (n + 2 : ℝ) ≤ η
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma weak_secant_weighted_moment_of_bumps {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hnb : ∀ u : S, C ∈ 𝓝 (x + γ • (u : H)) ∧ C ∈ 𝓝 (x - γ • (u : H)))
    (φ : ℕ → ContDiffBump (0 : H))
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hs : ∀ n, ∀ u : S,
      tsupport (fun z => (φ n).normed volume (x + γ • (u : H) - z)) ⊆ U ∧
      tsupport (fun z => (φ n).normed volume (x - γ • (u : H) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
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
  let a := fun n => fun z : S × Ω =>
    (((fun t => F0 (t, z.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume)
      (x + γ • (z.1 : H)) -
      ((fun t => F0 (t, z.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume)
      (x - γ • (z.1 : H))) / (2 * γ)
  have hm (n : ℕ) := mollified_secant_weighted_moment hF0m hG (φ n).contDiff_normed
    (φ n).hasCompactSupport_normed (φ n).nonneg_normed (φ n).integral_normed hF0
    x hγ hB (hs n) hi hb i j hij k
  have ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop
      (𝓝 ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := Q) (ν := P)).ae hF] with z hz
    have hmi : AEStronglyMeasurable (C.indicator (fun t => F (t, z.2))) volume :=
      ((hFm.comp (measurable_id.prodMk measurable_const)).indicator hC.measurableSet).aestronglyMeasurable
    have hp := indicator_bump_tendsto_right (hz.1.continuousAt (hnb z.1).1) (hnb z.1).1 hmi hφ
    have hn := indicator_bump_tendsto_right (hz.1.continuousAt (hnb z.1).2) (hnb z.1).2 hmi hφ
    exact (hp.sub hn).div_const (2 * γ)
  exact weighted_moment_limit (by positivity) i k (fun n => (hm n).1) (fun n => (hm n).2) ht

lemma weak_secant_weighted_moment_interior {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    {η : ℝ} (hη : 0 < η)
    (hs : ∀ u : S, closedBall (x + γ • (u : H)) η ⊆ U ∧
      closedBall (x - γ • (u : H)) η ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  obtain ⟨φ, hφ, hφη⟩ := shrinking_bumps (d := d) hη
  have hnb : ∀ u : S, C ∈ 𝓝 (x + γ • (u : H)) ∧ C ∈ 𝓝 (x - γ • (u : H)) := by
    intro u
    exact ⟨Filter.mem_of_superset (closedBall_mem_nhds _ hη) ((hs u).1.trans hUC),
      Filter.mem_of_superset (closedBall_mem_nhds _ hη) ((hs u).2.trans hUC)⟩
  apply weak_secant_weighted_moment_of_bumps hC hUC hFm hG hF x hγ hB hnb φ hφ _ hi hb i j hij k
  intro n u
  have hk : tsupport ((φ n).normed volume) ⊆ closedBall (0 : H) η := by
    rw [(φ n).tsupport_normed_eq]
    exact closedBall_subset_closedBall (hφη n)
  exact ⟨translated_support_subset _ hk (hs u).1, translated_support_subset _ hk (hs u).2⟩

omit [NeZero d] in
lemma shifted_closedBall_subset_ball (x v : H) {η R : ℝ} (h : η + ‖v‖ < R) :
    closedBall (x + v) η ⊆ ball x R := by
  intro z hz
  apply mem_ball.mpr
  calc
    dist z x ≤ dist z (x + v) + dist (x + v) x := dist_triangle _ _ _
    _ ≤ η + ‖v‖ := by
      rw [show dist (x + v) x = ‖v‖ by simp [dist_eq_norm]]
      exact add_le_add (mem_closedBall.mp hz) le_rfl
    _ < R := h

omit [NeZero d] in
lemma paired_sphere_margin (x : H) {γ R : ℝ} (hγ : 0 ≤ γ) (hR : γ < R) (u : S) :
    closedBall (x + γ • (u : H)) ((R - γ) / 2) ⊆ ball x R ∧
      closedBall (x - γ • (u : H)) ((R - γ) / 2) ⊆ ball x R := by
  have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
  have hv : ‖γ • (u : H)‖ = γ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ, hu, mul_one]
  constructor
  · apply shifted_closedBall_subset_ball
    rw [hv]
    linarith
  · simpa only [sub_eq_add_neg] using shifted_closedBall_subset_ball x (-(γ • (u : H)))
      (show (R - γ) / 2 + ‖-(γ • (u : H))‖ < R by rw [norm_neg, hv]; linarith)

lemma weak_secant_weighted_moment_radius_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 < ρ n) (hργ : ∀ n, ρ n < γ)
    (hρ : Filter.Tendsto ρ Filter.atTop (𝓝 γ))
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  let a := fun n => fun z : S × Ω =>
    (F (x + ρ n • (z.1 : H), z.2) - F (x - ρ n • (z.1 : H), z.2)) / (2 * ρ n)
  have hm (n : ℕ) := weak_secant_weighted_moment_interior hC hUC hFm hG hF x
    (ne_of_gt (hρ0 n)) hB (show 0 < (γ - ρ n) / 2 by linarith [hργ n])
    (fun u => ⟨(paired_sphere_margin x (hρ0 n).le (hργ n) u).1.trans hU,
      (paired_sphere_margin x (hρ0 n).le (hργ n) u).2.trans hU⟩) hi hb i j hij k
  have hmem (u : S) (r : ℝ) (hr0 : 0 ≤ r) (hrγ : r ≤ γ) :
      x + r • (u : H) ∈ C ∧ x - r • (u : H) ∈ C := by
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
    constructor
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
  have ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop
      (𝓝 ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := Q) (ν := P)).ae hF] with z hz
    have hp : Filter.Tendsto (fun n => x + ρ n • (z.1 : H)) Filter.atTop
        (nhdsWithin (x + γ • (z.1 : H)) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.add (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem z.1 _ (hρ0 n).le (hργ n).le).1)⟩
    have hn : Filter.Tendsto (fun n => x - ρ n • (z.1 : H)) Filter.atTop
        (nhdsWithin (x - γ • (z.1 : H)) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.sub (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem z.1 _ (hρ0 n).le (hργ n).le).2)⟩
    have hpF := Filter.Tendsto.comp (hz.1 _ (hmem z.1 γ hγ.le le_rfl).1) hp
    have hnF := Filter.Tendsto.comp (hz.1 _ (hmem z.1 γ hγ.le le_rfl).2) hn
    exact (hpF.sub hnF).div (tendsto_const_nhds.mul hρ) (by positivity)
  exact weighted_moment_limit (by positivity) i k (fun n => (hm n).1) (fun n => (hm n).2) ht

lemma inner_radius_sequence {γ : ℝ} (hγ : 0 < γ) :
    ∃ ρ : ℕ → ℝ, (∀ n, 0 < ρ n) ∧ (∀ n, ρ n < γ) ∧
      Filter.Tendsto ρ Filter.atTop (𝓝 γ) := by
  obtain ⟨φ, hφ, hφγ⟩ := shrinking_bumps (d := 1) hγ
  refine ⟨fun n => γ - (φ n).rOut / 2, ?_, ?_, ?_⟩
  · intro n
    linarith [hφγ n]
  · intro n
    linarith [(φ n).rOut_pos]
  · simpa using tendsto_const_nhds.sub (hφ.div_const 2)

lemma weak_secant_weighted_moment {Ω : Type*} [MeasurableSpace Ω]
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
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  obtain ⟨ρ, hρ0, hργ, hρ⟩ := inner_radius_sequence hγ
  exact weak_secant_weighted_moment_radius_limit hC hUC hFm hG hF x hγ hB hU hCU
    ρ hρ0 hργ hρ hi hb i j hij k

lemma directional_moment_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → S × Ω → ℝ} {b : S × Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (v : H) (k : ℕ)
    (hi : ∀ n, Integrable (fun z : S × Ω => a n z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P))
    (hb : ∀ n, (d : ℝ) ^ (k + 1) *
      (∫ z : S × Ω, a n z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ B)
    (ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop (𝓝 (b z))) :
    Integrable (fun z : S × Ω => b z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) *
        (∫ z : S × Ω, b z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) ^ (k + 1) := pow_pos hd0 _
  have hn : ∀ n, 0 ≤ᵐ[(Q).prod P] (fun z : S × Ω => a n z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) := by
    intro n
    filter_upwards [] with z
    apply mul_nonneg (sq_nonneg _)
    rw [mul_comm 2 k, pow_mul]
    exact sq_nonneg _
  have hc : ∀ᵐ z ∂(Q).prod P,
      Filter.Tendsto (fun n => a n z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) Filter.atTop
        (𝓝 (b z ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k))) := by
    filter_upwards [ht] with z hz
    exact (hz.pow 2).mul_const _
  have h := nonnegative_limit_integral_bound (div_nonneg hB hd.le) hi hn
    (fun n => (le_div_iff₀ hd).mpr (by nlinarith only [hb n])) hc
  refine ⟨h.1, ?_⟩
  have hh := (le_div_iff₀ hd).mp h.2
  nlinarith only [hh]


lemma weak_secant_directional_moment_of_bumps {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hnb : ∀ u : S, C ∈ 𝓝 (x + γ • (u : H)) ∧ C ∈ 𝓝 (x - γ • (u : H)))
    (φ : ℕ → ContDiffBump (0 : H))
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hs : ∀ n, ∀ u : S,
      tsupport (fun z => (φ n).normed volume (x + γ • (u : H) - z)) ⊆ U ∧
      tsupport (fun z => (φ n).normed volume (x - γ • (u : H) - z)) ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
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
  let a := fun n => fun z : S × Ω =>
    (((fun t => F0 (t, z.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume)
      (x + γ • (z.1 : H)) -
      ((fun t => F0 (t, z.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume)
      (x - γ • (z.1 : H))) / (2 * γ)
  have hm (n : ℕ) := mollified_secant_directional_moment hF0m hG (φ n).contDiff_normed
    (φ n).hasCompactSupport_normed (φ n).nonneg_normed (φ n).integral_normed hF0
    x hγ hB (hs n) hi hb i j hij v k
  have ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop
      (𝓝 ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := Q) (ν := P)).ae hF] with z hz
    have hmi : AEStronglyMeasurable (C.indicator (fun t => F (t, z.2))) volume :=
      ((hFm.comp (measurable_id.prodMk measurable_const)).indicator hC.measurableSet).aestronglyMeasurable
    have hp := indicator_bump_tendsto_right (hz.1.continuousAt (hnb z.1).1) (hnb z.1).1 hmi hφ
    have hn := indicator_bump_tendsto_right (hz.1.continuousAt (hnb z.1).2) (hnb z.1).2 hmi hφ
    exact (hp.sub hn).div_const (2 * γ)
  exact directional_moment_limit (by positivity) v k (fun n => (hm n).1) (fun n => (hm n).2) ht

lemma weak_secant_directional_moment_interior {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    {η : ℝ} (hη : 0 < η)
    (hs : ∀ u : S, closedBall (x + γ • (u : H)) η ⊆ U ∧
      closedBall (x - γ • (u : H)) η ⊆ U)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  obtain ⟨φ, hφ, hφη⟩ := shrinking_bumps (d := d) hη
  have hnb : ∀ u : S, C ∈ 𝓝 (x + γ • (u : H)) ∧ C ∈ 𝓝 (x - γ • (u : H)) := by
    intro u
    exact ⟨Filter.mem_of_superset (closedBall_mem_nhds _ hη) ((hs u).1.trans hUC),
      Filter.mem_of_superset (closedBall_mem_nhds _ hη) ((hs u).2.trans hUC)⟩
  apply weak_secant_directional_moment_of_bumps hC hUC hFm hG hF x hγ hB hnb φ hφ _ hi hb i j hij v k
  intro n u
  have hk : tsupport ((φ n).normed volume) ⊆ closedBall (0 : H) η := by
    rw [(φ n).tsupport_normed_eq]
    exact closedBall_subset_closedBall (hφη n)
  exact ⟨translated_support_subset _ hk (hs u).1, translated_support_subset _ hk (hs u).2⟩

lemma weak_secant_directional_moment_radius_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 < ρ n) (hργ : ∀ n, ρ n < γ)
    (hρ : Filter.Tendsto ρ Filter.atTop (𝓝 γ))
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  let a := fun n => fun z : S × Ω =>
    (F (x + ρ n • (z.1 : H), z.2) - F (x - ρ n • (z.1 : H), z.2)) / (2 * ρ n)
  have hm (n : ℕ) := weak_secant_directional_moment_interior hC hUC hFm hG hF x
    (ne_of_gt (hρ0 n)) hB (show 0 < (γ - ρ n) / 2 by linarith [hργ n])
    (fun u => ⟨(paired_sphere_margin x (hρ0 n).le (hργ n) u).1.trans hU,
      (paired_sphere_margin x (hρ0 n).le (hργ n) u).2.trans hU⟩) hi hb i j hij v k
  have hmem (u : S) (r : ℝ) (hr0 : 0 ≤ r) (hrγ : r ≤ γ) :
      x + r • (u : H) ∈ C ∧ x - r • (u : H) ∈ C := by
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
    constructor
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
    · apply hCU
      simp only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one]
      exact hrγ
  have ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop
      (𝓝 ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := Q) (ν := P)).ae hF] with z hz
    have hp : Filter.Tendsto (fun n => x + ρ n • (z.1 : H)) Filter.atTop
        (nhdsWithin (x + γ • (z.1 : H)) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.add (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem z.1 _ (hρ0 n).le (hργ n).le).1)⟩
    have hn : Filter.Tendsto (fun n => x - ρ n • (z.1 : H)) Filter.atTop
        (nhdsWithin (x - γ • (z.1 : H)) C) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.sub (hρ.smul_const _),
        Filter.Eventually.of_forall (fun n => (hmem z.1 _ (hρ0 n).le (hργ n).le).2)⟩
    have hpF := Filter.Tendsto.comp (hz.1 _ (hmem z.1 γ hγ.le le_rfl).1) hp
    have hnF := Filter.Tendsto.comp (hz.1 _ (hmem z.1 γ hγ.le le_rfl).2) hn
    exact (hpF.sub hnF).div (tendsto_const_nhds.mul hρ) (by positivity)
  exact directional_moment_limit (by positivity) v k (fun n => (hm n).1) (fun n => (hm n).2) ht

lemma weak_secant_directional_moment {Ω : Type*} [MeasurableSpace Ω]
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
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  obtain ⟨ρ, hρ0, hργ, hρ⟩ := inner_radius_sequence hγ
  exact weak_secant_directional_moment_radius_limit hC hUC hFm hG hF x hγ hB hU hCU
    ρ hρ0 hργ hρ hi hb i j hij v k

end LongTails.Proofs.MollifiedSecantMoments
