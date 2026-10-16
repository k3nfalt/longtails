import LongTails.Proofs.SphericalSecantMoments

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.DirectionalSphericalMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma isometry_precomp_gradient {a : E → ℝ} {g : E → E}
    (hd : ∀ x, HasGradientAt a (g x) x) (R : E ≃ₗᵢ[ℝ] E) (x : E) :
    HasGradientAt (fun y => a (R y)) (R.symm (g (R x))) x := by
  have h := (hd (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext v
    change ⟪R.symm (g (R x)), v⟫ = ⟪g (R x), R v⟫
    simpa only [R.apply_symm_apply] using (R.inner_map_map (R.symm (g (R x))) v).symm

section Spherical

open OracleTemplate.ZerothOrder LongTails.Proofs.SphericalSecantMoments

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

omit [NeZero d] in
lemma sphere_rotation_embedding (R : H ≃ₗᵢ[ℝ] H) : MeasurableEmbedding (sphereRotate R) := by
  have hi : Isometry (sphereRotate R) := by
    intro u v
    change edist (R (u : H)) (R (v : H)) = edist (u : H) (v : H)
    exact R.isometry _ _
  exact hi.isClosedEmbedding.measurableEmbedding

lemma sphere_sample_rotation_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (R : H ≃ₗᵢ[ℝ] H) (f : S × Ω → ℝ) :
    (∫ z : S × Ω, f (sphereRotate R z.1, z.2) ∂(Q).prod P) = ∫ z, f z ∂(Q).prod P := by
  have hmp := (sphereLaw_rotate H R).prod (MeasurePreserving.id P)
  exact hmp.integral_comp ((sphere_rotation_embedding R).prodMap MeasurableEmbedding.id) f

lemma sphere_sample_rotation_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (R : H ≃ₗᵢ[ℝ] H) (f : S × Ω → ℝ) :
    Integrable (fun z : S × Ω => f (sphereRotate R z.1, z.2)) ((Q).prod P) ↔
      Integrable f ((Q).prod P) := by
  have hmp := (sphereLaw_rotate H R).prod (MeasurePreserving.id P)
  exact hmp.integrable_comp_emb ((sphere_rotation_embedding R).prodMap MeasurableEmbedding.id)

lemma rotated_coordinate_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (ha : Measurable (fun z : S × Ω => a z.1 z.2))
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x) ∧
      (∀ x, a (-x) ξ = -a x ξ))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (R : H ≃ₗᵢ[ℝ] H) (k : ℕ) :
    Integrable (fun z : S × Ω => a z.1 z.2 ^ 2 *
      ⟪(z.1 : H), R (EuclideanSpace.single i 1)⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω, a z.1 z.2 ^ 2 *
        ⟪(z.1 : H), R (EuclideanSpace.single i 1)⟫ ^ (2 * k) ∂(Q).prod P) ≤
          5 * 8 ^ k * (k.factorial : ℝ) * B := by
  let ar := fun x ξ => a (R x) ξ
  let gr := fun x ξ => R.symm (g (R x) ξ)
  have hm : Measurable (fun z : S × Ω => (sphereRotate R z.1, z.2)) :=
    ((measurable_sphereRotate R).comp measurable_fst).prodMk measurable_snd
  have har : Measurable (fun z : S × Ω => ar z.1 z.2) := ha.comp hm
  have hgr : Measurable (fun z : S × Ω => gr z.1 z.2) := R.symm.continuous.measurable.comp (hg.comp hm)
  have hsr : ∀ᵐ ξ ∂P, Continuous (fun x => gr x ξ) ∧
      (∀ x, HasGradientAt (fun y => ar y ξ) (gr x ξ) x) ∧
      (∀ x, ar (-x) ξ = -ar x ξ) := by
    filter_upwards [hs] with ξ hξ
    refine ⟨R.symm.continuous.comp (hξ.1.comp R.continuous), ?_, ?_⟩
    · exact fun x => isometry_precomp_gradient hξ.2.1 R x
    · intro x
      dsimp [ar]
      rw [map_neg, hξ.2.2]
  have hir : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖gr u ξ‖ ^ 2) P := by
    filter_upwards [(sphereLaw_rotate H R).quasiMeasurePreserving.ae hi] with u hu
    simpa only [gr, sphereRotate, R.symm.norm_map] using hu
  have hbr : ∀ᵐ u : S ∂Q, (∫ ξ, ‖gr u ξ‖ ^ 2 ∂P) ≤ B := by
    filter_upwards [(sphereLaw_rotate H R).quasiMeasurePreserving.ae hb] with u hu
    simpa only [gr, sphereRotate, R.symm.norm_map] using hu
  have h := stochastic_weighted_moment_bound har hgr hsr hB hir hbr i j hij k
  let f := fun z : S × Ω => a z.1 z.2 ^ 2 * ⟪(z.1 : H), R (EuclideanSpace.single i 1)⟫ ^ (2 * k)
  have he : (fun z : S × Ω => f (sphereRotate R z.1, z.2)) =
      fun z : S × Ω => ar z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * k) := by
    funext z
    dsimp [f, ar, sphereRotate]
    rw [R.inner_map_map]
    simp [PiLp.inner_apply]
  have hfi : Integrable f ((Q).prod P) := (sphere_sample_rotation_integrable R f).mp (by rw [he]; exact h.1)
  refine ⟨hfi, ?_⟩
  have heq := sphere_sample_rotation_integral (P := P) R f
  rw [he] at heq
  change (d : ℝ) ^ (k + 1) * (∫ z, f z ∂(Q).prod P) ≤ _
  rw [← heq]
  exact h.2

lemma unit_direction_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (ha : Measurable (fun z : S × Ω => a z.1 z.2))
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x) ∧
      (∀ x, a (-x) ξ = -a x ξ))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (hv : ‖v‖ = 1) (k : ℕ) :
    Integrable (fun z : S × Ω => a z.1 z.2 ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω, a z.1 z.2 ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤
        5 * 8 ^ k * (k.factorial : ℝ) * B := by
  let e : H := EuclideanSpace.single i 1
  let R := Submodule.reflection (ℝ ∙ (e - v))ᗮ
  have hRv : R e = v := Submodule.reflection_sub (by simp [e, hv])
  have h := rotated_coordinate_moment_bound ha hg hs hB hi hb i j hij R k
  have hRv' : R (EuclideanSpace.single i 1) = v := hRv
  simpa only [hRv'] using h

omit [NeZero d] in
lemma unit_direction_representation (i : Fin d) (v : H) :
    ∃ w : H, ‖w‖ = 1 ∧ v = ‖v‖ • w := by
  by_cases hv : v = 0
  · refine ⟨EuclideanSpace.single i 1, by simp, ?_⟩
    simp [hv]
  · refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

lemma directional_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (ha : Measurable (fun z : S × Ω => a z.1 z.2))
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x) ∧
      (∀ x, a (-x) ξ = -a x ξ))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω => a z.1 z.2 ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω, a z.1 z.2 ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤
        5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  obtain ⟨w, hw, hv⟩ := unit_direction_representation i v
  have h := unit_direction_moment_bound ha hg hs hB hi hb i j hij w hw k
  have he : (fun z : S × Ω => a z.1 z.2 ^ 2 * ⟪(z.1 : H), v⟫ ^ (2 * k)) =
      fun z : S × Ω => ‖v‖ ^ (2 * k) * (a z.1 z.2 ^ 2 * ⟪(z.1 : H), w⟫ ^ (2 * k)) := by
    funext z
    conv_lhs => rw [hv, real_inner_smul_right, mul_pow]
    ring
  rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hn : 0 ≤ ‖v‖ ^ (2 * k) := pow_nonneg (norm_nonneg _) _
  have hh := mul_le_mul_of_nonneg_right h.2 hn
  nlinarith only [hh]

lemma smooth_secant_directional_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    (hF : Measurable F) (hG : Measurable G)
    (hs : ∀ᵐ ξ ∂P, Continuous (fun y => G (y, ξ)) ∧
      ∀ y, HasGradientAt (fun z => F (z, ξ)) (G (y, ξ)) y)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖G (x + γ • (u : H), ξ)‖ ^ 2) P ∧
      Integrable (fun ξ => ‖G (x - γ • (u : H), ξ)‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖G (x + γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B ∧
      (∫ ξ, ‖G (x - γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (v : H) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        ⟪(z.1 : H), v⟫ ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          ⟪(z.1 : H), v⟫ ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B * ‖v‖ ^ (2 * k) := by
  have h := smooth_secant_fields hF hG hs x hγ hi hb
  exact directional_moment_bound h.1 h.2.1 h.2.2.1 hB h.2.2.2.1 h.2.2.2.2 i j hij v k

end Spherical

end LongTails.Proofs.DirectionalSphericalMoments
