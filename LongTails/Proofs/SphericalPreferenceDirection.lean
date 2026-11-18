import LongTails.Proofs.WeightedSphericalMoments
import Mathlib.Analysis.Normed.Module.Normalize

open MeasureTheory Set Metric NormedSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SphericalPreferenceDirection

open OracleTemplate.ZerothOrder LongTails.Proofs.WeightedSphericalMoments

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma first_moment_minorant (x : ℝ) : x ^ 2 / 4 - x ^ 4 / 64 ≤ |x| := by
  have hx := abs_nonneg x
  have he : |x| ^ 2 = x ^ 2 := sq_abs _
  rcases le_total |x| 4 with h | h
  · nlinarith only [mul_nonneg hx (sub_nonneg.mpr h), he, sq_nonneg (x ^ 2)]
  · have h₂ : 16 ≤ x ^ 2 := by nlinarith [sq_nonneg (|x| - 4)]
    nlinarith only [hx, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h₂)]

lemma sphere_first_moment_lower (i : Fin d) :
    1 / 8 ≤ Real.sqrt d * ∫ u : S, |(u : H) i| ∂Q := by
  let t := Real.sqrt d
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht₂ : t ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hI := sphere_coordinate_power_integrable (d := d) i
  have h₁ : Integrable (fun u : S => |(u : H) i|) Q := by simpa using (hI 1).abs
  have h := integral_mono
    (((hI 2).const_mul (t ^ 2 / 4)).sub ((hI 4).const_mul (t ^ 4 / 64))) (h₁.const_mul t)
    (fun u : S => by
      have := first_moment_minorant (t * (u : H) i)
      rw [abs_mul, abs_of_nonneg ht] at this
      dsimp
      linarith only [this])
  simp only [Pi.sub_apply] at h
  rw [integral_sub ((hI 2).const_mul _) ((hI 4).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    sphere_coordinate_second_moment] at h
  have h₄ := sphere_even_moment_bound (d := d) i 2
  norm_num at h₄
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  rw [show t ^ 4 = (d : ℝ) ^ 2 by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ht₂],
    ht₂] at h
  have hid : ((d : ℝ) / 4) * (1 / d) = 1 / 4 := by field_simp
  nlinarith only [h, h₄, hid]

noncomputable def bitSign (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

lemma monotone_bitSign : Monotone bitSign := by
  intro a b hab
  unfold bitSign
  split_ifs <;> linarith

lemma bitSign_mul_self (t : ℝ) : bitSign t * t = |t| := by
  unfold bitSign
  split_ifs with ht
  · simp [abs_of_nonneg ht]
  · simp [abs_of_neg (lt_of_not_ge ht)]

lemma measurable_bitSign : Measurable bitSign :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

noncomputable def signedDirection (g : H) (u : S) : H :=
  bitSign ⟪g, (u : H)⟫ • (u : H)

omit [NeZero d] in
lemma measurable_signedDirection (g : H) : Measurable (signedDirection g) := by
  unfold signedDirection
  exact (measurable_bitSign.comp (by fun_prop)).smul measurable_subtype_coe

lemma integrable_signedDirection (g : H) : Integrable (signedDirection g) Q := by
  apply Integrable.of_bound (measurable_signedDirection g).aestronglyMeasurable 1
  filter_upwards [] with u
  have hu := mem_sphere_zero_iff_norm.mp u.property
  simp only [signedDirection, bitSign, norm_smul, Real.norm_eq_abs, hu, mul_one]
  split_ifs <;> norm_num

omit [NeZero d] in
lemma signedDirection_equivariant (U : H ≃ₗᵢ[ℝ] H) (g : H) (u : S) :
    signedDirection (U g) (sphereRotate U u) = U (signedDirection g u) := by
  change bitSign ⟪U g, U (u : H)⟫ • U (u : H) = U (bitSign ⟪g, (u : H)⟫ • (u : H))
  rw [U.inner_map_map, map_smul]

lemma signed_mean_equivariant (U : H ≃ₗᵢ[ℝ] H) (g : H) :
    (∫ u : S, signedDirection (U g) u ∂Q) = U (∫ u : S, signedDirection g u ∂Q) := by
  have hm := (sphereLaw_rotate H U).map_eq
  calc
    _ = ∫ u : S, signedDirection (U g) (sphereRotate U u) ∂Q := by
      rw [← integral_map (measurable_sphereRotate U).aemeasurable
        (measurable_signedDirection (U g)).aestronglyMeasurable, hm]
    _ = _ := by
      simp_rw [signedDirection_equivariant]
      exact U.toLinearIsometry.integral_comp_comm _

lemma signed_mean_parallel (g : H) :
    ∃ c : ℝ, (∫ u : S, signedDirection g u ∂Q) = c • g := by
  let K := ℝ ∙ g
  have hg : K.reflection g = g :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self g)
  have h := signed_mean_equivariant K.reflection g
  rw [hg] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((K.reflection_eq_self_iff _).mp h.symm)
  exact ⟨c, hc.symm⟩

lemma signed_mean_inner (g : H) :
    ⟪g, ∫ u : S, signedDirection g u ∂Q⟫ = ∫ u : S, |⟪g, (u : H)⟫| ∂Q := by
  rw [← integral_inner (𝕜 := ℝ) (integrable_signedDirection g) g]
  apply integral_congr_ae
  filter_upwards [] with u
  exact (real_inner_smul_right _ _ _).trans (bitSign_mul_self _)

noncomputable def angularWeight (d : ℕ) [NeZero d] : ℝ :=
  ∫ u : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, |(u : EuclideanSpace ℝ (Fin d)) 0|
    ∂(sphereLaw (EuclideanSpace ℝ (Fin d)) : Measure _)

lemma signed_mean (g : H) :
    (∫ u : S, signedDirection g u ∂Q) = angularWeight d • normalize g := by
  let e : H := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨c, hc⟩ := signed_mean_parallel e
  have hinner := signed_mean_inner e
  rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq, he] at hinner
  have hce : c = angularWeight d := by
    simpa [e, angularWeight, EuclideanSpace.inner_single_left] using hinner
  rw [hce] at hc
  by_cases hg : g = 0
  · obtain ⟨a, ha⟩ := signed_mean_parallel g
    rw [ha, hg]
    simp
  let U := Submodule.reflection (ℝ ∙ (e - normalize g))ᗮ
  have hU : U e = normalize g := Submodule.reflection_sub (he.trans (norm_normalize hg).symm)
  have hsc (u : S) : signedDirection (normalize g) u = signedDirection g u := by
    simp [signedDirection, NormedSpace.normalize, real_inner_smul_left, bitSign,
      mul_nonneg_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hg))]
  have h := signed_mean_equivariant U e
  simpa only [hU, hsc, hc, map_smul] using h

end LongTails.Proofs.SphericalPreferenceDirection
