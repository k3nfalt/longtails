import LongTails.Proofs.SphericalPreferenceAlignment
import LongTails.Proofs.DirectionalSphericalMoments
import LongTails.Setups.SphericalRandomUtility
import LongTails.Proofs.SphericalPreferenceDirection

open Filter MeasureTheory Metric Set NormedSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SphericalPreferenceTaste

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceAlignment
open OracleTemplate.ZerothOrder

variable {d : ℕ}
local notation "H" => Point d

lemma normalize_bound (x : H) : ‖normalize x‖ ≤ 1 := by
  by_cases h : x = 0
  · simp [h]
  · exact (norm_normalize h).le

lemma measurable_unit : Measurable (normalize : H → H) := by
  unfold NormedSpace.normalize
  fun_prop

lemma integral_rotate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure H} (hs : Spherical μ) (U : H ≃ₗᵢ[ℝ] H) (f : H → F) (hf : Measurable f) :
    (∫ z, f (U z) ∂μ) = ∫ z, f z ∂μ := by
  rw [← integral_map U.continuous.measurable.aemeasurable hf.aestronglyMeasurable, hs U]

lemma spherical_restrict_ball {μ : Measure H} (hs : Spherical μ) (r : ℝ) :
    Spherical (μ.restrict (closedBall 0 r)) := by
  intro U
  have he : U ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext z
    simp
  have hm := Measure.restrict_map (μ := μ) U.continuous.measurable
    (s := closedBall 0 r) measurableSet_closedBall
  rw [hs U, he] at hm
  exact hm.symm

lemma normalize_map (U : H ≃ₗᵢ[ℝ] H) (x : H) :
    normalize (U x) = U (normalize x) := by simp [NormedSpace.normalize]

lemma normalized_integral_zero {μ : Measure H} (hs : Spherical μ) :
    (∫ z, normalize z ∂μ) = (0 : H) := by
  have he := integral_rotate hs (LinearIsometryEquiv.neg ℝ : H ≃ₗᵢ[ℝ] H) normalize measurable_unit
  change (∫ z, normalize (-z) ∂μ) = _ at he
  simp_rw [normalize_neg, integral_neg] at he
  have htwo : (2 : ℝ) • (∫ z, normalize z ∂μ) = (0 : H) := by
    rw [two_smul]
    nth_rw 1 [← he]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

noncomputable def tasteMean (μ : Measure H) (g : H) : H := ∫ z, normalize (g + z) ∂μ

lemma tasteMean_rotate {μ : Measure H} (hs : Spherical μ) (U : H ≃ₗᵢ[ℝ] H) (g : H) :
    tasteMean μ (U g) = U (tasteMean μ g) := by
  unfold tasteMean
  rw [← integral_rotate hs U (fun z => normalize (U g + z))
    (measurable_unit.comp (measurable_const.add measurable_id))]
  simp_rw [← map_add, normalize_map]
  exact U.toLinearIsometry.integral_comp_comm _

lemma tasteMean_parallel {μ : Measure H} (hs : Spherical μ) (g : H) :
    ∃ c : ℝ, tasteMean μ g = c • g := by
  let K := ℝ ∙ g
  have hg : K.reflection g = g :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self g)
  have h := tasteMean_rotate hs K.reflection g
  rw [hg] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((K.reflection_eq_self_iff _).mp h.symm)
  exact ⟨c, hc.symm⟩

lemma projected_square_rotate {μ : Measure H} (hs : Spherical μ) (U : H ≃ₗᵢ[ℝ] H) (g : H) :
    (∫ z, ⟪U g, normalize z⟫ ^ 2 ∂μ) = ∫ z, ⟪g, normalize z⟫ ^ 2 ∂μ := by
  rw [← integral_rotate hs U (fun z => ⟪U g, normalize z⟫ ^ 2)
    (by have hm := measurable_unit (d := d); fun_prop)]
  simp only [normalize_map, U.inner_map_map]

lemma projected_square_bound [NeZero d] {μ : Measure H} [IsFiniteMeasure μ]
    (hs : Spherical μ) (g : H) :
    (∫ z, ⟪g, normalize z⟫ ^ 2 ∂μ) ≤ ‖g‖ ^ 2 / d * μ.real univ := by
  let S := sphere (0 : H) 1
  let Q : Measure S := sphereLaw H
  obtain ⟨v, hv, hgv⟩ := LongTails.Proofs.DirectionalSphericalMoments.unit_direction_representation 0 g
  have he (u : S) :
      (∫ z, ⟪(u : H), normalize z⟫ ^ 2 ∂μ) = ∫ z, ⟪v, normalize z⟫ ^ 2 ∂μ := by
    have hn : ‖v‖ = ‖(u : H)‖ := hv.trans (mem_sphere_zero_iff_norm.mp u.property).symm
    let U := Submodule.reflection (ℝ ∙ (v - (u : H)))ᗮ
    have hU : U v = (u : H) := Submodule.reflection_sub hn
    simpa only [hU] using projected_square_rotate hs U v
  have hI : Integrable (fun q : S × H => ⟪(q.1 : H), normalize q.2⟫ ^ 2) (Q.prod μ) := by
    apply Integrable.of_bound (by
      have hm := measurable_unit (d := d)
      fun_prop) 1
    filter_upwards [] with q
    have hle := abs_real_inner_le_norm (q.1 : H) (normalize q.2)
    rw [mem_sphere_zero_iff_norm.mp q.1.property, one_mul] at hle
    rw [Real.norm_eq_abs, abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (hle.trans (normalize_bound _)) 2
  have huv : (∫ z, ⟪v, normalize z⟫ ^ 2 ∂μ) = ∫ z, ‖normalize z‖ ^ 2 / d ∂μ := by
    calc
      _ = ∫ u : S, ∫ z, ⟪(u : H), normalize z⟫ ^ 2 ∂μ ∂Q := by simp_rw [he]; simp [Q]
      _ = ∫ z, ∫ u : S, ⟪(u : H), normalize z⟫ ^ 2 ∂Q ∂μ := integral_integral_swap hI
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simpa only [real_inner_comm (normalize z)] using sphere_projection_second_moment (normalize z)
  have hbound : (∫ z, ‖normalize z‖ ^ 2 / d ∂μ) ≤ (1 / (d : ℝ)) * μ.real univ := by
    have hi : Integrable (fun z : H => ‖normalize z‖ ^ 2 / d) μ := by
      apply Integrable.of_bound (by
        have hm := measurable_unit (d := d)
        fun_prop) (1 / (d : ℝ))
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (by
        simpa using pow_le_pow_left₀ (norm_nonneg _) (normalize_bound z) 2) (Nat.cast_nonneg _)
    have h := integral_mono hi (integrable_const (1 / (d : ℝ))) (fun z => by
      gcongr
      simpa using pow_le_pow_left₀ (norm_nonneg _) (normalize_bound z) 2)
    simpa [mul_comm, smul_eq_mul] using h
  calc
    _ = ‖g‖ ^ 2 * ∫ z, ⟪v, normalize z⟫ ^ 2 ∂μ := by
      conv_lhs => arg 2; intro z; rw [hgv, real_inner_smul_left, mul_pow]
      rw [integral_const_mul]
    _ ≤ _ := by rw [huv]; nlinarith only [mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖g‖),
      show ‖g‖ ^ 2 * ((1 / (d : ℝ)) * μ.real univ) = ‖g‖ ^ 2 / d * μ.real univ by ring]

lemma self_unit (z : H) : ⟪z, normalize z⟫ = ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [NormedSpace.normalize, real_inner_smul_right, pow_two, norm_ne_zero_iff.mpr hz]

lemma normalization_monotone (g z : H) :
    0 ≤ ⟪g, normalize (g + z) - normalize z⟫ := by
  let w := g + z
  have h (u v : H) : ⟪u, normalize v⟫ ≤ ‖u‖ := by
    exact (real_inner_le_norm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (normalize_bound v) (norm_nonneg u))
  change 0 ≤ ⟪g, normalize w - normalize z⟫
  nth_rw 1 [show g = w - z by simp [w]]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, self_unit, self_unit]
  linarith only [h w z, h z w]

lemma quantile_pointwise (g z : H) {B : ℝ} (hB : 0 ≤ B) (hz : ‖z‖ ≤ 2 * B) :
    ‖g‖ ^ 2 - ⟪g, normalize z⟫ ^ 2 ≤
      2 * (‖g‖ + 2 * B) * ⟪g, normalize (g + z) - normalize z⟫ := by
  by_cases he : z = 0
  · subst z
    simp only [normalize_zero_eq_zero, inner_zero_right, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero, add_zero, self_unit]
    nlinarith only [mul_nonneg (norm_nonneg g) hB, sq_nonneg ‖g‖]
  have h := radial_alignment g (normalize z) (norm_normalize he) (norm_nonneg z)
  rw [norm_smul_normalize] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (normalization_monotone g z))

lemma unit_integrable {μ : Measure H} [IsFiniteMeasure μ] (g : H) :
    Integrable (fun z => normalize (g+z)) μ :=
  Integrable.of_bound (measurable_unit.comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall fun z => normalize_bound (g+z))

lemma tasteMean_lower [NeZero d] {μ : Measure H} [IsProbabilityMeasure μ]
    (hs : Spherical μ) {B : ℝ} (hB : 0 < B) (hd : 2 ≤ d)
    (hq : 1 / 2 ≤ μ.real (closedBall 0 (2*B))) (g : H) (hg : ‖g‖ ≤ B) :
    ‖g‖ ^ 2 ≤ (24 * B) * ⟪g, tasteMean μ g⟫ := by
  let C : Set H := closedBall 0 (2*B)
  let D := fun z : H => ⟪g, normalize (g+z) - normalize z⟫
  have h0 : Integrable (normalize : H → H) μ := by simpa using unit_integrable (μ := μ) (0:H)
  have hD : Integrable D μ := ((unit_integrable g).sub h0).const_inner g
  have hD0 (z : H) : 0 ≤ D z := normalization_monotone g z
  have hmean : (∫ z, D z ∂μ) = ⟪g, tasteMean μ g⟫ := by
    dsimp [D, tasteMean]
    rw [← integral_inner (𝕜 := ℝ) (unit_integrable g) g]
    simp_rw [inner_sub_right]
    rw [integral_sub ((unit_integrable g).const_inner g) (h0.const_inner g), integral_inner (𝕜 := ℝ) h0 g,
      normalized_integral_zero hs, inner_zero_right, sub_zero]
  have hsqI : Integrable (fun z : H => ⟪g, normalize z⟫^2) (μ.restrict C) := by
    apply Integrable.of_bound (by have hm := measurable_unit (d := d); fun_prop) (‖g‖^2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (abs_real_inner_le_norm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (normalize_bound z) (norm_nonneg g))
  have hsq := projected_square_bound (spherical_restrict_ball hs (2*B)) g
  have hmC : (μ.restrict C).real univ = μ.real C := by simp [measureReal_def]
  rw [hmC] at hsq
  have hrest := integral_mono_ae ((integrable_const (‖g‖ ^ 2)).sub hsqI)
    (hD.restrict.const_mul (2 * (‖g‖ + 2*B))) (by
      filter_upwards [ae_restrict_mem (μ := μ) (s := C) measurableSet_closedBall] with z hz
      exact quantile_pointwise g z hB.le (mem_closedBall_zero_iff.mp hz))
  simp only [Pi.sub_apply] at hrest
  rw [integral_sub (integrable_const _) hsqI, integral_const, hmC, smul_eq_mul,
    integral_const_mul] at hrest
  have hfull : (∫ z in C, D z ∂μ) ≤ ⟪g, tasteMean μ g⟫ :=
    (setIntegral_le_integral hD (Filter.Eventually.of_forall hD0)).trans_eq hmean
  have hn : 0 ≤ ⟪g, tasteMean μ g⟫ := hmean ▸ integral_nonneg hD0
  have hsimp : ‖g‖ ^ 2 / d ≤ ‖g‖ ^ 2 / 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    exact_mod_cast hd
  have hq' : 1 / 2 ≤ μ.real C := hq
  nlinarith only [hrest, hsq, mul_le_mul_of_nonneg_right hsimp (measureReal_nonneg (μ := μ) (s := C)),
    mul_le_mul_of_nonneg_right hq' (sq_nonneg ‖g‖),
    mul_le_mul_of_nonneg_left hfull (show 0 ≤ 2 * (‖g‖ + 2*B) by positivity),
    mul_le_mul_of_nonneg_right hg hn]

lemma expected_direction_gain [NeZero d] {μ : Measure H} [IsProbabilityMeasure μ]
    (hs : Spherical μ) {B : ℝ} (hB : 0 < B) (hd : 2 ≤ d)
    (hq : 1 / 2 ≤ μ.real (closedBall 0 (2 * B))) (g v : H) (hg : ‖g‖ ≤ B)
    {gap : ℝ} (hgap : 0 ≤ gap) (hsupp : gap ≤ ⟪g, v⟫) :
    gap / (192 * B * Real.sqrt d) ≤
      ⟪LongTails.Proofs.SphericalPreferenceDirection.angularWeight d • tasteMean μ g, v⟫ := by
  obtain ⟨c, hc⟩ := tasteMean_parallel hs g
  rw [hc, real_inner_smul_left, real_inner_smul_left]
  have hdim : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
  by_cases hz : g = 0
  · simp [hz] at hsupp ⊢
    rw [le_antisymm hsupp hgap]
    simp
  have hl := tasteMean_lower hs hB hd hq g hg
  rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq] at hl
  have hnorm : 0 < ‖g‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) _
  have hfactor : 1 ≤ 24 * B * c := by
    apply le_of_mul_le_mul_right _ hnorm
    linarith only [show ‖g‖^2 ≤ (24 * B * c) * ‖g‖^2 by simpa only [mul_assoc] using hl]
  have ha := LongTails.Proofs.SphericalPreferenceDirection.sphere_first_moment_lower (0 : Fin d)
  change 1 / 8 ≤ Real.sqrt d * LongTails.Proofs.SphericalPreferenceDirection.angularWeight d at ha
  have hc0 : 0 ≤ c := by by_contra! h; nlinarith [mul_neg_of_pos_of_neg hB h]
  have ha0 : 0 ≤ LongTails.Proofs.SphericalPreferenceDirection.angularWeight d := integral_nonneg fun _ => abs_nonneg _
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    gap ≤ (24 * B * c) * gap := by simpa using mul_le_mul_of_nonneg_right hfactor hgap
    _ ≤ (8 * (Real.sqrt d * LongTails.Proofs.SphericalPreferenceDirection.angularWeight d)) *
        ((24 * B * c) * gap) := by
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ 8 * (Real.sqrt d *
        LongTails.Proofs.SphericalPreferenceDirection.angularWeight d) by linarith) (by positivity : 0 ≤ (24 * B * c) * gap)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hsupp (show 0 ≤
        192 * B * Real.sqrt d * LongTails.Proofs.SphericalPreferenceDirection.angularWeight d * c by positivity)
      ring_nf at hh ⊢
      exact hh

end LongTails.Proofs.SphericalPreferenceTaste
