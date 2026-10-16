import LongTails.Algorithms.ClippedTwoPoint
import LongTails.Proofs.ClippedSphericalMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClippedVectorMoments

open LongTails.Algorithms.ClippedTwoPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma direction_estimate_norm (d : ℕ) (τ a : ℝ) (u : E) :
    ‖directionEstimate d τ u a‖ = (d : ℝ) * |OracleTemplate.clip τ a| * ‖u‖ := by
  simp only [directionEstimate, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d)]

lemma direction_estimate_norm_le (d : ℕ) {τ : ℝ} (hτ : 0 ≤ τ)
    (a : ℝ) (u : E) (hu : ‖u‖ = 1) : ‖directionEstimate d τ u a‖ ≤ (d : ℝ) * τ := by
  rw [direction_estimate_norm, hu, mul_one]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  simpa only [Real.norm_eq_abs] using OracleTemplate.norm_clip_le hτ a

lemma direction_estimate_inner (d : ℕ) (τ a : ℝ) (u v : E) :
    ⟪directionEstimate d τ u a, v⟫ = (d : ℝ) * OracleTemplate.clip τ a * ⟪u, v⟫ := by
  simp only [directionEstimate, real_inner_smul_left]

lemma direction_estimate_measurable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : Ω → E} {a : Ω → ℝ} (hu : Measurable u) (ha : Measurable a) (d : ℕ) (τ : ℝ) :
    Measurable (fun z => directionEstimate d τ (u z) (a z)) := by
  exact (((OracleTemplate.measurable_clip τ).comp ha).const_mul (d : ℝ)).smul hu

lemma direction_estimate_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hunit : ∀ z, ‖u z‖ = 1)
    (d : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun z => directionEstimate d τ (u z) (a z)) P ∧
      Integrable (fun z => ‖directionEstimate d τ (u z) (a z)‖ ^ 2) P := by
  have hm := direction_estimate_measurable hu ha d τ
  have hb := fun z => direction_estimate_norm_le d hτ (a z) (u z) (hunit z)
  refine ⟨Integrable.mono' (integrable_const ((d : ℝ) * τ)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hb), ?_⟩
  apply Integrable.mono' (integrable_const (((d : ℝ) * τ) ^ 2)) (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2

lemma centered_direction_estimate_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a : Ω → ℝ}
    (hunit : ∀ z, ‖u z‖ = 1) (d : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (z : Ω) :
    ‖directionEstimate d τ (u z) (a z) - ∫ w, directionEstimate d τ (u w) (a w) ∂P‖ ≤
      2 * (d : ℝ) * τ := by
  have hb := fun w => direction_estimate_norm_le d hτ (a w) (u w) (hunit w)
  have hi : ‖∫ w, directionEstimate d τ (u w) (a w) ∂P‖ ≤ (d : ℝ) * τ := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := P) (Filter.Eventually.of_forall hb)
  have hh := norm_sub_le (directionEstimate d τ (u z) (a z))
    (∫ w, directionEstimate d τ (u w) (a w) ∂P)
  nlinarith only [hh, hb z, hi]


lemma perturbed_direction_estimate_square_le (d : ℕ) {τ h : ℝ} (hτ : 0 ≤ τ)
    (a c : ℝ) (hc : |c| ≤ h) (u : E) (hu : ‖u‖ = 1) :
    ‖directionEstimate d τ u (a + c)‖ ^ 2 ≤ 2 * (d : ℝ) ^ 2 * a ^ 2 + 2 * (d : ℝ) ^ 2 * h ^ 2 := by
  have hclip : |OracleTemplate.clip τ (a + c)| ≤ |a + c| := by
    simpa only [Real.norm_eq_abs] using ScalarClippedMoments.clipped_norm_le_input hτ (a + c)
  have hclip2 := pow_le_pow_left₀ (abs_nonneg _) hclip 2
  have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
  simp only [sq_abs] at hclip2 hc2
  rw [direction_estimate_norm, hu, mul_one, mul_pow, sq_abs]
  have h1 := mul_le_mul_of_nonneg_left hclip2 (sq_nonneg (d : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg (d : ℝ))
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg (a - c))]

lemma perturbed_direction_estimate_trace {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a c : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hc : Measurable c) (hunit : ∀ z, ‖u z‖ = 1)
    (d : ℕ) {τ B h : ℝ} (hτ : 0 ≤ τ) (hcb : ∀ z, |c z| ≤ h)
    (hai : Integrable (fun z => a z ^ 2) P)
    (hab : (d : ℝ) * (∫ z, a z ^ 2 ∂P) ≤ 5 * B) :
    Integrable (fun z => ‖directionEstimate d τ (u z) (a z + c z)‖ ^ 2) P ∧
      (∫ z, ‖directionEstimate d τ (u z) (a z + c z)‖ ^ 2 ∂P) ≤
        10 * (d : ℝ) * (B + d * h ^ 2) := by
  have hi := (direction_estimate_integrable (P := P) hu (ha.add hc) hunit d hτ).2
  have hbound : Integrable (fun z => 2 * (d : ℝ) ^ 2 * a z ^ 2 + 2 * (d : ℝ) ^ 2 * h ^ 2) P :=
    (hai.const_mul _).add (integrable_const _)
  have hh := integral_mono hi hbound
    (fun z => perturbed_direction_estimate_square_le d hτ (a z) (c z) (hcb z) (u z) (hunit z))
  rw [integral_add (hai.const_mul _) (integrable_const _), integral_const_mul] at hh
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  simp only [Pi.add_apply] at hh
  have hscaled := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg d)
  refine ⟨hi, ?_⟩
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg h)]


lemma perturbed_centered_direction_estimate_trace {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a c : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hc : Measurable c) (hunit : ∀ z, ‖u z‖ = 1)
    (d : ℕ) {τ B h : ℝ} (hτ : 0 ≤ τ) (hcb : ∀ z, |c z| ≤ h)
    (hai : Integrable (fun z => a z ^ 2) P)
    (hab : (d : ℝ) * (∫ z, a z ^ 2 ∂P) ≤ 5 * B) :
    let G := fun z => directionEstimate d τ (u z) (a z + c z)
    Integrable (fun z => ‖G z - ∫ w, G w ∂P‖ ^ 2) P ∧
      (∫ z, ‖G z - ∫ w, G w ∂P‖ ^ 2 ∂P) ≤ 10 * (d : ℝ) * (B + d * h ^ 2) := by
  have hG := direction_estimate_integrable (P := P) hu (ha.add hc) hunit d hτ
  have ht := perturbed_direction_estimate_trace hu ha hc hunit d hτ hcb hai hab
  have hv := ScalarClippedMoments.centered_vector_second_moment hG.1 hG.2
  exact ⟨hv.1, hv.2.trans ht.2⟩

lemma centered_direction_estimate_inner {Ω : Type*} [MeasurableSpace Ω] [CompleteSpace E]
    {P : Measure Ω} {u : Ω → E} {a : Ω → ℝ} (d : ℕ) (τ : ℝ)
    (hi : Integrable (fun z => directionEstimate d τ (u z) (a z)) P) (v : E) (z : Ω) :
    ⟪v, directionEstimate d τ (u z) (a z) - ∫ w, directionEstimate d τ (u w) (a w) ∂P⟫ =
      (d : ℝ) * OracleTemplate.clip τ (a z) * ⟪u z, v⟫ -
        ∫ w, (d : ℝ) * OracleTemplate.clip τ (a w) * ⟪u w, v⟫ ∂P := by
  have he (w : Ω) : ⟪v, directionEstimate d τ (u w) (a w)⟫ =
      (d : ℝ) * OracleTemplate.clip τ (a w) * ⟪u w, v⟫ := by
    rw [real_inner_comm, direction_estimate_inner]
  rw [inner_sub_right, ← integral_inner hi v]
  simp only [he]


lemma spherical_centered_direction_mgf {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a c : (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) × Ω → ℝ} {τ B h θ : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hcb : ∀ z, |c z| ≤ h) (v : EuclideanSpace ℝ (Fin d))
    (hm : ∀ k : ℕ,
      Integrable (fun z => a z ^ 2 * ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ (2 * (k + 1)))
        ((OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P) ∧
      (d : ℝ) ^ (k + 2) * (∫ z, a z ^ 2 * ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ (2 * (k + 1))
        ∂(OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P) ≤
        5 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * ‖v‖ ^ (2 * (k + 1)))
    (hsmall : 256 * |θ| * (Real.sqrt d * τ * ‖v‖) < 1) :
    let Q := (OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P
    let G := fun z => directionEstimate d τ (z.1 : EuclideanSpace ℝ (Fin d)) (a z + c z)
    Integrable (fun z => Real.exp (θ * ⟪v, G z - ∫ w, G w ∂Q⟫)) Q ∧
      (∫ z, Real.exp (θ * ⟪v, G z - ∫ w, G w ∂Q⟫) ∂Q) ≤
        Real.exp (131072 * ((B + d * h ^ 2) * ‖v‖ ^ 2) * θ ^ 2 /
          (1 - 256 * |θ| * (Real.sqrt d * τ * ‖v‖))) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let Q := (OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P
  have hu : Measurable (fun z : S × Ω => (z.1 : EuclideanSpace ℝ (Fin d))) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hunit : ∀ z : S × Ω, ‖(z.1 : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    intro z
    simpa only [S, mem_sphere_iff_norm, sub_zero] using z.1.property
  have hG := (direction_estimate_integrable (P := Q) hu (ha.add hc) hunit d hτ).1
  have hh := ClippedSphericalMoments.clipped_direction_centered_mgf ha hc hτ hB hcb v hm hsmall
  have he (z : S × Ω) := centered_direction_estimate_inner d τ hG v z
  simp only [Pi.add_apply] at he
  dsimp only
  dsimp only [Q, S] at he
  simp_rw [he]
  exact hh


lemma norm_le_unit_direction_bound (x : E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v : E, ‖v‖ = 1 → |⟪v, x⟫| ≤ C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa only [hx, norm_zero] using hC
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hn.ne']
  have hi : ⟪‖x‖⁻¹ • x, x⟫ = ‖x‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hh := hbound (‖x‖⁻¹ • x) hv
  simpa only [hi, abs_of_nonneg (norm_nonneg x)] using hh

lemma raw_direction_integrable {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hunit : ∀ z, ‖u z‖ = 1)
    (hai : Integrable (fun z => a z ^ 2) P) (d : ℕ) :
    Integrable (fun z => ((d : ℝ) * a z) • u z) P := by
  have ha1 : Integrable a P := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    ((memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr hai)
  have hdom : Integrable (fun z => (d : ℝ) * |a z|) P := by
    simpa only [Real.norm_eq_abs] using ha1.norm.const_mul (d : ℝ)
  apply hdom.mono' ((ha.const_mul (d : ℝ)).smul hu).aestronglyMeasurable
  filter_upwards [] with z
  change ‖((d : ℝ) * a z) • u z‖ ≤ (d : ℝ) * |a z|
  simp only [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d), hunit z, mul_one, le_refl]

lemma clean_direction_estimate_bias {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hunit : ∀ z, ‖u z‖ = 1)
    {d : ℕ} [NeZero d] {τ B : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hai : Integrable (fun z => a z ^ 2) P)
    (hab : (d : ℝ) * (∫ z, a z ^ 2 ∂P) ≤ 5 * B)
    (hw : ∀ v : E, ‖v‖ = 1 →
      Integrable (fun z => a z ^ 2 * ⟪u z, v⟫ ^ 2) P ∧
        (d : ℝ) ^ 2 * (∫ z, a z ^ 2 * ⟪u z, v⟫ ^ 2 ∂P) ≤ 40 * B) :
    ‖(∫ z, directionEstimate d τ (u z) (a z) ∂P) - (∫ z, ((d : ℝ) * a z) • u z ∂P)‖ ≤
      15 * B / (Real.sqrt d * τ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hraw := raw_direction_integrable hu ha hunit hai d
  have hclip := (direction_estimate_integrable (P := P) hu ha hunit d hτ.le).1
  apply norm_le_unit_direction_bound _ (by positivity)
  intro v hv
  have hwi := hw v hv
  have hh := ScalarClippedMoments.scalar_clipping_weighted_bias ha (hu.inner measurable_const)
    hd hτ hB hai hwi.1 hab hwi.2
  have heq : (fun z => ⟪v, directionEstimate d τ (u z) (a z) - ((d : ℝ) * a z) • u z⟫) =
      fun z => (d : ℝ) * ((OracleTemplate.clip τ (a z) - a z) * ⟪u z, v⟫) := by
    funext z
    simp only [directionEstimate, inner_sub_right, real_inner_smul_right, real_inner_comm v (u z)]
    ring
  have hdiff : Integrable (fun z => directionEstimate d τ (u z) (a z) - ((d : ℝ) * a z) • u z) P := hclip.sub hraw
  rw [← integral_sub hclip hraw, ← integral_inner hdiff v]
  rw [heq, integral_const_mul, abs_mul, abs_of_nonneg hd.le]
  exact hh.2

lemma perturbed_direction_estimate_mean_difference {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {u : Ω → E} {a c : Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (hc : Measurable c) (hunit : ∀ z, ‖u z‖ = 1)
    {d : ℕ} [NeZero d] {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h)
    (hcb : ∀ z, |c z| ≤ h)
    (hw : ∀ v : E, ‖v‖ = 1 →
      Integrable (fun z => ⟪u z, v⟫ ^ 2) P ∧
        (d : ℝ) * (∫ z, ⟪u z, v⟫ ^ 2 ∂P) ≤ 1) :
    ‖(∫ z, directionEstimate d τ (u z) (a z + c z) ∂P) -
      (∫ z, directionEstimate d τ (u z) (a z) ∂P)‖ ≤ Real.sqrt d * h := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hclean := (direction_estimate_integrable (P := P) hu ha hunit d hτ).1
  have hpert : Integrable (fun z => directionEstimate d τ (u z) (a z + c z)) P :=
    (direction_estimate_integrable (P := P) hu (ha.add hc) hunit d hτ).1
  apply norm_le_unit_direction_bound _ (by positivity)
  intro v hv
  have he : Measurable (fun z => OracleTemplate.clip τ (a z + c z) - OracleTemplate.clip τ (a z)) :=
    ((OracleTemplate.measurable_clip τ).comp (ha.add hc)).sub
      ((OracleTemplate.measurable_clip τ).comp ha)
  have heb (z : Ω) : |OracleTemplate.clip τ (a z + c z) - OracleTemplate.clip τ (a z)| ≤ h := by
    have hb := ScalarClippedMoments.scalar_clip_difference hτ (a z + c z) (a z)
    simp only [add_sub_cancel_left] at hb
    exact hb.trans (hcb z)
  have hb := ScalarClippedMoments.bounded_directional_bias he (hu.inner measurable_const)
    hd hh heb (hw v hv).1 (hw v hv).2
  have hdiff : Integrable (fun z => directionEstimate d τ (u z) (a z + c z) -
      directionEstimate d τ (u z) (a z)) P := hpert.sub hclean
  have heq : (fun z => ⟪v, directionEstimate d τ (u z) (a z + c z) -
      directionEstimate d τ (u z) (a z)⟫) = fun z => (d : ℝ) *
        ((OracleTemplate.clip τ (a z + c z) - OracleTemplate.clip τ (a z)) * ⟪u z, v⟫) := by
    funext z
    simp only [directionEstimate, inner_sub_right, real_inner_smul_right, real_inner_comm v (u z)]
    ring
  rw [← integral_sub hpert hclean, ← integral_inner hdiff v, heq, integral_const_mul,
    abs_mul, abs_of_nonneg hd.le]
  exact hb.2

lemma spherical_product_covariance {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (v : EuclideanSpace ℝ (Fin d)) :
    let Q := (OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P
    Integrable (fun z => ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ 2) Q ∧
      (d : ℝ) * (∫ z, ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ 2 ∂Q) = ‖v‖ ^ 2 := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let Q := (OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure
  have hs : Integrable (fun u : S => ⟪(u : EuclideanSpace ℝ (Fin d)), v⟫ ^ 2) Q := by
    simpa only [mul_one] using (ClippedSphericalMoments.sphere_direction_even_moment v 1).1
  have hi : Integrable (fun z : S × Ω => ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ 2) (Q.prod P) :=
    hs.comp_fst P
  refine ⟨hi, ?_⟩
  change (d : ℝ) * (∫ z : S × Ω, ⟪(z.1 : EuclideanSpace ℝ (Fin d)), v⟫ ^ 2 ∂Q.prod P) = _
  rw [integral_prod _ hi]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have he (u : S) : ⟪(u : EuclideanSpace ℝ (Fin d)), v⟫ = ⟪v, (u : EuclideanSpace ℝ (Fin d))⟫ := real_inner_comm _ _
  simp_rw [he]
  rw [OracleTemplate.ZerothOrder.sphere_projection_second_moment]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

lemma raw_spherical_direction_mean {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) × Ω → ℝ}
    (ha : Measurable a)
    (hai : Integrable (fun z => a z ^ 2)
      ((OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P)) :
    (∫ z, ((d : ℝ) * a z) • (z.1 : EuclideanSpace ℝ (Fin d))
      ∂(OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure.prod P) =
      ∫ u, ((d : ℝ) * (∫ ξ, a (u, ξ) ∂P)) • (u : EuclideanSpace ℝ (Fin d))
        ∂(OracleTemplate.ZerothOrder.sphereLaw (EuclideanSpace ℝ (Fin d))).toMeasure := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  have hu : Measurable (fun z : S × Ω => (z.1 : EuclideanSpace ℝ (Fin d))) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hunit : ∀ z : S × Ω, ‖(z.1 : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    intro z
    simpa only [S, mem_sphere_iff_norm, sub_zero] using z.1.property
  have hi := raw_direction_integrable hu ha hunit hai d
  rw [integral_prod _ hi]
  simp_rw [integral_smul_const, integral_const_mul]
  rfl

section WeakOracle

open Set Metric
open scoped ContDiff

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => Metric.sphere (0 : H) 1
local notation "Q" => (OracleTemplate.ZerothOrder.sphereLaw H : Measure S)

lemma weak_clipped_direction_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B τ h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : S × Ω → ℝ} (hc : Measurable c) (hcb : ∀ z, |c z| ≤ h) :
    let a := fun z : S × Ω => (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
    ‖(∫ z, directionEstimate d τ (z.1 : H) (a z + c z) ∂(Q).prod P) -
      (∫ z, ((d : ℝ) * a z) • (z.1 : H) ∂(Q).prod P)‖ ≤
        15 * B / (Real.sqrt d * τ) + Real.sqrt d * h := by
  let a := fun z : S × Ω => (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
  have hu : Measurable (fun z : S × Ω => (z.1 : H)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hunit : ∀ z : S × Ω, ‖(z.1 : H)‖ = 1 := by
    intro z
    simpa only [mem_sphere_iff_norm, sub_zero] using z.1.property
  have ha : Measurable a := by
    exact ((hFm.comp ((measurable_const.add (hu.const_smul γ)).prodMk measurable_snd)).sub
      (hFm.comp ((measurable_const.sub (hu.const_smul γ)).prodMk measurable_snd))).div_const _
  have hbase := WeakGradientSegments.weak_spherical_directional_moment hC hUC hFm hG hF x
    hγ hB hU hCU hi hb (0 : H) 0
  have hbase' : Integrable (fun z => a z ^ 2) ((Q).prod P) ∧
      (d : ℝ) * (∫ z, a z ^ 2 ∂(Q).prod P) ≤ 5 * B := by
    simpa only [Nat.zero_add, Nat.mul_zero, pow_zero, pow_one, mul_one, Nat.factorial_zero,
      Nat.cast_one] using hbase
  have hw (v : H) (hv : ‖v‖ = 1) :
      Integrable (fun z => a z ^ 2 * ⟪(z.1 : H), v⟫ ^ 2) ((Q).prod P) ∧
        (d : ℝ) ^ 2 * (∫ z, a z ^ 2 * ⟪(z.1 : H), v⟫ ^ 2 ∂(Q).prod P) ≤ 40 * B := by
    have hm := WeakGradientSegments.weak_spherical_directional_moment hC hUC hFm hG hF x
      hγ hB hU hCU hi hb v 1
    norm_num only [hv, Nat.factorial_one, Nat.cast_one, one_pow, mul_one, pow_one] at hm
    exact hm
  have hclean := clean_direction_estimate_bias hu ha hunit hτ hB hbase'.1 hbase'.2 hw
  have hcov (v : H) (hv : ‖v‖ = 1) : Integrable (fun z : S × Ω => ⟪(z.1 : H), v⟫ ^ 2) ((Q).prod P) ∧
      (d : ℝ) * (∫ z : S × Ω, ⟪(z.1 : H), v⟫ ^ 2 ∂(Q).prod P) ≤ 1 := by
    have hm := spherical_product_covariance P v
    exact ⟨hm.1, by simpa only [hv, one_pow] using hm.2.le⟩
  have hpert := perturbed_direction_estimate_mean_difference hu ha hc hunit hτ.le hh hcb hcov
  have ht := dist_triangle (∫ z, directionEstimate d τ (z.1 : H) (a z + c z) ∂(Q).prod P)
    (∫ z, directionEstimate d τ (z.1 : H) (a z) ∂(Q).prod P)
    (∫ z, ((d : ℝ) * a z) • (z.1 : H) ∂(Q).prod P)
  simp only [dist_eq_norm] at ht
  dsimp only
  exact ht.trans (by linarith)

end WeakOracle

lemma centered_direction_estimate_joint_measurable {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [SFinite P] {u : X × Ω → E} {a : X × Ω → ℝ}
    (hu : Measurable u) (ha : Measurable a) (d : ℕ) (τ : ℝ) :
    Measurable (fun z : X × Ω => directionEstimate d τ (u z) (a z) -
      ∫ w, directionEstimate d τ (u (z.1, w)) (a (z.1, w)) ∂P) := by
  have hG := direction_estimate_measurable hu ha d τ
  have hm : Measurable (fun x => ∫ w, directionEstimate d τ (u (x, w)) (a (x, w)) ∂P) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  exact hG.sub (hm.comp measurable_fst)

end LongTails.Proofs.ClippedVectorMoments
