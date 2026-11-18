import LongTails.Proofs.SphericalPreferenceDrift
import LongTails.Proofs.SphericalPreferenceStep

open MeasureTheory Metric Set NormedSpace Filter
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SphericalPreferenceIntegration

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceDrift
open LongTails.Algorithms.SphericalPreferenceDescent LongTails.Proofs.SphericalPreferenceSecant
open LongTails.Proofs.SphericalPreferenceDirection OracleTemplate.ZerothOrder

variable {A E F : Type*} [MeasurableSpace A] [MeasurableSpace E] [MeasurableSpace F]

private lemma boundI {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
      {g : α → ℝ} (hm : Measurable g) {c : ℝ} (hb : ∀ a, ‖g a‖ ≤ c) : Integrable g P :=
    Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall hb)

lemma rotate_integrals (P : Measure A) (Q : Measure E) (M : Measure F)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure M]
    (f : (A × E) × F → ℝ) (hm : Measurable f) {L : ℝ} (hb : ∀ a, ‖f a‖ ≤ L) :
    (∫ a, ∫ e, ∫ z, f ((a,e),z) ∂M ∂Q ∂P) =
      ∫ e, ∫ z, ∫ a, f ((a,e),z) ∂P ∂M ∂Q := by
  have hi : Integrable (fun q : A × (E × F) => f ((q.1,q.2.1),q.2.2)) (P.prod (Q.prod M)) :=
    Integrable.of_bound (hm.comp (by fun_prop)).aestronglyMeasurable L (Eventually.of_forall fun _ => hb _)
  have hslice (a : A) : Integrable (fun q : E × F => f ((a,q.1),q.2)) (Q.prod M) :=
    Integrable.of_bound (hm.comp (by fun_prop)).aestronglyMeasurable L (Eventually.of_forall fun _ => hb _)
  calc
    _ = ∫ a, ∫ q : E × F, f ((a,q.1),q.2) ∂Q.prod M ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun a => (integral_prod _ (hslice a)).symm
    _ = ∫ q : E × F, ∫ a, f ((a,q.1),q.2) ∂P ∂Q.prod M := integral_integral_swap hi
    _ = _ := integral_prod _ hi.integral_prod_right

variable {d : ℕ} [NeZero d]
local notation "H" => Point d
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

omit [NeZero d] in
lemma bounded_sign (b : ℝ) (u : S) (v : H) :
    ‖bitSign b * ⟪(u : H),v⟫‖ ≤ ‖v‖ := by
  rw [Real.norm_eq_abs, abs_mul, bit_abs, one_mul]
  simpa [mem_sphere_zero_iff_norm.mp u.property] using abs_real_inner_le_norm (u : H) v

set_option maxHeartbeats 800000 in
lemma sample_drift (μ : Measure H) [IsProbabilityMeasure μ] (hs : Spherical μ)
    {B : ℝ≥0} (hB : 0 < B) (hd : 2 ≤ d) (hq : 1/2 ≤ μ.real (closedBall 0 (2*B)))
    {f : H → ℝ} (hL : LipschitzWith B f) {C : Set H} (hc : ConvexOn ℝ C f)
    (o x m : H) (ho : o ∈ C) (hmin : IsMinOn f C o) {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hhr : h < r)
    (hy : ∀ w ∈ ball (0 : H) r, m+w ∈ C ∧ ‖x-(m+w)‖ ≤ 3*r)
    (hfeas : ∀ (u : S) w, w ∈ ball (0 : H) r →
      m+w-h • (u : H) ∈ C ∧ m+w+h • (u : H) ∈ C) :
    let J : Measure H := jitterLaw d r
    (f x-f o)/(192 * B * Real.sqrt d) - 3*r - B*(3*r)/(192 * B * Real.sqrt d) -
        2*(d : ℝ)*h/r*‖x-o‖ ≤
      ∫ w, ∫ u : S, ∫ z, secantBit f z u (m+w) h * ⟪(u : H),x-o⟫ ∂μ ∂Q ∂J := by
  let J : Measure H := jitterLaw d r
  let v := x-o
  let T := fun q : (H × H) × S => tangentBit f q.1.2 q.2 (m+q.1.1) * ⟪(q.2 : H),v⟫
  let D := fun q : (H × S) × H => secantBit f q.2 q.1.2 (m+q.1.1) h * ⟪(q.1.2 : H),v⟫
  have hmT : Measurable T := by
    have hg : Measurable (gradient f) := (InnerProductSpace.toDual ℝ H).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
    unfold T tangentBit
    exact (measurable_bitSign.comp (by fun_prop)).mul (by fun_prop)
  have hmD : Measurable D := by
    have hf := hL.continuous.measurable
    unfold D secantBit sampleUtility
    exact (measurable_bitSign.comp (by fun_prop)).mul (by fun_prop)
  have hT (q) : ‖T q‖ ≤ ‖v‖ := bounded_sign _ _ _
  have hD (q) : ‖D q‖ ≤ ‖v‖ := bounded_sign _ _ _
  have hmJs : J = ProbabilityTheory.cond volume (ball 0 r) := by simp [J, jitterLaw, hr]
  have hmJa : J ≪ (volume : Measure H) := by rw [hmJs]; exact ProbabilityTheory.cond_absolutelyContinuous
  have hJb : ∀ᵐ w ∂J, w ∈ ball (0:H) r := by rw [hmJs]; exact ProbabilityTheory.ae_cond_mem measurableSet_ball
  let K := (f x-f o)/(192 * B * Real.sqrt d) - 3*r - B*(3*r)/(192 * B * Real.sqrt d)
  have hK : K ≤ ∫ w, ∫ z, ∫ u : S, T ((w,z),u) ∂Q ∂μ ∂J := by
    have hTK (w : H) : (∫ z, ∫ u : S, T ((w,z),u) ∂Q ∂μ) =
        ⟪angularWeight d • LongTails.Proofs.SphericalPreferenceTaste.tasteMean μ (gradient f (m+w)),v⟫ :=
      tangent_average (μ := μ) (gradient f (m+w)) v
    simp_rw [hTK]
    have hint : Integrable (fun w => ⟪angularWeight d • LongTails.Proofs.SphericalPreferenceTaste.tasteMean μ (gradient f (m+w)),v⟫) J := by
      refine boundI J ?_ (c := ‖v‖) ?_
      · have hg : Measurable (gradient f) := (InnerProductSpace.toDual ℝ H).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
        have hm := (LongTails.Proofs.SphericalPreferenceTaste.measurable_unit (d := d)).comp
          (show Measurable (fun q : H × H => gradient f (m+q.1)+q.2) by fun_prop)
        have hm' := hm.stronglyMeasurable.integral_prod_right' (ν := μ)
        have hm'' : Measurable (fun w => LongTails.Proofs.SphericalPreferenceTaste.tasteMean μ (gradient f (m+w))) := hm'.measurable
        fun_prop
      · intro w
        exact (abs_real_inner_le_norm _ _).trans (by simpa using mul_le_mul_of_nonneg_right (mean_norm_le (μ := μ) (gradient f (m+w))) (norm_nonneg v))
    have hb := integral_mono_ae (integrable_const K) hint (by
      filter_upwards [hJb, hmJa.ae_le (ae_differentiable_shift hL m)] with w hw hdiff
      have h := tangent_drift hs hB hd hq hL hc (x := x) (hy w hw).1 ho (hmin (hy w hw).1) hdiff
      have hdist := (hy w hw).2
      have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist B.coe_nonneg)
        (show 0 ≤ 192 * (B:ℝ) * Real.sqrt d by positivity)
      dsimp [K,v]
      linarith only [h, hdist, hdiv])
    simpa using hb
  have hcT := rotate_integrals J μ Q T hmT hT
  have hcD := rotate_integrals J Q μ D hmD hD
  rw [hcT] at hK
  dsimp only
  change K - _ ≤ ∫ w, ∫ u : S, ∫ z, D ((w,u),z) ∂μ ∂Q ∂J
  rw [hcD]
  let t := fun q : S × H => ∫ w, T ((w,q.2),q.1) ∂J
  let s := fun q : S × H => ∫ w, D ((w,q.1),q.2) ∂J
  have ht : Integrable t ((Q).prod μ) := by
    refine boundI ((Q).prod μ) ?_ (c := ‖v‖) ?_
    · exact (hmT.comp (show Measurable (fun q : (S × H) × H => ((q.2,q.1.2),q.1.1)) by fun_prop)).stronglyMeasurable.integral_prod_right'.measurable
    · intro q
      simpa [t] using norm_integral_le_of_norm_le_const (μ := J) (Eventually.of_forall fun w => hT ((w,q.2),q.1))
  have hsI : Integrable s ((Q).prod μ) := by
    refine boundI ((Q).prod μ) ?_ (c := ‖v‖) ?_
    · exact (hmD.comp (show Measurable (fun q : (S × H) × H => ((q.2,q.1.1),q.1.2)) by fun_prop)).stronglyMeasurable.integral_prod_right'.measurable
    · intro q
      simpa [s] using norm_integral_le_of_norm_le_const (μ := J) (Eventually.of_forall fun w => hD ((w,q.1),q.2))
  have hpair := integral_mono (ht.sub (integrable_const (2*(d : ℝ)*h/r*‖v‖))) hsI (fun q =>
    weighted_secant_bias hL hc q.2 m v q.1 hr hh hhr (hfeas q.1))
  simp only [Pi.sub_apply] at hpair
  rw [integral_sub ht (integrable_const _), integral_const, probReal_univ, one_smul, integral_prod _ hsI] at hpair
  have hti := integral_prod _ ht
  rw [integral_integral_swap (f := fun u z => t (u,z)) ht] at hti
  change K ≤ ∫ z, ∫ u : S, t (u,z) ∂Q ∂μ at hK
  exact (sub_le_sub_right (hK.trans_eq hti.symm) _).trans hpair

end LongTails.Proofs.SphericalPreferenceIntegration
