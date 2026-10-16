import LongTails.Proofs.ClippedVectorMoments
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import LongTails.Proofs.FrankWolfeDescent

open MeasureTheory Filter
open scoped Topology Convolution RealInnerProductSpace

namespace LongTails.Proofs.LocalPopulationSmoothing

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => Metric.sphere (0 : H) 1
local notation "Q" => (OracleTemplate.ZerothOrder.sphereLaw H : Measure S)

lemma paired_population_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {f : H → ℝ} {C : Set H}
    (hF : Measurable F) (hi : ∀ x ∈ C, Integrable (fun ξ => F (x, ξ)) P)
    (hf : ∀ x ∈ C, (∫ ξ, F (x, ξ) ∂P) = f x)
    (x : H) (γ : ℝ) (hplus : ∀ u : S, x + γ • (u : H) ∈ C)
    (hminus : ∀ u : S, x - γ • (u : H) ∈ C)
    (hsecond : Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2)
        ((Q).prod P)) :
    (∫ z : S × Ω, ((d : ℝ) *
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ))) •
        (z.1 : H) ∂(Q).prod P) =
      ∫ u : S, ((d : ℝ) * ((f (x + γ • (u : H)) - f (x - γ • (u : H))) / (2 * γ))) •
        (u : H) ∂Q := by
  have hu : Measurable (fun z : S × Ω => (z.1 : H)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have ha : Measurable (fun z : S × Ω =>
      (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) :=
    ((hF.comp ((measurable_const.add (hu.const_smul γ)).prodMk measurable_snd)).sub
      (hF.comp ((measurable_const.sub (hu.const_smul γ)).prodMk measurable_snd))).div_const _
  rw [ClippedVectorMoments.raw_spherical_direction_mean ha hsecond]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [integral_div, integral_sub (hi _ (hplus u)) (hi _ (hminus u)), hf _ (hplus u), hf _ (hminus u)]


noncomputable def boundaryField (f : H → ℝ) (γ : ℝ) (x : H) : H :=
  ∫ u : S, (((d : ℝ) / γ) * f (x + γ • (u : H))) • (u : H) ∂Q

lemma ball_smooth_uniform_error {f g : H → ℝ} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (he : ∀ x, |f x - g x| ≤ ε) (γ : ℝ) (x : H) :
    |OracleTemplate.ZerothOrder.ballSmooth f γ x - OracleTemplate.ZerothOrder.ballSmooth g γ x| ≤ ε := by
  unfold OracleTemplate.ZerothOrder.ballSmooth
  rw [← integral_sub (OracleTemplate.ZerothOrder.ball_offset_continuous_integrable hf x γ)
    (OracleTemplate.ZerothOrder.ball_offset_continuous_integrable hg x γ)]
  have hh := norm_integral_le_of_norm_le_const
    (μ := (OracleTemplate.ZerothOrder.radialLaw d (NeZero.pos d)).toMeasure.prod (Q))
    (f := fun v : ℝ × S => f (x + γ • OracleTemplate.ZerothOrder.ballOffset v) -
      g (x + γ • OracleTemplate.ZerothOrder.ballOffset v))
    (Filter.Eventually.of_forall (fun v => by simpa only [Real.norm_eq_abs] using he _))
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hh

lemma boundary_field_uniform_error {f g : H → ℝ} (hf : Continuous f) (hg : Continuous g)
    {ε γ : ℝ} (hγ : 0 < γ) (he : ∀ x, |f x - g x| ≤ ε) (x : H) :
    ‖boundaryField f γ x - boundaryField g γ x‖ ≤ (d : ℝ) / γ * ε := by
  have hfi : Integrable (fun u : S => (((d : ℝ) / γ) * f (x + γ • (u : H))) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map (f := fun u : H =>
      (((d : ℝ) / γ) * f (x + γ • u)) • u) (by fun_prop)
  have hgi : Integrable (fun u : S => (((d : ℝ) / γ) * g (x + γ • (u : H))) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map (f := fun u : H =>
      (((d : ℝ) / γ) * g (x + γ • u)) • u) (by fun_prop)
  unfold boundaryField
  rw [← integral_sub hfi hgi]
  have hb (u : S) : ‖(((d : ℝ) / γ) * f (x + γ • (u : H))) • (u : H) -
      (((d : ℝ) / γ) * g (x + γ • (u : H))) • (u : H)‖ ≤ (d : ℝ) / γ * ε := by
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ d / γ by positivity), hu, mul_one]
    exact mul_le_mul_of_nonneg_left (he _) (by positivity)
  have hh := norm_integral_le_of_norm_le_const (μ := Q) (Filter.Eventually.of_forall hb)
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hh


lemma ball_smooth_gradient_of_uniform_approximation {f : H → ℝ}
    {fₙ : ℕ → H → ℝ} {gₙ : ℕ → H → H} {ε : ℕ → ℝ}
    (hf : Continuous f) (hfn : ∀ n, Continuous (fₙ n)) (hgn : ∀ n, Continuous (gₙ n))
    (hdn : ∀ n x, HasGradientAt (fₙ n) (gₙ n x) x)
    (he : ∀ n x, |fₙ n x - f x| ≤ ε n) (he0 : Tendsto ε atTop (𝓝 0))
    {γ : ℝ} (hγ : 0 < γ) (x : H) :
    HasGradientAt (OracleTemplate.ZerothOrder.ballSmooth f γ) (boundaryField f γ x) x := by
  have hgconv : TendstoUniformly
      (fun n y => (InnerProductSpace.toDual ℝ H) (boundaryField (fₙ n) γ y))
      (fun y => (InnerProductSpace.toDual ℝ H) (boundaryField f γ y)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro e hepos
    have hh : Tendsto (fun n => (d : ℝ) / γ * ε n) atTop (𝓝 0) := by
      simpa only [mul_zero] using he0.const_mul ((d : ℝ) / γ)
    filter_upwards [(tendsto_order.mp hh).2 e hepos] with n hn y
    rw [(InnerProductSpace.toDual ℝ H).isometry.dist_eq, dist_eq_norm, norm_sub_rev]
    exact (boundary_field_uniform_error (hfn n) hf hγ (he n) y).trans_lt hn
  have hv (y : H) : Tendsto (fun n => OracleTemplate.ZerothOrder.ballSmooth (fₙ n) γ y)
      atTop (𝓝 (OracleTemplate.ZerothOrder.ballSmooth f γ y)) := by
    apply Metric.tendsto_nhds.mpr
    intro e hepos
    filter_upwards [(tendsto_order.mp he0).2 e hepos] with n hn
    rw [Real.dist_eq]
    exact (ball_smooth_uniform_error (hfn n) hf (he n) γ y).trans_lt hn
  rw [hasGradientAt_iff_hasFDerivAt]
  apply hasFDerivAt_of_tendstoUniformly hgconv _ hv x
  intro n y
  have hh := OracleTemplate.ZerothOrder.ballSmooth_gradient (hgn n) (hdn n) γ y
  rw [OracleTemplate.ZerothOrder.ball_boundary_gradient (hfn n) (hgn n) (hdn n) y hγ.ne'] at hh
  exact hh.hasFDerivAt


lemma ball_smooth_gradient_lipschitz_function {f : H → ℝ} {M : NNReal}
    (hL : LipschitzWith M f) {γ : ℝ} (hγ : 0 < γ) (x : H) :
    HasGradientAt (OracleTemplate.ZerothOrder.ballSmooth f γ) (boundaryField f γ x) x := by
  obtain ⟨φ, hφ, _⟩ := MollifiedSecantMoments.shrinking_bumps (d := d) (show (0 : ℝ) < 1 by norm_num)
  let fₙ := fun n => f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (φ n).normed volume
  let gₙ := fun n y => ∫ z, f z • gradient ((φ n).normed volume) (y - z)
  have hlocal : LocallyIntegrable f volume := hL.continuous.locallyIntegrable
  have hdn (n : ℕ) (y : H) : HasGradientAt (fₙ n) (gₙ n y) y :=
    WeakGradientConvolution.convolution_hasGradientAt_kernel hlocal (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed y
  have hfn (n : ℕ) : Continuous (fₙ n) :=
    continuous_iff_continuousAt.mpr (fun y => (hdn n y).continuousAt)
  have hgn (n : ℕ) : Continuous (gₙ n) :=
    WeakGradientConvolution.convolution_kernel_gradient_continuous hlocal (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed
  have he (n : ℕ) (y : H) : |fₙ n y - f y| ≤ (M : ℝ) * (φ n).rOut :=
    WeakGradientConvolution.normed_mollification_uniform_error hL (φ n) y
  have he0 : Tendsto (fun n => (M : ℝ) * (φ n).rOut) atTop (𝓝 0) := by
    simpa only [mul_zero] using hφ.const_mul (M : ℝ)
  exact ball_smooth_gradient_of_uniform_approximation hL.continuous hfn hgn hdn he he0 hγ x


lemma smoothing_agrees_on_ball {f g : H → ℝ} {C : Set H} (he : Set.EqOn f g C)
    (x : H) {γ : ℝ} (hγ : 0 ≤ γ) (hball : Metric.closedBall x γ ⊆ C) :
    OracleTemplate.ZerothOrder.ballSmooth f γ x = OracleTemplate.ZerothOrder.ballSmooth g γ x ∧
      boundaryField f γ x = boundaryField g γ x := by
  have hlegal (v : H) (hv : ‖v‖ ≤ 1) : x + γ • v ∈ C := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hγ]
    exact (mul_le_mul_of_nonneg_left hv hγ).trans_eq (mul_one γ)
  constructor
  · unfold OracleTemplate.ZerothOrder.ballSmooth
    apply integral_congr_ae
    filter_upwards [] with v
    exact he (hlegal _ (OracleTemplate.ZerothOrder.ballOffset_norm v))
  · unfold boundaryField
    apply integral_congr_ae
    filter_upwards [] with u
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [he (hlegal _ hu.le)]

lemma local_lipschitz_smoothing_extension {f : H → ℝ} {C D : Set H} {M : NNReal}
    (hL : LipschitzOnWith M f C) {γ : ℝ} (hγ : 0 < γ)
    (hball : ∀ x ∈ D, Metric.closedBall x γ ⊆ C) :
    ∃ F : H → ℝ, LipschitzWith M F ∧ Set.EqOn f F C ∧
      ∀ x ∈ D, OracleTemplate.ZerothOrder.ballSmooth F γ x = OracleTemplate.ZerothOrder.ballSmooth f γ x ∧
        HasGradientAt (OracleTemplate.ZerothOrder.ballSmooth F γ) (boundaryField f γ x) x := by
  obtain ⟨F, hF, he⟩ := hL.extend_real
  refine ⟨F, hF, he, ?_⟩
  intro x hx
  have ha := smoothing_agrees_on_ball he x hγ.le (hball x hx)
  exact ⟨ha.1.symm, ha.2.symm ▸ ball_smooth_gradient_lipschitz_function hF hγ x⟩


lemma boundary_field_lipschitz {f : H → ℝ} {M : NNReal} (hL : LipschitzWith M f)
    {γ : ℝ} (hγ : 0 < γ) (x y : H) :
    ‖boundaryField f γ x - boundaryField f γ y‖ ≤ Real.sqrt d * (M : ℝ) / γ * ‖x - y‖ := by
  have hf := hL.continuous
  let e := fun u : S => f (x + γ • (u : H)) - f (y + γ • (u : H))
  have hc : Continuous (fun u : H => f (x + γ • u) - f (y + γ • u)) := by
    exact (hL.continuous.comp (continuous_const.add (continuous_id.const_smul γ))).sub
      (hL.continuous.comp (continuous_const.add (continuous_id.const_smul γ)))
  have he : Measurable e := (hc.comp continuous_subtype_val).measurable
  have heb (u : S) : |e u| ≤ (M : ℝ) * ‖x - y‖ := by
    simpa only [e, Real.dist_eq, dist_eq_norm, add_sub_add_right_eq_sub, Real.norm_eq_abs] using
      hL.dist_le_mul (x + γ • (u : H)) (y + γ • (u : H))
  have hi : Integrable (fun u : S => ((d : ℝ) / γ * e u) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map
      (f := fun u : H => ((d : ℝ) / γ * (f (x + γ • u) - f (y + γ • u))) • u)
      ((continuous_const.mul hc).smul continuous_id)
  have hfi (z : H) : Integrable (fun u : S => ((d : ℝ) / γ * f (z + γ • (u : H))) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map
      (f := fun u : H => ((d : ℝ) / γ * f (z + γ • u)) • u) (by fun_prop)
  have hid : boundaryField f γ x - boundaryField f γ y =
      ∫ u : S, ((d : ℝ) / γ * e u) • (u : H) ∂Q := by
    unfold boundaryField
    rw [← integral_sub (hfi x) (hfi y)]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [e, mul_sub, sub_smul]
  rw [hid]
  apply ClippedVectorMoments.norm_le_unit_direction_bound _ (by positivity)
  intro v hv
  have hw : Measurable (fun u : S => ⟪v, (u : H)⟫) := by fun_prop
  have hwi : Integrable (fun u : S => ⟪v, (u : H)⟫ ^ 2) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous (f := fun u : H => ⟪v, u⟫ ^ 2) (by fun_prop)
  have hwb : (d : ℝ) * (∫ u : S, ⟪v, (u : H)⟫ ^ 2 ∂Q) ≤ 1 := by
    rw [OracleTemplate.ZerothOrder.sphere_projection_second_moment, hv, one_pow]
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
    simp [hd]
  have hb := ScalarClippedMoments.bounded_directional_bias he hw
    (show (0 : ℝ) < d by exact_mod_cast NeZero.pos d) (by positivity) heb hwi hwb
  rw [← integral_inner hi v]
  simp only [real_inner_smul_right]
  simp_rw [mul_assoc]
  rw [integral_const_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ d / γ by positivity)]
  have hh := (div_le_div_of_nonneg_right hb.2 hγ.le)
  convert hh using 1 <;> ring


lemma ball_smooth_convex_on {f : H → ℝ} {C D : Set H} (hf : Continuous f)
    (hc : ConvexOn ℝ C f) (hD : Convex ℝ D) {γ : ℝ}
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • OracleTemplate.ZerothOrder.ballOffset v ∈ C) :
    ConvexOn ℝ D (OracleTemplate.ZerothOrder.ballSmooth f γ) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  let P := (OracleTemplate.ZerothOrder.radialLaw d (NeZero.pos d)).toMeasure.prod (Q)
  have hi (z : H) := OracleTemplate.ZerothOrder.ball_offset_continuous_integrable hf z γ
  change (∫ v : ℝ × S, f (a • x + b • y + γ • OracleTemplate.ZerothOrder.ballOffset v) ∂P) ≤
    a • (∫ v : ℝ × S, f (x + γ • OracleTemplate.ZerothOrder.ballOffset v) ∂P) +
      b • (∫ v : ℝ × S, f (y + γ • OracleTemplate.ZerothOrder.ballOffset v) ∂P)
  calc
    _ ≤ ∫ v : ℝ × S, a * f (x + γ • OracleTemplate.ZerothOrder.ballOffset v) +
        b * f (y + γ • OracleTemplate.ZerothOrder.ballOffset v) ∂P := by
      apply integral_mono (hi _) (((hi x).const_mul a).add ((hi y).const_mul b))
      intro v
      have he : a • x + b • y + γ • OracleTemplate.ZerothOrder.ballOffset v =
          a • (x + γ • OracleTemplate.ZerothOrder.ballOffset v) +
            b • (y + γ • OracleTemplate.ZerothOrder.ballOffset v) := by
        rw [smul_add, smul_add]
        have hh : a • (γ • OracleTemplate.ZerothOrder.ballOffset v) +
            b • (γ • OracleTemplate.ZerothOrder.ballOffset v) = γ • OracleTemplate.ZerothOrder.ballOffset v := by
          rw [← add_smul, hab, one_smul]
        calc
          _ = a • x + b • y + (a • (γ • OracleTemplate.ZerothOrder.ballOffset v) +
              b • (γ • OracleTemplate.ZerothOrder.ballOffset v)) := by rw [hh]
          _ = _ := by abel
      change f (a • x + b • y + γ • OracleTemplate.ZerothOrder.ballOffset v) ≤
        a * f (x + γ • OracleTemplate.ZerothOrder.ballOffset v) + b * f (y + γ • OracleTemplate.ZerothOrder.ballOffset v)
      rw [he]
      exact hc.2 (hlegal x hx v) (hlegal y hy v) ha hb hab
    _ = _ := by
      rw [integral_add ((hi x).const_mul a) ((hi y).const_mul b), integral_const_mul, integral_const_mul]
      rfl

lemma ball_smooth_relative_support {f : H → ℝ} {M : NNReal} {C D : Set H}
    (hL : LipschitzWith M f) (hc : ConvexOn ℝ C f) (hD : Convex ℝ D) {γ : ℝ} (hγ : 0 < γ)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • OracleTemplate.ZerothOrder.ballOffset v ∈ C)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    OracleTemplate.ZerothOrder.ballSmooth f γ x + ⟪boundaryField f γ x, y - x⟫ ≤
      OracleTemplate.ZerothOrder.ballSmooth f γ y := by
  have hh := OracleTemplate.FrankWolfe.convex_support_on (ball_smooth_convex_on hL.continuous hc hD hlegal)
    hx hy (ball_smooth_gradient_lipschitz_function hL hγ x)
  linarith only [hh]

lemma ball_smooth_relative_upper {f : H → ℝ} {M : NNReal} {D : Set H}
    (hL : LipschitzWith M f) (hD : Convex ℝ D) {γ : ℝ} (hγ : 0 < γ)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    OracleTemplate.ZerothOrder.ballSmooth f γ y ≤ OracleTemplate.ZerothOrder.ballSmooth f γ x +
      ⟪boundaryField f γ x, y - x⟫ + (Real.sqrt d * (M : ℝ) / γ) / 2 * ‖y - x‖ ^ 2 :=
  OracleTemplate.FrankWolfe.smooth_upper_bound_on hD
    (fun z _ => ball_smooth_gradient_lipschitz_function hL hγ z)
    (fun z _ w _ => boundary_field_lipschitz hL hγ z w) hx hy


lemma paired_sphere_mean_eq_boundary {f : H → ℝ} (hf : Continuous f) (γ : ℝ) (x : H) :
    (∫ u : S, ((d : ℝ) * ((f (x + γ • (u : H)) - f (x - γ • (u : H))) / (2 * γ))) •
      (u : H) ∂Q) = boundaryField f γ x := by
  have hi : Integrable (fun u : S => ((d : ℝ) *
      ((f (x + γ • (u : H)) - f (x - γ • (u : H))) / (2 * γ))) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map (f := fun u : H =>
      ((d : ℝ) * ((f (x + γ • u) - f (x - γ • u)) / (2 * γ))) • u) (by fun_prop)
  have hb : Integrable (fun u : S => (((d : ℝ) / γ) * f (x + γ • (u : H))) • (u : H)) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map (f := fun u : H =>
      (((d : ℝ) / γ) * f (x + γ • u)) • u) (by fun_prop)
  unfold boundaryField
  ext i
  rw [OracleTemplate.ZerothOrder.integral_euclidean_apply hi, OracleTemplate.ZerothOrder.integral_euclidean_apply hb]
  have hplus : Integrable (fun u : S => f (x + γ • (u : H)) * (u : H) i) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map
      (f := fun u : H => f (x + γ • u) * u i) (by fun_prop)
  have hminus : Integrable (fun u : S => f (x - γ • (u : H)) * (u : H) i) (Q) :=
    OracleTemplate.ZerothOrder.sphere_integrable_continuous_map
      (f := fun u : H => f (x - γ • u) * u i) (by fun_prop)
  have hr := OracleTemplate.ZerothOrder.sphereLaw_integral_rotate H
    (LinearIsometryEquiv.neg ℝ : H ≃ₗᵢ[ℝ] H) (fun u : S => f (x + γ • (u : H)) * (u : H) i)
  have hre : (∫ u : S, f (x - γ • (u : H)) * (u : H) i ∂Q) =
      -(∫ u : S, f (x + γ • (u : H)) * (u : H) i ∂Q) := by
    have hn (u : S) : (OracleTemplate.ZerothOrder.sphereRotate
        (LinearIsometryEquiv.neg ℝ : H ≃ₗᵢ[ℝ] H) u : H) = -(u : H) := rfl
    simp only [hn, smul_neg, ← sub_eq_add_neg, PiLp.neg_apply, mul_neg, integral_neg] at hr
    linarith
  simp only [PiLp.smul_apply, smul_eq_mul]
  have he (u : S) : (d : ℝ) * ((f (x + γ • (u : H)) - f (x - γ • (u : H))) / (2 * γ)) * (u : H) i =
      (d : ℝ) / (2 * γ) * (f (x + γ • (u : H)) * (u : H) i - f (x - γ • (u : H)) * (u : H) i) := by ring
  simp_rw [he, mul_assoc]
  rw [integral_const_mul, integral_const_mul, integral_sub hplus hminus, hre]
  ring

end LongTails.Proofs.LocalPopulationSmoothing
