import LongTails.Proofs.SphericalPreferenceTaste
import LongTails.Proofs.SphericalPreferenceSecant

open MeasureTheory Metric Set NormedSpace Filter
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SphericalPreferenceDrift

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceDirection
open LongTails.Proofs.SphericalPreferenceTaste LongTails.Proofs.SphericalPreferenceSecant
open OracleTemplate.ZerothOrder

variable {d : ℕ} [NeZero d]
local notation "H" => Point d
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma tangent_average {μ : Measure H} [IsProbabilityMeasure μ] (g v : H) :
    (∫ z, ∫ u : S, bitSign ⟪g + z, (u : H)⟫ * ⟪(u : H), v⟫ ∂Q ∂μ) =
      ⟪angularWeight d • tasteMean μ g, v⟫ := by
  have he (z : H) : (∫ u : S, bitSign ⟪g + z, (u : H)⟫ * ⟪(u : H), v⟫ ∂Q) =
      angularWeight d * ⟪normalize (g + z), v⟫ := by
    rw [← real_inner_smul_left, ← signed_mean, real_inner_comm v _,
      ← integral_inner (𝕜 := ℝ) (integrable_signedDirection (g+z)) v]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [real_inner_comm _ v, signedDirection, real_inner_smul_left]
  simp_rw [he]
  rw [integral_const_mul, real_inner_smul_left, real_inner_comm v _, tasteMean, ← integral_inner (𝕜 := ℝ) (unit_integrable (μ := μ) g) v]
  simp_rw [real_inner_comm _ v]

lemma mean_norm_le {μ : Measure H} [IsProbabilityMeasure μ] (g : H) :
    ‖angularWeight d • tasteMean μ g‖ ≤ 1 := by
  have ha : ‖angularWeight d‖ ≤ 1 := by
    have he := signed_mean (EuclideanSpace.single (0 : Fin d) (1 : ℝ))
    have he' := norm_integral_le_of_norm_le_const (μ := Q) (f := signedDirection (EuclideanSpace.single (0 : Fin d) (1 : ℝ)))
      (C := 1) (Filter.Eventually.of_forall fun u => by
        simp [signedDirection, norm_smul, Real.norm_eq_abs, bit_abs, mem_sphere_zero_iff_norm.mp u.property])
    rw [he, norm_smul] at he'
    simpa [NormedSpace.normalize] using he'
  have hm : ‖tasteMean μ g‖ ≤ 1 := by
    simpa [tasteMean] using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall fun z => normalize_bound (g+z))
  rw [norm_smul]
  simpa using mul_le_mul ha hm (norm_nonneg _) zero_le_one

lemma tangent_drift {μ : Measure H} [IsProbabilityMeasure μ] (hs : Spherical μ)
    {B : ℝ≥0} (hB : 0 < B) (hd : 2 ≤ d) (hq : 1 / 2 ≤ μ.real (closedBall 0 (2 * B)))
    {f : H → ℝ} (hL : LipschitzWith B f) {C : Set H} (hc : ConvexOn ℝ C f)
    {x y o : H} (hy : y ∈ C) (ho : o ∈ C) (hmin : f o ≤ f y) (hdiff : DifferentiableAt ℝ f y) :
    (f x - f o) / (192 * B * Real.sqrt d) - ‖x-y‖ -
      B * ‖x-y‖ / (192 * B * Real.sqrt d) ≤
      ⟪angularWeight d • tasteMean μ (gradient f y), x-o⟫ := by
  let G := angularWeight d • tasteMean μ (gradient f y)
  have hnorm : ‖gradient f y‖ ≤ B := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)
  have hsup := OracleTemplate.FrankWolfe.convex_support_on hc hy ho hdiff.hasGradientAt
  rw [show o-y = -(y-o) by abel, inner_neg_right] at hsup
  have he := expected_direction_gain hs (show 0 < (B : ℝ) from hB) hd hq
    (gradient f y) (y-o) hnorm (sub_nonneg.mpr hmin) (by linarith only [hsup])
  have hshift : -‖x-y‖ ≤ ⟪G, x-y⟫ := by
    have h := (abs_real_inner_le_norm G (x-y)).trans (mul_le_mul_of_nonneg_right (mean_norm_le _) (norm_nonneg _))
    linarith only [(abs_le.mp h).1]
  have hLip := hL.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm] at hLip
  have hp := (abs_le.mp hLip).2
  have hden : 0 < 192 * (B : ℝ) * Real.sqrt d := by positivity
  have hmono := div_le_div_of_nonneg_right hp hden.le
  change _ ≤ ⟪G, x-o⟫
  rw [show x-o = x-y+(y-o) by abel, inner_add_right]
  change _ ≤ ⟪G,y-o⟫ at he
  rw [sub_div] at he hmono ⊢
  linarith only [he, hmono, hshift]

omit [NeZero d] in
lemma weighted_secant_bias {B : ℝ≥0} {f : H → ℝ} (hL : LipschitzWith B f)
    {C : Set H} (hc : ConvexOn ℝ C f) (z m v : H) (u : S) {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hhr : h < r)
    (hfeas : ∀ w ∈ ball (0 : H) r, m + w - h • (u : H) ∈ C ∧ m + w + h • (u : H) ∈ C) :
    let J : Measure H := LongTails.Algorithms.SphericalPreferenceDescent.jitterLaw d r
    (∫ w, tangentBit f z u (m+w) * ⟪(u : H), v⟫ ∂J) - 2 * d * h / r * ‖v‖ ≤
      ∫ w, secantBit f z u (m+w) h * ⟪(u : H), v⟫ ∂J := by
  dsimp only
  rw [integral_mul_const, integral_mul_const]
  have hu := mem_sphere_zero_iff_norm.mp u.property
  have he := finite_comparison_bias hL hc z u m hr hh hhr hu hfeas
  have hv := abs_real_inner_le_norm (u : H) v
  rw [hu, one_mul] at hv
  have hmul := mul_le_mul he hv (abs_nonneg _) (by positivity)
  rw [← abs_mul] at hmul
  linarith only [(abs_le.mp hmul).1]

end LongTails.Proofs.SphericalPreferenceDrift
