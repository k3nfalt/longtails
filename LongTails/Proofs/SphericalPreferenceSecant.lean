import LongTails.Proofs.SphericalPreferenceDirection
import LongTails.Proofs.SphericalPreferenceJitter
import LongTails.Proofs.FrankWolfeDescent
import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.SphericalPreferenceSecant

open LongTails.Setups.SphericalRandomUtility LongTails.Proofs.SphericalPreferenceDirection
open LongTails.Proofs.SphericalPreferenceJitter LongTails.Algorithms.SphericalPreferenceDescent

variable {d : ℕ}
local notation "H" => Point d

noncomputable def tangentBit (f : H → ℝ) (z u x : H) : ℝ :=
  bitSign ⟪gradient f x + z, u⟫

noncomputable def secantBit (f : H → ℝ) (z u y : H) (h : ℝ) : ℝ :=
  bitSign (sampleUtility f z (y + h • u) - sampleUtility f z (y - h • u))

lemma tangent_measurable (f : H → ℝ) (z u : H) : Measurable (tangentBit f z u) := by
  have hg : Measurable (gradient f) :=
    (InnerProductSpace.toDual ℝ H).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  unfold tangentBit
  apply measurable_bitSign.comp
  fun_prop

lemma bit_abs (a : ℝ) : |bitSign a| = 1 := by
  unfold bitSign
  split_ifs <;> norm_num

lemma bitSign_pos_smul (a : ℝ) {t : ℝ} (ht : 0 < t) : bitSign (t * a) = bitSign a := by
  simp [bitSign, mul_nonneg_iff_of_pos_left ht]

lemma secant_sandwich {C : Set H} {f : H → ℝ} (hc : ConvexOn ℝ C f)
    (z u y : H) {h : ℝ} (hh : 0 < h)
    (hm : y - h • u ∈ C) (hp : y + h • u ∈ C)
    (hdm : DifferentiableAt ℝ f (y - h • u)) (hdp : DifferentiableAt ℝ f (y + h • u)) :
    tangentBit f z u (y - h • u) ≤ secantBit f z u y h ∧
    secantBit f z u y h ≤ tangentBit f z u (y + h • u) := by
  have h₁ := OracleTemplate.FrankWolfe.convex_support_on hc hm hp hdm.hasGradientAt
  have h₂ := OracleTemplate.FrankWolfe.convex_support_on hc hp hm hdp.hasGradientAt
  have he : y + h • u - (y - h • u) = (2 * h) • u := by module
  have he' : y - h • u - (y + h • u) = -((2 * h) • u) := by module
  rw [he, real_inner_smul_right] at h₁
  rw [he', inner_neg_right, real_inner_smul_right] at h₂
  unfold tangentBit secantBit
  rw [← bitSign_pos_smul (⟪gradient f (y - h • u) + z, u⟫) (show 0 < 2*h by positivity),
    ← bitSign_pos_smul (⟪gradient f (y + h • u) + z, u⟫) (show 0 < 2*h by positivity)]
  constructor <;> apply monotone_bitSign <;>
    simp only [sampleUtility, inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_right] <;>
    linarith

lemma ae_differentiable_shift {f : H → ℝ} {B : ℝ≥0} (hL : LipschitzWith B f) (v : H) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ f (v + x) := by
  have hm : MeasurePreserving (v + ·) (volume : Measure H) volume :=
    ⟨measurable_const.add measurable_id, map_add_left_eq_self volume v⟩
  exact hm.quasiMeasurePreserving.ae (hL.ae_differentiableAt (μ := volume))

lemma finite_comparison_bias {f : H → ℝ} {B : ℝ≥0} (hL : LipschitzWith B f)
    {C : Set H} (hc : ConvexOn ℝ C f) (z u m : H) {r h : ℝ} (hr : 0 < r)
    (hh : 0 < h) (hhr : h < r) (hu : ‖u‖ = 1)
    (hfeas : ∀ w ∈ ball (0 : H) r, m + w - h • u ∈ C ∧ m + w + h • u ∈ C) :
    |(∫ w, secantBit f z u (m + w) h ∂(jitterLaw d r : Measure H)) -
      ∫ w, tangentBit f z u (m + w) ∂(jitterLaw d r : Measure H)| ≤ 2 * d * h / r := by
  have hμ : (jitterLaw d r : Measure H) = ProbabilityTheory.cond volume (ball 0 r) := by
    simp [jitterLaw, hr]
  have hF : Measurable (fun w : H => tangentBit f z u (m + w)) := (tangent_measurable f z u).comp (measurable_const.add measurable_id)
  apply sandwich_bias hr hh.le hhr (h • u) (by simp [norm_smul, hu, abs_of_pos hh])
    (fun w => tangentBit f z u (m+w)) _ hF
  · unfold secantBit sampleUtility
    apply measurable_bitSign.comp
    have hf := hL.continuous.measurable
    fun_prop
  · intro w
    exact (bit_abs _).le
  · intro w
    exact (bit_abs _).le
  rw [hμ]
  have hdom := ProbabilityTheory.cond_absolutelyContinuous (μ := (volume : Measure H)) (s := ball 0 r)
  filter_upwards [hdom.ae_le (ae_differentiable_shift hL (m - h • u)),
    hdom.ae_le (ae_differentiable_shift hL (m + h • u)),
    ProbabilityTheory.ae_cond_mem (μ := (volume : Measure H)) measurableSet_ball] with w hminus hplus hw
  have h1 : m - h • u + w = m + w - h • u := by abel
  have h2 : m + h • u + w = m + w + h • u := by abel
  rw [h1] at hminus
  rw [h2] at hplus
  simpa only [show m + (-(h • u) + w) = m + w - h • u by abel,
    show m + (h • u + w) = m + w + h • u by abel] using
    secant_sandwich hc z u (m+w) hh (hfeas w hw).1 (hfeas w hw).2 hminus hplus

end LongTails.Proofs.SphericalPreferenceSecant
