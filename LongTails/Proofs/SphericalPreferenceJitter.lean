import LongTails.Algorithms.SphericalPreferenceDescent
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory MeasureTheory.Measure Metric Set Filter
open scoped ENNReal

namespace LongTails.Proofs.SphericalPreferenceJitter

open LongTails.Algorithms.SphericalPreferenceDescent LongTails.Setups.SphericalRandomUtility

variable {d : ℕ}
local notation "H" => Point d
local notation "V" => (volume : Measure H)

lemma collar_bound {r h : ℝ} (hr : 0 < r) (_hh : 0 ≤ h) (hhr : h < r) (v : H) :
    (V).real (ball v r) - (V).real (ball 0 (r - h)) ≤
      d * h / r * (V).real (ball 0 r) := by
  let a := 1 - h / r
  have ha : 0 < a := by dsimp [a]; rw [sub_pos, div_lt_one hr]; exact hhr
  have hab : r - h = a * r := by dsimp [a]; field_simp
  have he : (V).real (ball 0 (r - h)) = a ^ d * (V).real (ball 0 r) := by
    rw [hab, measureReal_def, addHaar_ball_mul_of_pos V _ ha, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ha.le _)]
    simp [Point, measureReal_def]
  rw [addHaar_real_ball_center V v r, he]
  have ht : -2 ≤ -(h / r) := by have := (div_lt_one hr).mpr hhr; linarith
  have hpow := one_add_mul_le_pow ht d
  have ha' : 1 + -(h / r) = a := by ring
  rw [ha'] at hpow
  have := mul_le_mul_of_nonneg_right hpow (measureReal_nonneg : 0 ≤ (V).real (ball 0 r))
  ring_nf at this ⊢
  linarith only [this]

lemma shift_integral (F : H → ℝ) (hm : Measurable F) (v : H) (r : ℝ) :
    (∫ x in ball 0 r, F (v + x)) = ∫ x in ball v r, F x := by
  have hs : (v + ·) ⁻¹' ball v r = ball 0 r := by ext x; simp
  have hm' : Measurable (v + ·) := measurable_const.add measurable_id
  have he := Measure.restrict_map (μ := V) hm' (s := ball v r) measurableSet_ball
  rw [hs, map_add_left_eq_self] at he
  rw [← integral_map hm'.aemeasurable hm.aestronglyMeasurable, ← he]

lemma setIntegral_collar {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hhr : h < r)
    (v : H) (hv : ‖v‖ ≤ h) (F : H → ℝ) (hm : Measurable F) (hF : ∀ x, ‖F x‖ ≤ 1) :
    |(∫ x in ball v r, F x) - ∫ x in ball 0 (r - h), F x| ≤
      d * h / r * (V).real (ball 0 r) := by
  have hsub : ball 0 (r - h) ⊆ ball v r := by
    intro x hx
    have hx' := mem_ball_zero_iff.mp hx
    have hd := norm_sub_le x v
    rw [mem_ball, dist_eq_norm]
    linarith
  have hi := (V).integrableOn_of_bounded (s := ball v r) measure_ball_lt_top.ne
    hm.aestronglyMeasurable (Eventually.of_forall hF)
  rw [← setIntegral_sdiff measurableSet_ball hi hsub, ← Real.norm_eq_abs]
  have ht : V (ball v r \ ball 0 (r - h)) < ∞ :=
    (measure_mono sdiff_subset).trans_lt measure_ball_lt_top
  have := norm_setIntegral_le_of_norm_le_const (f := F) ht (fun x _ => hF x)
  rw [one_mul, measureReal_sdiff hsub measurableSet_ball measure_ball_lt_top.ne] at this
  exact this.trans (collar_bound hr hh hhr v)

lemma jitter_shift {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hhr : h < r)
    (v : H) (hv : ‖v‖ ≤ h) (F : H → ℝ) (hm : Measurable F) (hF : ∀ x, ‖F x‖ ≤ 1) :
    |(∫ x, F (v + x) ∂(jitterLaw d r : Measure H)) -
      ∫ x, F x ∂(jitterLaw d r : Measure H)| ≤ 2 * d * h / r := by
  have hμ : (jitterLaw d r : Measure H) = (V (ball 0 r))⁻¹ • (V).restrict (ball 0 r) := by
    simp [jitterLaw, hr, ProbabilityTheory.cond]
  rw [hμ, integral_smul_measure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    smul_eq_mul, ← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
    shift_integral F hm v r]
  have hpos : 0 < (V).real (ball 0 r) :=
    ENNReal.toReal_pos (measure_ball_pos V 0 hr).ne' measure_ball_lt_top.ne
  change ((V).real (ball 0 r))⁻¹ * _ ≤ _
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  have h₁ := setIntegral_collar hr hh hhr v hv F hm hF
  have h₂ := setIntegral_collar hr hh hhr 0 (by simpa using hh) F hm hF
  rw [abs_le] at h₁ h₂ ⊢
  change -(2 * (d : ℝ) * h / r * (V).real (ball 0 r)) ≤ _ ∧ _ ≤ _
  rw [show 2 * (d : ℝ) * h / r * (V).real (ball 0 r) = 2 * ((d : ℝ) * h / r * (V).real (ball 0 r)) by ring]
  constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2]

lemma sandwich_bias {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hhr : h < r)
    (v : H) (hv : ‖v‖ ≤ h) (F G : H → ℝ) (hm : Measurable F) (hmG : Measurable G)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hG : ∀ x, ‖G x‖ ≤ 1)
    (hs : ∀ᵐ x ∂(jitterLaw d r : Measure H), F (-v + x) ≤ G x ∧ G x ≤ F (v + x)) :
    |(∫ x, G x ∂(jitterLaw d r : Measure H)) - ∫ x, F x ∂(jitterLaw d r : Measure H)| ≤
      2 * d * h / r := by
  let μ : Measure H := jitterLaw d r
  have hi (w : H) : Integrable (fun x => F (w + x)) μ :=
    Integrable.of_bound (hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => hF (w + x))
  have hI : Integrable G μ := Integrable.of_bound hmG.aestronglyMeasurable 1 (Eventually.of_forall hG)
  have hleft := integral_mono_ae (hi (-v)) hI (hs.mono fun _ hx => hx.1)
  have hright := integral_mono_ae hI (hi v) (hs.mono fun _ hx => hx.2)
  dsimp [μ] at hleft hright
  have hm' := (abs_le.mp (jitter_shift hr hh hhr (-v) (by simpa using hv) F hm hF)).1
  have hp' := (abs_le.mp (jitter_shift hr hh hhr v hv F hm hF)).2
  exact abs_le.mpr ⟨by linarith only [hm', hleft], by linarith only [hp', hright]⟩

end LongTails.Proofs.SphericalPreferenceJitter
