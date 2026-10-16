import LongTails.Proofs.Clipping
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ScalarClippedMoments

open OracleTemplate

lemma clipped_norm_le_input {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {τ : ℝ} (hτ : 0 ≤ τ) (a : E) : ‖clip τ a‖ ≤ ‖a‖ := by
  by_cases h : ‖a‖ ≤ τ
  · rw [clip_eq_self h]
  · exact (norm_clip_le hτ a).trans (le_of_not_ge h)

lemma scalar_clip_eq_clamp {τ : ℝ} (hτ : 0 ≤ τ) (a : ℝ) :
    clip τ a = max (-τ) (min τ a) := by
  by_cases h : |a| ≤ τ
  · have ha : a ≤ τ := (le_abs_self a).trans h
    have hn : -τ ≤ a := neg_le_of_abs_le h
    simp only [clip, Real.norm_eq_abs, ite_eq_left h, min_eq_right ha, max_eq_right hn]
  · have ht : τ < |a| := lt_of_not_ge h
    have ha0 : a ≠ 0 := by intro ha; simp [ha] at ht; linarith
    simp only [clip, Real.norm_eq_abs, ite_eq_right h, smul_eq_mul]
    by_cases ha : 0 ≤ a
    · have hta : τ ≤ a := by simpa only [abs_of_nonneg ha] using ht.le
      rw [min_eq_left hta, max_eq_right (by linarith : -τ ≤ τ), abs_of_nonneg ha]
      exact div_mul_cancel₀ _ ha0
    · have han : a < 0 := lt_of_not_ge ha
      have hat : a ≤ -τ := by rw [abs_of_neg han] at ht; linarith
      rw [min_eq_right (by linarith : a ≤ τ), max_eq_left hat, abs_of_neg han]
      field_simp

lemma scalar_clip_lipschitz {τ : ℝ} (hτ : 0 ≤ τ) :
    LipschitzWith 1 (clip (E := ℝ) τ) := by
  have he : clip (E := ℝ) τ = fun a => max (-τ) (min τ a) :=
    funext (scalar_clip_eq_clamp hτ)
  rw [he]
  exact (LipschitzWith.id.const_min τ).const_max (-τ)

lemma scalar_clip_difference {τ : ℝ} (hτ : 0 ≤ τ) (a b : ℝ) :
    |clip τ a - clip τ b| ≤ |a - b| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (scalar_clip_lipschitz hτ).dist_le_mul a b

lemma scalar_clipped_even_power {τ : ℝ} (hτ : 0 ≤ τ) (a : ℝ) (k : ℕ) :
    |clip τ a| ^ (2 * (k + 1)) ≤ a ^ 2 * τ ^ (2 * k) := by
  have hi : |clip τ a| ^ 2 ≤ a ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (clipped_norm_le_input hτ a) 2
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have ht : |clip τ a| ^ (2 * k) ≤ τ ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using norm_clip_le hτ a) _
  rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
  exact mul_le_mul hi ht (pow_nonneg (abs_nonneg _) _) (sq_nonneg _)

lemma scalar_clipped_weighted_even_power {τ : ℝ} (hτ : 0 ≤ τ) (a w : ℝ) (k : ℕ) :
    |clip τ a * w| ^ (2 * (k + 1)) ≤
      τ ^ (2 * k) * (a ^ 2 * |w| ^ (2 * (k + 1))) := by
  rw [abs_mul, mul_pow]
  have h := mul_le_mul_of_nonneg_right (scalar_clipped_even_power hτ a k)
    (pow_nonneg (abs_nonneg w) (2 * (k + 1)))
  nlinarith only [h]

lemma scalar_clipped_weighted_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {a w : Ω → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : Measurable a) (hw : Measurable w) (k : ℕ)
    (hi : Integrable (fun ξ => a ξ ^ 2 * |w ξ| ^ (2 * (k + 1))) P) :
    Integrable (fun ξ => |clip τ (a ξ) * w ξ| ^ (2 * (k + 1))) P ∧
      (∫ ξ, |clip τ (a ξ) * w ξ| ^ (2 * (k + 1)) ∂P) ≤
        τ ^ (2 * k) * ∫ ξ, a ξ ^ 2 * |w ξ| ^ (2 * (k + 1)) ∂P := by
  have hm : Measurable (fun ξ => |clip τ (a ξ) * w ξ| ^ (2 * (k + 1))) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_def] using ((((measurable_clip τ).comp ha).mul hw).norm.pow_const (2 * (k + 1)))
  have hb := fun ξ => scalar_clipped_weighted_even_power hτ (a ξ) (w ξ) k
  have hI : Integrable (fun ξ => |clip τ (a ξ) * w ξ| ^ (2 * (k + 1))) P := by
    apply (hi.const_mul (τ ^ (2 * k))).mono' hm.aestronglyMeasurable
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact hb ξ
  refine ⟨hI, ?_⟩
  have h := integral_mono hI (hi.const_mul (τ ^ (2 * k))) hb
  simpa only [integral_const_mul] using h

lemma perturbed_weighted_square_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {a c w : Ω → ℝ} {h : ℝ}
    (ha : Measurable a) (hc : Measurable c) (hw : Measurable w)
    (hcB : ∀ ξ, |c ξ| ≤ h) (k : ℕ)
    (hi : Integrable (fun ξ => a ξ ^ 2 * |w ξ| ^ k) P)
    (hwi : Integrable (fun ξ => |w ξ| ^ k) P) :
    Integrable (fun ξ => (a ξ + c ξ) ^ 2 * |w ξ| ^ k) P ∧
      (∫ ξ, (a ξ + c ξ) ^ 2 * |w ξ| ^ k ∂P) ≤
        2 * (∫ ξ, a ξ ^ 2 * |w ξ| ^ k ∂P) + 2 * h ^ 2 * (∫ ξ, |w ξ| ^ k ∂P) := by
  have hp (ξ : Ω) : (a ξ + c ξ) ^ 2 * |w ξ| ^ k ≤
      2 * (a ξ ^ 2 * |w ξ| ^ k) + 2 * h ^ 2 * |w ξ| ^ k := by
    have hc2 : c ξ ^ 2 ≤ h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcB ξ) 2
    have hs : (a ξ + c ξ) ^ 2 ≤ 2 * a ξ ^ 2 + 2 * h ^ 2 := by
      nlinarith [sq_nonneg (a ξ - c ξ)]
    have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (abs_nonneg (w ξ)) k)
    nlinarith only [hm]
  have hW : Measurable (fun ξ => |w ξ| ^ k) := by
    simpa only [Real.norm_eq_abs] using hw.norm.pow_const k
  have hI := (hi.const_mul 2).add (hwi.const_mul (2 * h ^ 2))
  have hJ : Integrable (fun ξ => (a ξ + c ξ) ^ 2 * |w ξ| ^ k) P := by
    apply hI.mono' (((ha.add hc).pow_const 2).mul hW).aestronglyMeasurable
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg _) _))]
    exact hp ξ
  refine ⟨hJ, ?_⟩
  have hb := integral_mono hJ hI hp
  simpa only [Pi.add_apply, integral_add (hi.const_mul 2) (hwi.const_mul (2 * h ^ 2)), integral_const_mul] using hb

lemma scalar_clipped_perturbed_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {a c w : Ω → ℝ} {τ h : ℝ} (hτ : 0 ≤ τ)
    (ha : Measurable a) (hc : Measurable c) (hw : Measurable w)
    (hcB : ∀ ξ, |c ξ| ≤ h) (k : ℕ)
    (hi : Integrable (fun ξ => a ξ ^ 2 * |w ξ| ^ (2 * (k + 1))) P)
    (hwi : Integrable (fun ξ => |w ξ| ^ (2 * (k + 1))) P) :
    Integrable (fun ξ => |clip τ (a ξ + c ξ) * w ξ| ^ (2 * (k + 1))) P ∧
      (∫ ξ, |clip τ (a ξ + c ξ) * w ξ| ^ (2 * (k + 1)) ∂P) ≤
        τ ^ (2 * k) * (2 * (∫ ξ, a ξ ^ 2 * |w ξ| ^ (2 * (k + 1)) ∂P) +
          2 * h ^ 2 * (∫ ξ, |w ξ| ^ (2 * (k + 1)) ∂P)) := by
  have hP := perturbed_weighted_square_moment ha hc hw hcB (2 * (k + 1)) hi hwi
  have hC := scalar_clipped_weighted_moment hτ (ha.add hc) hw k hP.1
  exact ⟨hC.1, hC.2.trans (mul_le_mul_of_nonneg_left hP.2 (pow_nonneg hτ _))⟩


lemma centered_vector_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → E}
    (hG : Integrable G P) (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) P) :
    Integrable (fun ω => ‖G ω - ∫ z, G z ∂P‖ ^ 2) P ∧
      (∫ ω, ‖G ω - ∫ z, G z ∂P‖ ^ 2 ∂P) ≤ ∫ ω, ‖G ω‖ ^ 2 ∂P := by
  let m := ∫ z, G z ∂P
  have heq : (fun ω => ‖G ω - m‖ ^ 2) =
      fun ω => ‖G ω‖ ^ 2 - 2 * ⟪m, G ω⟫ + ‖m‖ ^ 2 := by
    funext ω
    rw [norm_sub_sq_real, real_inner_comm (G ω) m]
  have hi : Integrable (fun ω => ⟪m, G ω⟫) P := hG.const_inner m
  have hdiff : Integrable (fun ω => ‖G ω‖ ^ 2 - 2 * ⟪m, G ω⟫) P := hG2.sub (hi.const_mul 2)
  rw [heq]
  refine ⟨hdiff.add (integrable_const _), ?_⟩
  rw [integral_add hdiff (integrable_const _),
    integral_sub hG2 (hi.const_mul 2), integral_const_mul, integral_inner hG m]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  change (∫ ω, ‖G ω‖ ^ 2 ∂P) - 2 * ⟪m, m⟫ + ‖m‖ ^ 2 ≤ _
  rw [real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖m‖]


lemma scalar_clip_residual_square {τ : ℝ} (hτ : 0 ≤ τ) (a : ℝ) :
    τ * |clip τ a - a| ≤ a ^ 2 := by
  have he := clip_residual_norm hτ a
  simp only [Real.norm_eq_abs] at he
  rw [abs_sub_comm, he]
  by_cases ha : |a| ≤ τ
  · rw [max_eq_left (by linarith), mul_zero]
    exact sq_nonneg a
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (|a| - τ), sq_abs a]

lemma scalar_clip_weighted_residual {D τ : ℝ} (hD : 0 ≤ D) (hτ : 0 ≤ τ) (a w : ℝ) :
    6 * Real.sqrt D * τ * |(clip τ a - a) * w| ≤ 9 * a ^ 2 + D * (a ^ 2 * w ^ 2) := by
  have hr := mul_le_mul_of_nonneg_left (scalar_clip_residual_square hτ a)
    (show 0 ≤ 6 * Real.sqrt D * |w| by positivity)
  have hs := mul_nonneg (sq_nonneg a) (sq_nonneg (Real.sqrt D * |w| - 3))
  simp only [sub_sq, mul_pow, sq_abs, Real.sq_sqrt hD] at hs
  rw [abs_mul]
  nlinarith only [hr, hs]

lemma scalar_clipping_weighted_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {a w : Ω → ℝ} {D τ B : ℝ}
    (ha : Measurable a) (hw : Measurable w) (hD : 0 < D) (hτ : 0 < τ) (hB : 0 ≤ B)
    (hai : Integrable (fun z => a z ^ 2) P)
    (hwi : Integrable (fun z => a z ^ 2 * w z ^ 2) P)
    (hab : D * (∫ z, a z ^ 2 ∂P) ≤ 5 * B)
    (hwb : D ^ 2 * (∫ z, a z ^ 2 * w z ^ 2 ∂P) ≤ 40 * B) :
    Integrable (fun z => (clip τ (a z) - a z) * w z) P ∧
      D * |∫ z, (clip τ (a z) - a z) * w z ∂P| ≤ 15 * B / (Real.sqrt D * τ) := by
  let r := 6 * Real.sqrt D * τ
  have hr : 0 < r := by dsimp [r]; positivity
  have hm : Measurable (fun z => (clip τ (a z) - a z) * w z) :=
    (((measurable_clip τ).comp ha).sub ha).mul hw
  have hdom : Integrable (fun z => (9 * a z ^ 2 + D * (a z ^ 2 * w z ^ 2)) / r) P :=
    ((hai.const_mul 9).add (hwi.const_mul D)).div_const r
  have hp (z : Ω) : |(clip τ (a z) - a z) * w z| ≤
      (9 * a z ^ 2 + D * (a z ^ 2 * w z ^ 2)) / r := by
    apply (le_div_iff₀ hr).mpr
    have hh := scalar_clip_weighted_residual hD.le hτ.le (a z) (w z)
    dsimp [r]
    nlinarith only [hh]
  have hi : Integrable (fun z => (clip τ (a z) - a z) * w z) P := by
    apply hdom.mono' hm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using Filter.Eventually.of_forall hp
  have habs : |∫ z, (clip τ (a z) - a z) * w z ∂P| ≤
      ∫ z, |(clip τ (a z) - a z) * w z| ∂P := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := fun z => (clip τ (a z) - a z) * w z) (μ := P)
  have hh := habs.trans (integral_mono hi.norm hdom hp)
  rw [integral_div, integral_add (hai.const_mul 9) (hwi.const_mul D),
    integral_const_mul, integral_const_mul] at hh
  have hscaled := mul_le_mul_of_nonneg_left ((le_div_iff₀ hr).mp hh) hD.le
  refine ⟨hi, ?_⟩
  apply (le_div_iff₀ (show 0 < Real.sqrt D * τ by positivity)).mpr
  dsimp [r] at hscaled
  nlinarith

lemma bounded_directional_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {e w : Ω → ℝ} {D h : ℝ}
    (he : Measurable e) (hw : Measurable w) (hD : 0 < D) (hh : 0 ≤ h)
    (heb : ∀ z, |e z| ≤ h) (hwi : Integrable (fun z => w z ^ 2) P)
    (hwb : D * (∫ z, w z ^ 2 ∂P) ≤ 1) :
    Integrable (fun z => e z * w z) P ∧
      D * |∫ z, e z * w z ∂P| ≤ Real.sqrt D * h := by
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hp (z : Ω) : |e z * w z| ≤ h * (1 + D * w z ^ 2) / (2 * Real.sqrt D) := by
    have hy := sq_nonneg (Real.sqrt D * |w z| - 1)
    simp only [sub_sq, mul_pow, sq_abs, Real.sq_sqrt hD.le] at hy
    have hb := mul_le_mul_of_nonneg_right (heb z) (abs_nonneg (w z))
    have hyh := mul_le_mul_of_nonneg_left hy hh
    apply (le_div_iff₀ (by positivity)).mpr
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * Real.sqrt D by positivity)]
  have hdom : Integrable (fun z => h * (1 + D * w z ^ 2) / (2 * Real.sqrt D)) P :=
    (((integrable_const 1).add (hwi.const_mul D)).const_mul h).div_const _
  have hi : Integrable (fun z => e z * w z) P := by
    apply hdom.mono' (he.mul hw).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using Filter.Eventually.of_forall hp
  have hn : |∫ z, e z * w z ∂P| ≤ ∫ z, |e z * w z| ∂P := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := fun z => e z * w z) (μ := P)
  have hb := hn.trans (integral_mono hi.norm hdom hp)
  rw [integral_div, integral_const_mul,
    integral_add (integrable_const 1) (hwi.const_mul D), integral_const_mul] at hb
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hb
  have hc := (le_div_iff₀ (show 0 < 2 * Real.sqrt D by positivity)).mp hb
  have hmult := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg D)
  have hwb' := mul_le_mul_of_nonneg_left hwb hh
  refine ⟨hi, ?_⟩
  nlinarith [Real.sq_sqrt hD.le]

end LongTails.Proofs.ScalarClippedMoments
