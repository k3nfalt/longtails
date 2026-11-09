import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.CovarianceAcceleratedClipping

lemma clip_eq {z : ℝ} (hz : |z| ≤ 1) : max (-1) (min 1 z) = z := by
  rw [min_eq_right (abs_le.mp hz).2, max_eq_right (abs_le.mp hz).1]

lemma clip_abs_le (z : ℝ) : |max (-1) (min 1 z)| ≤ 1 := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clipped_shift_abs_le (a x : ℝ) :
    |max (-1) (min 1 (a + x)) - a| ≤ 1 + |a| := by
  have h := abs_sub (max (-1) (min 1 (a + x))) a
  have hclip := clip_abs_le (a + x)
  linarith

lemma clip_neg (z : ℝ) :
    max (-1) (min 1 (-z)) = -(max (-1) (min 1 z)) := by
  by_cases h : z ≤ -1
  · rw [min_eq_right (by linarith : z ≤ 1), max_eq_left h,
      min_eq_left (by linarith : 1 ≤ -z)]
    norm_num
  · by_cases h' : 1 ≤ z
    · rw [min_eq_left h', min_eq_right (by linarith : -z ≤ 1),
        max_eq_left (by linarith : -z ≤ -1)]
      norm_num
    · have hz : |z| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [clip_eq hz, clip_eq (by simpa using hz : |-z| ≤ 1)]

lemma exp_two_le_nine : Real.exp 2 ≤ 9 := by
  have h := Real.exp_one_lt_three
  have hp := Real.exp_pos 1
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith

lemma clipped_exp_upper {a x : ℝ} (ha : |a| ≤ 1 / 2) :
    Real.exp (max (-1) (min 1 (a + x)) - a) ≤ 1 + x + 40 * x ^ 2 := by
  by_cases hx : |x| ≤ 1 / 2
  · have hax : |a + x| ≤ 1 := (abs_add_le a x).trans (by linarith)
    rw [clip_eq hax, add_sub_cancel_left]
    have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
      (show |x| ≤ 1 by linarith))).2
    nlinarith [sq_nonneg x]
  · have hc : max (-1) (min 1 (a + x)) ≤ (1 : ℝ) :=
      max_le (by norm_num) (min_le_left _ _)
    have hb : max (-1) (min 1 (a + x)) - a ≤ (2 : ℝ) := by
      have := (abs_le.mp ha).1
      linarith
    have he := (Real.exp_le_exp.mpr hb).trans exp_two_le_nine
    have hr : (1 / 2 : ℝ) ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hs := mul_nonneg (sub_nonneg.mpr hr) (abs_nonneg x)
    nlinarith [sq_abs x, neg_abs_le x]

lemma clipped_exp_lower {a x : ℝ} (ha : |a| ≤ 1 / 2) :
    Real.exp (-(max (-1) (min 1 (a + x)) - a)) ≤ 1 - x + 40 * x ^ 2 := by
  have h := clipped_exp_upper (a := -a) (x := -x) (by simpa using ha)
  have he : -a + -x = -(a + x) := by ring
  rw [he, clip_neg] at h
  convert h using 1 <;> congr 1 <;> ring

lemma clipped_exp_split_upper {a v w : ℝ} (ha : |a| ≤ 1 / 2) :
    Real.exp (max (-1) (min 1 (a + (v + w))) - a) ≤
      1 + v + w + 80 * (v ^ 2 + w ^ 2) := by
  have h := clipped_exp_upper (x := v + w) ha
  nlinarith [sq_nonneg (v - w)]

lemma clipped_exp_split_lower {a v w : ℝ} (ha : |a| ≤ 1 / 2) :
    Real.exp (-(max (-1) (min 1 (a + (v + w))) - a)) ≤
      1 - v - w + 80 * (v ^ 2 + w ^ 2) := by
  have h := clipped_exp_lower (x := v + w) ha
  nlinarith [sq_nonneg (v - w)]

open MeasureTheory

lemma integral_quadratic_majorant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Z : Ω → ℝ} {c : ℝ}
    (hZ : Measurable Z) (hX : Integrable X P)
    (h2 : Integrable (fun ω => (X ω) ^ 2) P) (hmean : (∫ ω, X ω ∂P) = 0)
    (hpos : ∀ ω, 0 ≤ Z ω) (hbound : ∀ ω, Z ω ≤ 1 + X ω + c * (X ω) ^ 2) :
    Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 1 + c * (∫ ω, (X ω) ^ 2 ∂P) := by
  have hr : Integrable (fun ω => 1 + X ω + c * (X ω) ^ 2) P :=
    ((integrable_const 1).add hX).add (h2.const_mul c)
  have hi : Integrable Z P := hr.mono' hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω)]
      exact hbound ω)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hr hbound
  have hlin : Integrable (fun ω => 1 + X ω) P := (integrable_const 1).add hX
  rw [integral_add hlin (h2.const_mul c),
    integral_add (integrable_const 1) hX, integral_const_mul] at hh
  simpa [hmean] using hh

lemma clipped_exp_integral_upper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {a : ℝ}
    (hX : Measurable X) (hi : Integrable X P)
    (h2 : Integrable (fun ω => (X ω) ^ 2) P) (hmean : (∫ ω, X ω ∂P) = 0)
    (ha : |a| ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (max (-1) (min 1 (a + X ω)) - a)) P ∧
      (∫ ω, Real.exp (max (-1) (min 1 (a + X ω)) - a) ∂P) ≤
        1 + 40 * (∫ ω, (X ω) ^ 2 ∂P) := by
  apply integral_quadratic_majorant P (X := X) (c := 40) (by fun_prop)
    hi h2 hmean
  · exact fun ω => (Real.exp_pos _).le
  · exact fun ω => clipped_exp_upper ha

lemma clipped_exp_integral_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {a : ℝ}
    (hX : Measurable X) (hi : Integrable X P)
    (h2 : Integrable (fun ω => (X ω) ^ 2) P) (hmean : (∫ ω, X ω ∂P) = 0)
    (ha : |a| ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (-(max (-1) (min 1 (a + X ω)) - a))) P ∧
      (∫ ω, Real.exp (-(max (-1) (min 1 (a + X ω)) - a)) ∂P) ≤
        1 + 40 * (∫ ω, (X ω) ^ 2 ∂P) := by
  have hneg : Integrable (fun ω => (-X ω) ^ 2) P := by simpa using h2
  have hm : (∫ ω, -X ω ∂P) = 0 := by rw [integral_neg, hmean, neg_zero]
  have h := integral_quadratic_majorant P (X := fun ω => -X ω) (c := 40)
    (Z := fun ω => Real.exp (-(max (-1) (min 1 (a + X ω)) - a)))
    (by fun_prop) hi.neg hneg hm (fun ω => (Real.exp_pos _).le)
    (fun ω => by simpa [sub_eq_add_neg] using clipped_exp_lower (x := X ω) ha)
  simpa using h

lemma clipped_exp_integral_global {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (a sign : ℝ) (hsign : |sign| ≤ 1) :
    Integrable (fun ω => Real.exp (sign * (max (-1) (min 1 (a + X ω)) - a))) P ∧
      (∫ ω, Real.exp (sign * (max (-1) (min 1 (a + X ω)) - a)) ∂P) ≤
        Real.exp (1 + |a|) := by
  have hbound (ω) : Real.exp (sign * (max (-1) (min 1 (a + X ω)) - a)) ≤
      Real.exp (1 + |a|) := by
    apply Real.exp_le_exp.mpr
    calc
      sign * (max (-1) (min 1 (a + X ω)) - a) ≤
          |sign * (max (-1) (min 1 (a + X ω)) - a)| := le_abs_self _
      _ = |sign| * |max (-1) (min 1 (a + X ω)) - a| := abs_mul _ _
      _ ≤ 1 * |max (-1) (min 1 (a + X ω)) - a| :=
        mul_le_mul_of_nonneg_right hsign (abs_nonneg _)
      _ ≤ _ := by simpa using clipped_shift_abs_le a (X ω)
  have hi : Integrable (fun ω => Real.exp (sign *
      (max (-1) (min 1 (a + X ω)) - a))) P :=
    (integrable_const (Real.exp (1 + |a|))).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hbound ω)
  refine ⟨hi, ?_⟩
  simpa using integral_mono hi (integrable_const (Real.exp (1 + |a|))) hbound

lemma clipped_exp_integral_mixed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {a sign : ℝ}
    (hX : Measurable X) (hi : Integrable X P)
    (h2 : Integrable (fun ω => (X ω) ^ 2) P) (hmean : (∫ ω, X ω ∂P) = 0)
    (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun ω => Real.exp (sign * (max (-1) (min 1 (a + X ω)) - a))) P ∧
      (∫ ω, Real.exp (sign * (max (-1) (min 1 (a + X ω)) - a)) ∂P) ≤
        1 + 40 * (∫ ω, (X ω) ^ 2 ∂P) +
          (if 1 / 2 < |a| then Real.exp (1 + |a|) else 0) := by
  have hs : |sign| ≤ 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hg := clipped_exp_integral_global P hX a sign hs
  refine ⟨hg.1, ?_⟩
  by_cases ha : |a| ≤ 1 / 2
  · rw [ite_eq_right (not_lt.mpr ha), add_zero]
    rcases hsign with rfl | rfl
    · simpa using (clipped_exp_integral_upper P hX hi h2 hmean ha).2
    · simpa using (clipped_exp_integral_lower P hX hi h2 hmean ha).2
  · rw [ite_eq_left (lt_of_not_ge ha)]
    have hv : 0 ≤ (∫ ω, (X ω) ^ 2 ∂P) := integral_nonneg (fun ω => sq_nonneg _)
    linarith [hg.2]

end LongTails.Proofs.CovarianceAcceleratedClipping
