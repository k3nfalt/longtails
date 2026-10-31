import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate

noncomputable def clip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ) (v : E) : E :=
  if ‖v‖ ≤ B then v else (B / ‖v‖) • v

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clip_eq_self {B : ℝ} {v : E} (hv : ‖v‖ ≤ B) : clip B v = v := ite_eq_left hv

lemma norm_clip_le {B : ℝ} (hB : 0 ≤ B) (v : E) : ‖clip B v‖ ≤ B := by
  unfold clip
  split_ifs with h
  · exact h
  · have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_cancel₀ _ hv.ne']

lemma measurable_clip [MeasurableSpace E] [BorelSpace E] (B : ℝ) : Measurable (clip (E := E) B) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    ((measurable_const.div measurable_norm).smul measurable_id)

lemma clip_residual_norm {B : ℝ} (hB : 0 ≤ B) (v : E) :
    ‖v - clip B v‖ = max 0 (‖v‖ - B) := by
  unfold clip
  split_ifs with h
  · simp [max_eq_left (sub_nonpos.mpr h)]
  · have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
    rw [show v - (B / ‖v‖) • v = (1 - B / ‖v‖) • v by rw [sub_smul, one_smul],
      norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by rw [sub_nonneg, div_le_iff₀ hv]; simpa using (lt_of_not_ge h).le),
      max_eq_right (by linarith : 0 ≤ ‖v‖ - B)]
    field_simp

lemma norm_clip_sub_le {B : ℝ} (hB : 0 ≤ B) {u : E} (hu : ‖u‖ ≤ B) (v : E) :
    ‖clip B v - u‖ ≤ ‖v - u‖ := by
  unfold clip
  split_ifs with h
  · rfl
  · have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
    have hb : 0 ≤ B / ‖v‖ := by positivity
    have hratio : B / ‖v‖ ≤ 1 := (div_le_one hv).mpr (lt_of_not_ge h).le
    have hcancel : (B / ‖v‖) * ‖v‖ = B := div_mul_cancel₀ _ hv.ne'
    have hi : ⟪v, u⟫ ≤ ‖v‖ * B :=
      (real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_left hu hv.le)
    have hsq : ‖(B / ‖v‖) • v - u‖ ^ 2 ≤ ‖v - u‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hb, hcancel]
      have hh := mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hi)
      nlinarith [sq_nonneg (‖v‖ - B)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma sq_le_rpow_mul {a b p : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hp : p ≤ 2) :
    a ^ 2 ≤ b ^ (2 - p) * a ^ p := by
  by_cases hz : a = 0
  · subst a
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (Real.rpow_nonneg (ha.trans hab) _) (Real.rpow_nonneg ha _)
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  have h := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow ha hab (sub_nonneg.mpr hp)) (Real.rpow_nonneg ha p)
  rw [← Real.rpow_add ha', sub_add_cancel, Real.rpow_two] at h
  exact h

lemma norm_clip_sub_sq_le {B p : ℝ} (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp : p ≤ 2) {u : E}
    (hu : ‖u‖ ≤ B) (v : E) :
    ‖clip B v - u‖ ^ 2 ≤ (2 * B) ^ (2 - p) * ‖v - u‖ ^ p := by
  have hclip := norm_clip_sub_le hB hu v
  have hbounded : ‖clip B v - u‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by have := norm_clip_le hB v; linarith)
  exact (sq_le_rpow_mul (norm_nonneg _) hbounded hp).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hclip hp0)
      (Real.rpow_nonneg (by positivity) _))

lemma clip_residual_le_moment {B p : ℝ} (hB : 0 < B) (hp : 1 ≤ p) {u : E}
    (hu : ‖u‖ ≤ B / 2) (v : E) :
    ‖v - clip B v‖ ≤ ‖v - u‖ ^ p / (B / 2) ^ (p - 1) := by
  by_cases hv : ‖v‖ ≤ B
  · rw [clip_eq_self hv, sub_self, norm_zero]
    positivity
  have ht : B / 2 ≤ ‖v - u‖ := by
    have h := norm_sub_norm_le v u
    linarith [lt_of_not_ge hv]
  have he : 0 < ‖v - u‖ := lt_of_lt_of_le (by positivity) ht
  have hr : ‖v - clip B v‖ ≤ ‖v - u‖ := by
    rw [clip_residual_norm hB.le, max_eq_right (by linarith : 0 ≤ ‖v‖ - B)]
    have := norm_sub_norm_le v u
    linarith
  apply hr.trans
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < B / 2) _)).mpr
  have hh := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity : 0 ≤ B / 2) ht (sub_nonneg.mpr hp)) he.le
  calc
    _ ≤ ‖v - u‖ * ‖v - u‖ ^ (p - 1) := hh
    _ = ‖v - u‖ ^ p := by
      nth_rw 1 [← Real.rpow_one ‖v - u‖]
      rw [← Real.rpow_add he]
      congr 1
      ring

lemma inner_clip_residual_nonpos {B : ℝ} (hB : 0 ≤ B) {u : E} (hu : ‖u‖ ≤ B) (v : E) :
    ⟪v - clip B v, u - clip B v⟫ ≤ 0 := by
  unfold clip
  split_ifs with h
  · simp
  have hv : 0 < ‖v‖ := lt_of_le_of_lt hB (lt_of_not_ge h)
  have hr : 0 ≤ 1 - B / ‖v‖ := sub_nonneg.mpr ((div_le_one hv).mpr (lt_of_not_ge h).le)
  have hi : ⟪v, u⟫ ≤ ‖v‖ * B :=
    (real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_left hu hv.le)
  rw [show v - (B / ‖v‖) • v = (1 - B / ‖v‖) • v by rw [sub_smul, one_smul],
    real_inner_smul_left, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  apply mul_nonpos_of_nonneg_of_nonpos hr
  have he : B / ‖v‖ * ‖v‖ ^ 2 = ‖v‖ * B := by field_simp
  rw [he]
  linarith

lemma norm_clip_sub_sq_add_residual_le {B : ℝ} (hB : 0 ≤ B) {u : E} (hu : ‖u‖ ≤ B) (v : E) :
    ‖clip B v - u‖ ^ 2 + ‖v - clip B v‖ ^ 2 ≤ ‖v - u‖ ^ 2 := by
  have hi := inner_clip_residual_nonpos hB hu v
  have he : v - u = (v - clip B v) + (clip B v - u) := by abel
  rw [he, norm_add_sq_real]
  have he' : u - clip B v = -(clip B v - u) := by abel
  rw [he', inner_neg_right] at hi
  linarith

end OracleTemplate
