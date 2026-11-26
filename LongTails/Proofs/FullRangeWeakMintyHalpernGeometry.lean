import LongTails.Algorithms.FullRangeWeakMintyHalpern
import Mathlib.Tactic

open scoped RealInnerProductSpace
namespace OracleTemplate.FullRangeWeakMintyHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local macro "gram" : tactic => `(tactic|
  (simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm] <;> ring))

private lemma depth_mul {δ : ℝ} {w y f : E} (hf : 0 < ‖f‖) :
    depth δ w y f * ‖f‖ = ⟪f,w-y⟫ - (1-δ)*‖f‖^2 := by
  unfold depth
  field_simp

lemma moderate {w b y v : E} {δ t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hd : 0 ≤ δ) (hv : 0 < ‖v‖)
    (hr : ‖y - center w b + v‖ ≤ t^2 / 16 * ‖v‖)
    (hl : ‖v-b‖ ≤ ‖y-w‖) (hb : t*‖v‖ ≤ ‖b‖) :
    t*‖b‖/16 ≤ depth δ w y v := by
  let r := y - center w b + v
  have id : (⟪v,w-y⟫ - (1-δ)*‖v‖^2) =
      δ*‖v‖^2 + ‖b‖^2/8 - 2/3*⟪v,r⟫ + 1/6*⟪b,r⟫ - ‖r‖^2/6 +
      (‖y-w‖^2 - ‖v-b‖^2)/6 := by
    dsimp [r, center]
    gram
  have hr' : ‖r‖ ≤ t*‖b‖/16 := by
    nlinarith only [hr, mul_le_mul_of_nonneg_left hb ht.le]
  have htB : t*‖b‖ ≤ ‖b‖ := mul_le_of_le_one_left (norm_nonneg _) ht1
  have hrB : ‖r‖ ≤ ‖b‖/16 := by linarith
  have hvr : ⟪v,r⟫ ≤ ‖b‖^2/16 := by
    have := mul_le_mul_of_nonneg_left hr' (norm_nonneg v)
    nlinarith only [this, real_inner_le_norm v r, mul_le_mul_of_nonneg_right hb (norm_nonneg b)]
  have hbr := real_inner_le_norm b (-r)
  rw [inner_neg_right, norm_neg] at hbr
  have hbrr := mul_le_mul_of_nonneg_left hrB (norm_nonneg b)
  have hrr := pow_le_pow_left₀ (norm_nonneg _) hrB 2
  apply le_of_mul_le_mul_right _ hv
  rw [depth_mul hv, id]
  nlinarith only [hvr, hbr, hbrr, hrr, sq_nonneg ‖b‖, mul_nonneg hd (sq_nonneg ‖v‖),
    pow_le_pow_left₀ (norm_nonneg _) hl 2, mul_le_mul_of_nonneg_right hb (norm_nonneg b)]

lemma large {w b y v u f : E} {δ t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hd : (t^2)^2 = δ) (hf : 0 < ‖f‖)
    (hr : ‖y - center w b + v‖ ≤ t^2/16 * ‖v‖)
    (hs : ‖u - average w y + f‖ ≤ t^2/16 * ‖f‖)
    (hw : ‖f-b‖ ≤ ‖u-w‖) (hy : ‖f-v‖ ≤ ‖u-y‖) (hb : ‖b‖ < t*‖v‖) :
    t*‖b‖/16 ≤ depth δ w u f := by
  let r := y - center w b + v
  let s := u - average w y + f
  have id : ⟪f,w-u⟫ - (1-δ)*‖f‖^2 =
      δ*‖f‖^2 + ‖b‖^2/6 + ‖v‖^2/3 - ‖y-w‖^2/9 - ‖s‖^2/2 - 2/3*⟪f,r⟫ +
      (‖u-w‖^2 - ‖f-b‖^2)/6 + (‖u-y‖^2 - ‖f-v‖^2)/3 := by
    dsimp [r,s,center,average]
    gram
  have ht2 : t^2 ≤ 1 := pow_le_one₀ ht.le ht1
  have hbv : ‖b‖ ≤ ‖v‖ := hb.le.trans (mul_le_of_le_one_left (norm_nonneg _) ht1)
  have hr' : ‖r‖ ≤ ‖v‖/16 := by
    nlinarith only [hr, mul_le_mul_of_nonneg_right ht2 (norm_nonneg v)]
  have hyw : ‖y-w‖ ≤ 25/16 * ‖v‖ := by
    have eq : y-w = r-v-(1/2:ℝ) • b := by dsimp [r, center]; module
    rw [eq]
    have h := norm_sub_le (r-v) ((1/2:ℝ) • b)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
    linarith [norm_sub_le r v]
  have hcross := (real_inner_le_norm f r).trans
    (mul_le_mul_of_nonneg_left hr (norm_nonneg f))
  have hss := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have ham := sq_nonneg (‖v‖ / 3 - t^2 * ‖f‖)
  have hbf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.le ht.le) hf.le
  apply le_of_mul_le_mul_right _ hf
  rw [depth_mul hf, id, ← hd]
  nlinarith only [ham, hbf, hcross, hss, sq_nonneg (t^2 * ‖f‖),
    mul_nonneg (sq_nonneg t) (mul_nonneg (norm_nonneg v) hf.le),
    sq_nonneg ‖b‖, sq_nonneg ‖v‖, pow_le_pow_left₀ (norm_nonneg _) hyw 2,
    pow_le_pow_left₀ (norm_nonneg _) hw 2, pow_le_pow_left₀ (norm_nonneg _) hy 2]

lemma project_progress {w y f z : E} {δ t e : ℝ} (ht : 0 < t) (he : 0 < e)
    (hf : 0 < ‖f‖) (h : t*e/16 < depth δ w y f)
    (hm : -(1-δ)*‖f‖^2 ≤ ⟪f,y-z⟫) :
    ‖project δ w y f-z‖^2 < ‖w-z‖^2 - t^2*e^2/256 := by
  let d := depth δ w y f
  have hd : 0 < d := lt_trans (by positivity) h
  have hinner : d*‖f‖ ≤ ⟪f,w-z⟫ := by
    rw [show w-z = (w-y)+(y-z) by abel, inner_add_right]
    dsimp [d]
    rw [depth_mul hf]
    linarith
  have id : ‖project δ w y f-z‖^2 =
      ‖w-z‖^2 - 2*(d/‖f‖)*⟪f,w-z⟫ + (d/‖f‖)^2*‖f‖^2 := by
    dsimp only [project,d]
    gram
  rw [id]
  have h₁ := mul_le_mul_of_nonneg_left hinner (div_nonneg hd.le hf.le)
  have eq : d/‖f‖*(d*‖f‖) = d^2 := by field_simp
  rw [eq] at h₁
  rw [show (d/‖f‖)^2*‖f‖^2 = d^2 by field_simp]
  have hsq : (t*e/16)^2 < d^2 := pow_lt_pow_left₀ h (by positivity) (by decide)
  nlinarith only [h₁, hsq]

end OracleTemplate.FullRangeWeakMintyHalpern
