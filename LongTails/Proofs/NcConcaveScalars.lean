import LongTails.Proofs.SmoothConvexFiniteGeometry
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Topology

namespace LongTails.Proofs.NcConcaveScalars

open LongTails.Proofs.SmoothConvexFiniteGeometry

lemma hasDerivAt_of_model {f f' : ℝ → ℝ} {C : ℝ}
    (h : ∀ x y, |f y - f x - f' x * (y - x)| ≤ C * (y - x) ^ 2) (x : ℝ) :
    HasDerivAt f (f' x) x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun y => f y - f x - (y - x) • f' x) =O[nhds x] (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound |C|
    filter_upwards [] with y
    have hy := h x y
    simp only [Real.norm_eq_abs, smul_eq_mul, mul_comm (y - x), sq_abs,
      abs_of_nonneg (sq_nonneg (y - x))]
    calc |f y - f x - f' x * (y - x)| ≤ C * (y - x) ^ 2 := hy
      _ ≤ |C| * (y - x) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

noncomputable def nu (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then 3 * t ^ 2 - 2 * t ^ 3 else 1

noncomputable def rr (t : ℝ) : ℝ := t - 2 * ramp t

noncomputable def drr (t : ℝ) : ℝ := 1 - 2 * rampSlope t

noncomputable def dnu (t : ℝ) : ℝ := 6 * max 0 (rr t)

lemma rr_cases (t : ℝ) : rr t = if t ≤ 0 then t else if t ≤ 1 then t * (1 - t) else 1 - t := by
  simp only [rr, ramp]
  split_ifs <;> ring

lemma drr_cases (t : ℝ) : drr t = if t ≤ 0 then 1 else if t ≤ 1 then 1 - 2 * t else -1 := by
  simp only [drr, rampSlope_cases]
  split_ifs <;> ring

lemma dnu_cases (t : ℝ) : dnu t = if t ≤ 0 then 0 else if t ≤ 1 then 6 * (t * (1 - t)) else 0 := by
  simp only [dnu, rr_cases]
  split_ifs with h1 h2
  · rw [max_eq_left h1]; ring
  · rw [max_eq_right (by nlinarith)]
  · rw [max_eq_left (by linarith)]; ring

lemma rr_model (x y : ℝ) : |rr y - rr x - drr x * (y - x)| ≤ 1 * (y - x) ^ 2 := by
  rw [abs_le]
  simp only [rr_cases, drr_cases]
  split_ifs <;> constructor <;>
    nlinarith [sq_nonneg (y - x), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_self_nonneg x,
      mul_self_nonneg y]

lemma rr_hasDerivAt (x : ℝ) : HasDerivAt rr (drr x) x := hasDerivAt_of_model rr_model x

lemma nu_model (x y : ℝ) : |nu y - nu x - dnu x * (y - x)| ≤ 3 * (y - x) ^ 2 := by
  rw [abs_le]
  simp only [nu, dnu_cases]
  split_ifs <;> constructor <;>
    nlinarith [sq_nonneg (y - x), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_self_nonneg x,
      mul_self_nonneg y, mul_nonneg (sq_nonneg (y - x)) (sq_nonneg x),
      mul_nonneg (sq_nonneg (y - x)) (sq_nonneg (y - 1))]

lemma nu_hasDerivAt (x : ℝ) : HasDerivAt nu (dnu x) x := hasDerivAt_of_model nu_model x

lemma nu_nonneg (t : ℝ) : 0 ≤ nu t := by
  simp only [nu]; split_ifs <;> nlinarith

lemma nu_le_one (t : ℝ) : nu t ≤ 1 := by
  simp only [nu]; split_ifs <;> nlinarith [sq_nonneg (t - 1)]

lemma nu_of_nonpos {t : ℝ} (h : t ≤ 0) : nu t = 0 := by simp [nu, h]

lemma dnu_of_nonpos {t : ℝ} (h : t ≤ 0) : dnu t = 0 := by simp [dnu_cases, h]

lemma dnu_nonneg (t : ℝ) : 0 ≤ dnu t := by
  simp only [dnu]; positivity

lemma dnu_le (t : ℝ) : dnu t ≤ 3 / 2 := by
  simp only [dnu_cases]; split_ifs <;> nlinarith [sq_nonneg (2 * t - 1)]

lemma dnu_lipschitz (x y : ℝ) : |dnu x - dnu y| ≤ 6 * |x - y| := by
  simp only [dnu_cases]
  rw [abs_le]
  constructor <;> split_ifs <;> cases abs_cases (x - y) <;> nlinarith

lemma drr_abs (t : ℝ) : |drr t| ≤ 1 := by
  rw [drr_cases, abs_le]; split_ifs <;> constructor <;> linarith

lemma drr_lipschitz (x y : ℝ) : |drr x - drr y| ≤ 2 * |x - y| := by
  have h := rampSlope_lipschitz x y
  simp only [drr]
  rw [show 1 - 2 * rampSlope x - (1 - 2 * rampSlope y) = -2 * (rampSlope x - rampSlope y) by ring,
    abs_mul]
  norm_num
  linarith

lemma rr_lipschitz (x y : ℝ) : |rr x - rr y| ≤ |x - y| := by
  simp only [rr_cases, abs_le]
  constructor <;> split_ifs <;> cases abs_cases (x - y) <;> nlinarith

lemma rr_zero : rr 0 = 0 := by simp [rr_cases]

lemma drr_zero : drr 0 = 1 := by simp [drr_cases]

lemma rr_one : rr 1 = 0 := by simp [rr_cases]

lemma abs_rr_le (t : ℝ) : |rr t| ≤ |t| := by
  have h := rr_lipschitz t 0
  rwa [rr_zero, sub_zero, sub_zero] at h

lemma dnu_eq_six_rr {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : dnu t = 6 * rr t := by
  simp only [dnu, max_eq_right (show 0 ≤ rr t by rw [rr_cases]; simp [h0.not_ge, h1.le]; nlinarith)]

lemma nu_le_two_abs_rr {κ t : ℝ} (_hκ : 0 ≤ κ) (hκ8 : κ < 1 / 8) (ht : t ≤ 2 * κ) :
    nu t ≤ 2 * |rr t| := by
  simp only [nu, rr_cases]
  split_ifs with h1 h2
  · positivity
  · rw [abs_of_nonneg (by nlinarith)]; nlinarith
  · linarith

lemma drr_ge {κ t : ℝ} (hκ : 0 ≤ κ) (ht : t ≤ 2 * κ) : 1 - 4 * κ ≤ drr t := by
  simp only [drr_cases]; split_ifs <;> linarith

lemma one_sub_nu_le {κ t : ℝ} (_hκ : 0 ≤ κ) (hκ8 : κ < 1 / 8) (ht : 1 - 2 * κ ≤ t) :
    1 - nu t ≤ 2 * |rr t| := by
  simp only [nu, rr_cases]
  split_ifs with h1 h2
  · linarith
  · rw [abs_of_nonneg (by nlinarith)]; nlinarith [sq_nonneg (1 - t)]
  · simp

end LongTails.Proofs.NcConcaveScalars
