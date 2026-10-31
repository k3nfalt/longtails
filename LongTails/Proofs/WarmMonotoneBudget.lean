import LongTails.Proofs.WarmMonotoneRun
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.WarmAnchoredMonotone

noncomputable def finishScalar (A C : ℝ) : ℝ :=
  11 * A + (27 * C + 4) * Real.log (1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))))

lemma finishScalar_nonneg {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) : 0 ≤ finishScalar A C := by
  unfold finishScalar
  have hl : 0 ≤ Real.log (1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3)))) :=
    Real.log_nonneg (by
      have hh : 0 ≤ 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))) := by positivity
      linarith)
  positivity

lemma log_radius_bound {C : ℝ} (hC : 1 ≤ C) :
    Real.log (1 + 8 * C) ≤ 11 * C ^ ((1 : ℝ) / 3) := by
  have hCp : 0 < C := by linarith
  have hs := Real.one_le_rpow hC (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  have hl := Real.log_le_log (show 0 < 1 + 8 * C by positivity)
    (show 1 + 8 * C ≤ 9 * C by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt hCp)] at hl
  have h9 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num)
  have hc := Real.log_le_rpow_div hCp.le (show (0 : ℝ) < 1 / 3 by norm_num)
  norm_num at h9
  nlinarith

lemma log_accuracy_bound {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C) :
    Real.log (1 + 8 * A) ≤ Real.log (1 + 8 * C) + A / C := by
  have harg : 1 + 8 * A ≤ (1 + 8 * C) * (1 + A / C) := by
    field_simp
    nlinarith
  have hl := Real.log_le_log (show 0 < 1 + 8 * A by positivity) harg
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + A / C by positivity)
  linarith

lemma log_finish_bound {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) :
    Real.log (1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3)))) ≤
      A / C + 24 * C ^ ((1 : ℝ) / 3) := by
  have hCp : 0 < C := by linarith
  have hs : 0 ≤ C ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hCp.le _
  have he : 1 ≤ Real.exp (2 * C ^ ((1 : ℝ) / 3)) := Real.one_le_exp (by positivity)
  have harg : 1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))) ≤
      ((1 + 8 * A) * (1 + 8 * C)) * Real.exp (2 * C ^ ((1 : ℝ) / 3)) := by
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + 8 * A by positivity)
    have hn : 0 ≤ C * Real.exp (2 * C ^ ((1 : ℝ) / 3)) := by positivity
    nlinarith
  have hl := Real.log_le_log (by positivity) harg
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp] at hl
  have ha := log_accuracy_bound hA hCp
  have hc := log_radius_bound hC
  linarith

lemma finishScalar_bound {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    finishScalar A C ≤ 18115 * A + 1000 * C ^ ((4 : ℝ) / 3) := by
  have hD : 0 ≤ C ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hC _
  by_cases hC1 : 1 ≤ C
  · have hCp : 0 < C := by linarith
    have hl := log_finish_bound hA hC1
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 27 * C + 4 by positivity)
    have hc : 27 * C + 4 ≤ 31 * C := by linarith
    have hn := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ A / C + 24 * C ^ ((1 : ℝ) / 3) by positivity)
    have he : C * C ^ ((1 : ℝ) / 3) = C ^ ((4 : ℝ) / 3) := by
      have hh := Real.rpow_add hCp 1 ((1 : ℝ) / 3)
      norm_num at hh
      exact hh.symm
    have hd : C * (A / C) = A := mul_div_cancel₀ A (ne_of_gt hCp)
    unfold finishScalar
    nlinarith
  · have hCs : C ≤ 1 := le_of_lt (lt_of_not_ge hC1)
    have hs := Real.rpow_le_one hC hCs (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have he2 : Real.exp 2 ≤ 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have he : Real.exp (2 * C ^ ((1 : ℝ) / 3)) ≤ 9 :=
      (Real.exp_le_exp.mpr (by linarith)).trans he2
    have hm := mul_le_mul hCs he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
    have harg : 1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))) ≤
        1 + 584 * A := by
      have hh := mul_le_mul_of_nonneg_left hm hA
      nlinarith
    have hl := Real.log_le_sub_one_of_pos
      (show 0 < 1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))) by positivity)
    have hl0 : 0 ≤ Real.log (1 + 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3)))) :=
      Real.log_nonneg (by
      have hh : 0 ≤ 8 * A * (1 + 8 * C * Real.exp (2 * C ^ ((1 : ℝ) / 3))) := by positivity
      linarith)
    have hc : 27 * C + 4 ≤ 31 := by linarith
    have hh := mul_le_mul_of_nonneg_right hc hl0
    unfold finishScalar
    nlinarith

lemma warm_count_bound {L1 R : ℝ} (hC : 0 ≤ L1 * R) :
    (warmLimit L1 R : ℝ) ≤ 4 * (L1 * R) ^ ((4 : ℝ) / 3) + 2 := by
  unfold warmLimit
  split_ifs
  · have hh := Nat.ceil_lt_add_one
      (show 0 ≤ 4 * (L1 * R) ^ ((4 : ℝ) / 3) by positivity)
    push_cast
    linarith
  · simp only [Nat.cast_zero]
    positivity

lemma total_blocks {A L1 R : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ L1 * R) :
    warmLimit L1 R + ⌈finishScalar A (L1 * R)⌉₊ + 1 ≤
      ⌈(2 : ℝ) ^ 15 * (1 + A + (L1 * R) ^ ((4 : ℝ) / 3))⌉₊ := by
  have hw := warm_count_bound hC
  have hf := Nat.ceil_lt_add_one (finishScalar_nonneg hA hC)
  have hb := finishScalar_bound hA hC
  have hn := Nat.le_ceil ((2 : ℝ) ^ 15 * (1 + A + (L1 * R) ^ ((4 : ℝ) / 3)))
  have hD : 0 ≤ (L1 * R) ^ ((4 : ℝ) / 3) := Real.rpow_nonneg hC _
  have hh : ((warmLimit L1 R + ⌈finishScalar A (L1 * R)⌉₊ + 1 : ℕ) : ℝ) ≤
      (⌈(2 : ℝ) ^ 15 * (1 + A + (L1 * R) ^ ((4 : ℝ) / 3))⌉₊ : ℝ) := by
    push_cast
    norm_num at hn
    nlinarith
  exact_mod_cast hh

lemma finishScalar_eq (L0 L1 R ε : ℝ) :
    finishScalar (L0 * R / ε) (L1 * R) =
      11 * L0 * R / ε + (27 * L1 * R + 4) *
        Real.log (1 + 8 * (L0 + L1 * warmThreshold L0 L1 R) * R / ε) := by
  have he : 1 + 8 * (L0 * R / ε) *
      (1 + 8 * (L1 * R) * Real.exp (2 * (L1 * R) ^ ((1 : ℝ) / 3))) =
      1 + 8 * (L0 + L1 * warmThreshold L0 L1 R) * R / ε := by
    unfold warmThreshold warmScale
    ring
  unfold finishScalar
  rw [he]
  ring

end OracleTemplate.WarmAnchoredMonotone
