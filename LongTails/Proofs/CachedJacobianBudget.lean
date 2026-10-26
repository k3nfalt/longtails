import LongTails.Proofs.CachedJacobianCounts
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CachedJacobianBudget

open LongTails.Setups.LipschitzJacobianMonotone
open LongTails.Algorithms.CachedJacobian CachedJacobianTuning

lemma outerCount_upper (p : Params) :
    (outerCount p : ℝ) ≤ 1024 * Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε) + 2 := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 1024 * Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε) by positivity)
  unfold outerCount
  push_cast
  linarith

lemma outer_log_bound {p : Params} (hv : spec.valid p) :
    Real.log ((outerCount p : ℝ) + 1) ≤ 11 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε) := by
  have hL := hv.1
  have hε := hv.2.2.1
  let A := (p.m : ℝ) * p.L * p.D ^ 2 / p.ε
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs := Real.sq_sqrt hA
  have hsn := Real.sqrt_nonneg A
  have hsup : Real.sqrt A ≤ 1 + A := by nlinarith [sq_nonneg (Real.sqrt A - 1)]
  have hT := outerCount_upper p
  have hbound : (outerCount p : ℝ) + 1 ≤ 2048 * (2 + A) := by
    change (outerCount p : ℝ) ≤ 1024 * Real.sqrt A + 2 at hT
    linarith
  have hh := Real.log_le_log (show 0 < (outerCount p : ℝ) + 1 by positivity) hbound
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  have hlog : Real.log (2048 : ℝ) ≤ 11 := by
    have heq : (2048 : ℝ) = 2 ^ 11 := by norm_num
    rw [heq, Real.log_pow]
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb ⊢
    linarith
  dsimp only [A] at hh
  linarith

lemma nat_log_bound {n : ℕ} (hn : 0 < n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have hp := Nat.pow_log_le_self 2 hn.ne'
  have hreal : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast hp
  have hh := Real.log_le_log (show 0 < (2 : ℝ) ^ Nat.log 2 n by positivity) hreal
  rw [Real.log_pow] at hh
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.log_div, Real.log_one] at h <;> norm_num at *
    linarith
  have hmul := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (Nat.log 2 n : ℝ) by positivity)
  linarith

lemma innerCount_upper {p : Params} (hv : spec.valid p) :
    (innerCount p : ℝ) ≤ 48 * (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε)) := by
  have hL := hv.1
  have hε := hv.2.2.1
  have hh := nat_log_bound (show 0 < outerCount p + 1 by omega)
  have hl := outer_log_bound hv
  have hn : 0 ≤ Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε) := by
    apply Real.log_nonneg
    have hp : 0 ≤ (p.m : ℝ) * p.L * p.D ^ 2 / p.ε := by positivity
    linarith
  unfold innerCount
  push_cast at *
  linarith

lemma total_length_bound {p : Params} (hv : spec.valid p) :
    ((2 * innerCount p) * outerCount p + 2 : ℕ) ≤
      (100000 : ℝ) * (1 + Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε)) *
        (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε)) := by
  have hL := hv.1
  have hε := hv.2.2.1
  have hA : 0 ≤ (p.m : ℝ) * p.L * p.D ^ 2 / p.ε := by positivity
  have hlog : 0 ≤ Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε) :=
    Real.log_nonneg (by linarith)
  have hs := Real.sqrt_nonneg (p.m * p.L * p.D ^ 2 / p.ε)
  have hT := outerCount_upper p
  have hl := innerCount_upper hv
  have hTp : 0 ≤ (outerCount p : ℝ) := by positivity
  have hlp : 0 ≤ (innerCount p : ℝ) := by positivity
  have hmul := mul_le_mul hl hT hTp (show 0 ≤
    48 * (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε)) by positivity)
  push_cast
  nlinarith [mul_nonneg hs hlog]

lemma cache_factor_bound {p : Params} (hv : spec.valid p) :
    3200 * p.L * p.D * stepSize p (outerCount p - 1) ≤
      1028 * (1 + Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε))) := by
  have hL := hv.1
  have hD := hv.2.1
  have hε := hv.2.2.1
  have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast hv.2.2.2.1
  have hmp : (0 : ℝ) < p.m := by linarith
  have hT := outerCount_upper p
  have hindex : ((outerCount p - 1 : ℕ) : ℝ) + 1 = outerCount p := by
    exact_mod_cast (Nat.sub_add_cancel (outerCount_pos p))
  have heq : 3200 * p.L * p.D * stepSize p (outerCount p - 1) =
      25 * ((outerCount p : ℝ) + 2) / (384 * p.m) := by
    unfold stepSize initialStep
    rw [show ((outerCount p - 1 : ℕ) : ℝ) + 3 = outerCount p + 2 by linarith]
    field_simp
    ring
  have hsqrt : Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε) =
      p.m * Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε)) := by
    have hh : (p.m : ℝ) * p.L * p.D ^ 2 / p.ε =
        (p.m : ℝ) ^ 2 * (p.L * p.D ^ 2 / (p.m * p.ε)) := by field_simp
    rw [hh, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [heq]
  rw [hsqrt] at hT
  apply (div_le_iff₀ (show 0 < (384 : ℝ) * p.m by positivity)).mpr
  have hs := Real.sqrt_nonneg (p.L * p.D ^ 2 / (p.m * p.ε))
  nlinarith [mul_nonneg (show 0 ≤ (p.m : ℝ) - 1 by linarith) hs]

lemma jacobian_budget_bound {p : Params} (hv : spec.valid p) :
    1 + 3200 * p.L * p.D * stepSize p (outerCount p - 1) * (1 + Real.log (outerCount p)) ≤
      20000 * (1 + Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε))) *
        (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε)) := by
  have hL := hv.1
  have hε := hv.2.2.1
  have hA : 0 ≤ (p.m : ℝ) * p.L * p.D ^ 2 / p.ε := by positivity
  have hlog : 0 ≤ Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε) :=
    Real.log_nonneg (by linarith)
  have hT : (1 : ℝ) ≤ outerCount p := by exact_mod_cast outerCount_pos p
  have hlogT : 0 ≤ Real.log (outerCount p) := Real.log_nonneg hT
  have hl := outer_log_bound hv
  have hl' := Real.log_le_log (by linarith : (0 : ℝ) < outerCount p)
    (show (outerCount p : ℝ) ≤ outerCount p + 1 by linarith)
  have hf := cache_factor_bound hv
  have hs := Real.sqrt_nonneg (p.L * p.D ^ 2 / (p.m * p.ε))
  have hmul := mul_le_mul hf (show 1 + Real.log (outerCount p) ≤
    12 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε) by linarith)
    (by linarith : 0 ≤ 1 + Real.log (outerCount p))
    (show 0 ≤ 1028 * (1 + Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε))) by positivity)
  nlinarith [mul_nonneg hs hlog]

lemma counts_sufficient {p : Params} {F : p.E → p.E} (hv : spec.valid p)
    (hF : ∀ x ∈ p.X, DifferentiableAt ℝ F x)
    (hmono : ∀ x ∈ p.X, ∀ z ∈ p.X, 0 ≤ ⟪F x - F z, x - z⟫)
    (hJ : ∀ x ∈ p.X, ∀ z ∈ p.X,
      ‖fderiv ℝ F x - fderiv ℝ F z‖ ≤ p.L * ‖x - z‖) (i : Fin 2) :
    EnergyHessianExecution.counts (CachedJacobianExecution.replies p F) (plan p) i ≤
      if i = 0 then
        ⌈100000 * (1 + Real.sqrt (p.m * p.L * p.D ^ 2 / p.ε)) *
          (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε))⌉₊
      else
        ⌈20000 * (1 + Real.sqrt (p.L * p.D ^ 2 / (p.m * p.ε))) *
          (1 + Real.log (2 + p.m * p.L * p.D ^ 2 / p.ε))⌉₊ := by
  have hs := EnergyHessianExecution.counts_sum (CachedJacobianExecution.replies p F) (plan p)
  fin_cases i
  · have hcount : EnergyHessianExecution.counts (CachedJacobianExecution.replies p F) (plan p) 0 ≤
        (2 * innerCount p) * outerCount p + 2 := by
      exact (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)).trans_eq hs
    apply hcount.trans
    exact_mod_cast (total_length_bound hv).trans (Nat.le_ceil _)
  · exact_mod_cast ((CachedJacobianCounts.jacobian_count_bound hv hF hmono hJ).trans
      (jacobian_budget_bound hv)).trans (Nat.le_ceil _)

end LongTails.Proofs.CachedJacobianBudget
