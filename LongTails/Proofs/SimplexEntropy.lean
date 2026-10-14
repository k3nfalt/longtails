import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OracleTemplate.SimplexEntropy

lemma scalar_hellinger {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤
      x * Real.log x - x * Real.log y - x + y := by
  by_cases hz : x = 0
  · subst x
    simp [Real.sq_sqrt hy.le]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hsx := Real.sqrt_pos.mpr hxp
  have hsy := Real.sqrt_pos.mpr hy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy.le,
    Real.log_sqrt hx] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * x)
  have he : 2 * x * (Real.sqrt y / Real.sqrt x - 1) =
      2 * Real.sqrt x * Real.sqrt y - 2 * x := by
    have hsq := Real.sq_sqrt hx
    field_simp
    nlinarith
  rw [he] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy.le]

lemma sum_hellinger {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (hsx : ∑ i, x i = 1) (hsy : ∑ i, y i = 1) :
    ∑ i, (Real.sqrt (x i) - Real.sqrt (y i)) ^ 2 ≤
      ∑ i, (x i * Real.log (x i) - x i * Real.log (y i)) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => scalar_hellinger (hx i) (hy i))
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsx, hsy,
    sub_add_cancel] using h

lemma oneNorm_sq_le_hellinger {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hsx : ∑ i, x i = 1) (hsy : ∑ i, y i = 1) :
    (∑ i, |x i - y i|) ^ 2 ≤
      4 * ∑ i, (Real.sqrt (x i) - Real.sqrt (y i)) ^ 2 := by
  have hpoint (i : ι) : |x i - y i| ^ 2 ≤
      (Real.sqrt (x i) - Real.sqrt (y i)) ^ 2 * (2 * (x i + y i)) := by
    rw [sq_abs]
    have he : (x i - y i) ^ 2 =
        (Real.sqrt (x i) - Real.sqrt (y i)) ^ 2 *
          (Real.sqrt (x i) + Real.sqrt (y i)) ^ 2 := by
      nlinarith [Real.sq_sqrt (hx i), Real.sq_sqrt (hy i)]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [Real.sq_sqrt (hx i), Real.sq_sqrt (hy i),
      sq_nonneg (Real.sqrt (x i) - Real.sqrt (y i))]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => sq_nonneg (Real.sqrt (x i) - Real.sqrt (y i)))
    (fun i _ => mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (hx i) (hy i)))
    (fun i _ => hpoint i)
  have hg : (∑ i, 2 * (x i + y i)) = 4 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hsx, hsy]
    norm_num
  rw [hg] at h
  simpa only [mul_comm] using h

lemma relative_entropy_lower {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (hsx : ∑ i, x i = 1) (hsy : ∑ i, y i = 1) :
    (∑ i, |x i - y i|) ^ 2 / 4 ≤
      ∑ i, (x i * Real.log (x i) - x i * Real.log (y i)) := by
  have h1 := oneNorm_sq_le_hellinger hx (fun i => (hy i).le) hsx hsy
  have h2 := sum_hellinger hx hy hsx hsy
  linarith

lemma regularized_linear_lower {ι : Type*} [Fintype ι] {x y s : ι → ℝ}
    {B c : ℝ} (hB : 0 ≤ B) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (hsx : ∑ i, x i = 1) (hsy : ∑ i, y i = 1)
    (hlog : ∀ i, B * Real.log (y i) + s i = c) :
    B / 4 * (∑ i, |x i - y i|) ^ 2 ≤
      (∑ i, (s i * x i + B * (x i * Real.log (x i)))) -
        (∑ i : ι, (s i * y i + B * (y i * Real.log (y i)))) := by
  have h := mul_le_mul_of_nonneg_left (relative_entropy_lower hx hy hsx hsy) hB
  have he (i : ι) :
      s i * x i + B * (x i * Real.log (x i)) -
        (s i * y i + B * (y i * Real.log (y i))) =
      B * (x i * Real.log (x i) - x i * Real.log (y i)) + c * (x i - y i) := by
    rw [← hlog i]
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  have hsum : (∑ i, (x i - y i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsx, hsy, sub_self]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  nlinarith

end OracleTemplate.SimplexEntropy
