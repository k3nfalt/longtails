import LongTails.Proofs.DiagonalCut

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

lemma metric_agd_step {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hconv : ∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y)
    {P : Fin d → ℝ} (hP : ∀ i, 0 < P i) {θ A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hθa : a ^ 2 ≤ θ * (A + a))
    {x z u y xp zp : EuclideanSpace ℝ (Fin d)}
    (hy : ∀ i, (A + a) * y i = A * x i + a * z i)
    (hzp : ∀ i, zp i = z i - a * (P i * gradient f y i))
    (harm : f xp ≤ f y - θ * (∑ i, P i * gradient f y i ^ 2) / 2) :
    (A + a) * (f xp - f u) + (∑ i, (zp i - u i) ^ 2 / P i) / 2 ≤
      A * (f x - f u) + (∑ i, (z i - u i) ^ 2 / P i) / 2 := by
  set g := gradient f y
  have h1 := hconv y x
  have h2 := hconv y u
  rw [inner_eq_sum] at h1 h2
  simp only [PiLp.sub_apply] at h1 h2
  set Q := ∑ i, P i * g i ^ 2
  set S1 := ∑ i, g i * (x i - y i)
  set S2 := ∑ i, g i * (u i - y i)
  set S3 := ∑ i, g i * (z i - u i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => mul_nonneg (hP i).le (sq_nonneg _)
  have hid : A * S1 + a * S2 = -(a * S3) := by
    simp only [S1, S2, S3, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hy i
    linear_combination (-(g i)) * this
  have hexp : ∑ i, (zp i - u i) ^ 2 / P i =
      ∑ i, (z i - u i) ^ 2 / P i - 2 * a * S3 + a ^ 2 * Q := by
    simp only [S3, Q, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hzp i]
    have := (hP i).ne'
    field_simp
    ring
  have hfin : a ^ 2 * Q ≤ θ * (A + a) * Q := mul_le_mul_of_nonneg_right hθa hQ
  rw [hexp]
  nlinarith [h1, h2, hid, harm, hfin, mul_le_mul_of_nonneg_left h1 hA,
    mul_le_mul_of_nonneg_left h2 ha.le]

lemma secant_bounds {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ : ℝ}
    (hsmooth : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (∑ i, w i * (y i - x i) ^ 2) / 2)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ * (∑ i, w i * (y i - x i) ^ 2) / 2 ≤ f y)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    μ * w i ≤ gradient f (x + EuclideanSpace.single i 1) i - gradient f x i ∧
      gradient f (x + EuclideanSpace.single i 1) i - gradient f x i ≤ w i := by
  classical
  set y := x + EuclideanSpace.single i 1
  have hyx : ∀ j, y j - x j = if j = i then 1 else 0 := by
    intro j; by_cases h : j = i <;> simp [y, h]
  have hxy : ∀ j, x j - y j = -(if j = i then 1 else 0) := by
    intro j; rw [← hyx j]; ring
  have hsum : ∑ j, w j * (y j - x j) ^ 2 = w i := by
    simp only [hyx]; simp
  have hsum' : ∑ j, w j * (x j - y j) ^ 2 = w i := by
    simp only [hxy]; simp
  have hin1 : ⟪gradient f x, y - x⟫ = gradient f x i := by
    rw [inner_eq_sum]; simp only [PiLp.sub_apply, hyx]; simp
  have hin2 : ⟪gradient f y, x - y⟫ = -gradient f y i := by
    rw [inner_eq_sum]; simp only [PiLp.sub_apply, hxy]; simp
  have a1 := hsmooth x y
  have a2 := hsmooth y x
  have b1 := hsc x y
  have b2 := hsc y x
  rw [hin1, hsum] at a1 b1
  rw [hin2, hsum'] at a2 b2
  constructor <;> linarith

end OracleTemplate.OnlineMetricAccelerated
