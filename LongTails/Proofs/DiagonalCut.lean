import LongTails.Algorithms.OnlineMetricAccelerated

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

@[simp] lemma scale_apply (p : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    scale p v i = p i * v i := rfl

lemma inner_eq_sum (u v : EuclideanSpace ℝ (Fin d)) : ⟪u, v⟫ = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma cutVector_nonneg (g g' : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    0 ≤ cutVector g g' i := le_max_right _ _

lemma cut_valid {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} (hw : ∀ i, 0 < w i)
    (hsmooth : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (∑ i, w i * (y i - x i) ^ 2) / 2)
    (hconv : ∀ x y, f x + ⟪gradient f x, y - x⟫ ≤ f y)
    (y : EuclideanSpace ℝ (Fin d)) (q : Fin d → ℝ) :
    ∑ i, cutVector (gradient f y) (gradient f (y - scale q (gradient f y))) i / w i ≤
      cutLevel q (f y) (f (y - scale q (gradient f y))) (gradient f y)
        (gradient f (y - scale q (gradient f y))) := by
  set g := gradient f y
  set xp := y - scale q g
  set g' := gradient f xp
  classical
  let p : Fin d → ℝ := fun i => if 0 < g i ^ 2 / 2 - g i * g' i then 1 / w i else 0
  let v := y - scale p g
  have h1 := hsmooth y v
  have h2 := hconv xp v
  have hvy : ∀ i, v i - y i = -(p i * g i) := by
    intro i; simp [v]
  have hvx : ∀ i, v i - xp i = (q i - p i) * g i := by
    intro i; simp [v, xp]; ring
  rw [inner_eq_sum] at h1 h2
  simp only [PiLp.sub_apply] at h1 h2
  simp only [hvy, hvx] at h1 h2
  have hq : ∀ i, w i * (-(p i * g i)) ^ 2 = p i * g i ^ 2 := by
    intro i
    by_cases h : 0 < g i ^ 2 / 2 - g i * g' i
    · simp only [p, h, ite_true]
      have := (hw i).ne'
      field_simp
    · simp only [p, h, ite_false]
      ring
  have hterm : ∀ i, cutVector g g' i / w i = p i * (g i ^ 2 / 2 - g i * g' i) := by
    intro i
    by_cases h : 0 < g i ^ 2 / 2 - g i * g' i
    · simp only [cutVector, p, h, ite_true, max_eq_left h.le]
      field_simp
    · simp only [cutVector, p, h, ite_false, zero_mul]
      rw [max_eq_right (not_lt.mp h), zero_div]
  simp only [hq] at h1
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  unfold cutLevel
  have e1 : ∑ i, g i * -(p i * g i) = -∑ i, p i * g i ^ 2 := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, g' i * ((q i - p i) * g i) = ∑ i, q i * g i * g' i - ∑ i, p i * g i * g' i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, p i * (g i ^ 2 / 2 - g i * g' i) =
      (∑ i, p i * g i ^ 2) / 2 - ∑ i, p i * g i * g' i := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3]
  linarith

lemma cut_exceeds {q : Fin d → ℝ} (hq : ∀ i, 0 ≤ q i) {fy fx : ℝ}
    {g g' : EuclideanSpace ℝ (Fin d)} (hfail : fy - (∑ i, q i * g i ^ 2) / 2 < fx) :
    cutLevel q fy fx g g' < ∑ i, cutVector g g' i * q i := by
  unfold cutLevel
  have h : ∑ i, (g i ^ 2 / 2 - g i * g' i) * q i ≤ ∑ i, cutVector g g' i * q i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hq i)
  have e : ∑ i, (g i ^ 2 / 2 - g i * g' i) * q i =
      (∑ i, q i * g i ^ 2) / 2 - ∑ i, q i * g i * g' i := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end OracleTemplate.OnlineMetricAccelerated
