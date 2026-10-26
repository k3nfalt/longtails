import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace LongTails.Proofs.AdamMoments

lemma weighted_mean_sq_le {ι : Type*} [Fintype ι] (p q g : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hcard : (Fintype.card ι : ℝ) ≤ t)
    (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, p i ^ 2 ≤ t * q i) :
    (∑ i, p i * g i) ^ 2 ≤ t ^ 2 * ∑ i, q i * g i ^ 2 := by
  have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => p i * g i)
  have hterm : ∑ i, (p i * g i) ^ 2 ≤ t * ∑ i, q i * g i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_right (hpq i) (sq_nonneg (g i))]
  have hv : 0 ≤ ∑ i, q i * g i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg (Fintype.card ι) :
    (0 : ℝ) ≤ Fintype.card ι)
  have h₂ := mul_le_mul_of_nonneg_right hcard (mul_nonneg ht hv)
  simp only [Finset.card_univ] at hsq
  nlinarith

lemma weighted_mean_le_rms {ι : Type*} [Fintype ι] (p q g : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hcard : (Fintype.card ι : ℝ) ≤ t)
    (hq : ∀ i, 0 ≤ q i) (hpq : ∀ i, p i ^ 2 ≤ t * q i) :
    |∑ i, p i * g i| ≤ t * Real.sqrt (∑ i, q i * g i ^ 2) := by
  have hsq := weighted_mean_sq_le p q g t ht hcard hq hpq
  have hv : 0 ≤ ∑ i, q i * g i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (sq_nonneg _)
  have hs := Real.sq_sqrt hv
  have ha := sq_abs (∑ i, p i * g i)
  have hn : 0 ≤ t * Real.sqrt (∑ i, q i * g i ^ 2) := by positivity
  nlinarith [sq_nonneg (|∑ i, p i * g i| - t * Real.sqrt (∑ i, q i * g i ^ 2))]

lemma geometric_sum_bounds {β : ℝ} (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (n : ℕ) :
    1 ≤ ∑ j : Fin (n + 1), β ^ (j : ℕ) ∧
      (∑ j : Fin (n + 1), β ^ (j : ℕ)) ≤ n + 1 := by
  constructor
  · have h := Finset.single_le_sum (f := fun j : Fin (n + 1) => β ^ (j : ℕ))
      (fun j _ => pow_nonneg hβ _) (Finset.mem_univ (0 : Fin (n + 1)))
    simpa using h
  · calc
      ∑ j : Fin (n + 1), β ^ (j : ℕ) ≤ ∑ _j : Fin (n + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_one₀ hβ hβ₁
      _ = n + 1 := by simp

lemma normalized_weight_square {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hβ₁₁ : β₁ ≤ 1) (hβ₂₁ : β₂ ≤ 1) (hβ : β₁ ^ 2 ≤ β₂)
    (n : ℕ) (j : Fin (n + 1)) :
    (β₁ ^ (j : ℕ) / (∑ i : Fin (n + 1), β₁ ^ (i : ℕ))) ^ 2 ≤
      (n + 1) * (β₂ ^ (j : ℕ) / (∑ i : Fin (n + 1), β₂ ^ (i : ℕ))) := by
  obtain ⟨hS₁, _⟩ := geometric_sum_bounds hβ₁ hβ₁₁ n
  obtain ⟨hS₂, hS₂n⟩ := geometric_sum_bounds hβ₂ hβ₂₁ n
  have hS₁p : 0 < ∑ i : Fin (n + 1), β₁ ^ (i : ℕ) := by linarith
  have hS₂p : 0 < ∑ i : Fin (n + 1), β₂ ^ (i : ℕ) := by linarith
  have hp : (β₁ ^ (j : ℕ)) ^ 2 ≤ β₂ ^ (j : ℕ) := by
    calc
      (β₁ ^ (j : ℕ)) ^ 2 = (β₁ ^ 2) ^ (j : ℕ) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ β₂ ^ (j : ℕ) := pow_le_pow_left₀ (sq_nonneg _) hβ _
  have hp₀ : 0 ≤ β₂ ^ (j : ℕ) := pow_nonneg hβ₂ _
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hS₁p) hS₂p]
  have h₁ := mul_le_mul_of_nonneg_right hp hS₂p.le
  have h₂ := mul_le_mul_of_nonneg_left hS₂n hp₀
  have hS₁sq : 1 ≤ (∑ i : Fin (n + 1), β₁ ^ (i : ℕ)) ^ 2 := by nlinarith
  have h₃ := mul_le_mul_of_nonneg_left hS₁sq
    (show 0 ≤ (n + 1 : ℝ) * β₂ ^ (j : ℕ) by positivity)
  nlinarith

lemma weighted_mean_difference {ι : Type*} [Fintype ι] (p x y : ι → ℝ) (h : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hxy : ∀ i, |x i - y i| ≤ h) :
    |(∑ i, p i * x i) - ∑ i, p i * y i| ≤ h := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (p i * x i - p i * y i)| ≤ ∑ i, |p i * x i - p i * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * h := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hp i)]
      exact mul_le_mul_of_nonneg_left (hxy i) (hp i)
    _ = h := by rw [← Finset.sum_mul, hsum, one_mul]

lemma weighted_rms_difference {ι : Type*} [Fintype ι] (p x y : ι → ℝ) (h : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hh : 0 ≤ h)
    (hxy : ∀ i, |x i - y i| ≤ h) :
    |Real.sqrt (∑ i, p i * x i ^ 2) - Real.sqrt (∑ i, p i * y i ^ 2)| ≤ h := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => Real.sqrt (p i) * x i)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => Real.sqrt (p i) * y i)
  have hu : ‖u‖ = Real.sqrt (∑ i, p i * x i ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg u), EuclideanSpace.real_norm_sq_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [u, mul_pow, Real.sq_sqrt (hp i)]
  have hv : ‖v‖ = Real.sqrt (∑ i, p i * y i ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v), EuclideanSpace.real_norm_sq_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [v, mul_pow, Real.sq_sqrt (hp i)]
  have huv : ‖u - v‖ ^ 2 ≤ h ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ = ∑ i, p i * (x i - y i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [u, v, PiLp.sub_apply]
        rw [← mul_sub, mul_pow, Real.sq_sqrt (hp i)]
      _ ≤ ∑ i, p i * h ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hp i)
        nlinarith [hxy i, abs_nonneg (x i - y i), sq_abs (x i - y i)]
      _ = h ^ 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hn : ‖u - v‖ ≤ h := by nlinarith [norm_nonneg (u - v)]
  rw [← hu, ← hv]
  exact (abs_norm_sub_norm_le u v).trans hn

end LongTails.Proofs.AdamMoments
