import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.SparseTensorBounds

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma sum_product_bound (a b : ι → ℝ) {U V κ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hκ : 0 ≤ κ)
    (ha : ∑ i, (a i) ^ 2 ≤ κ * U ^ 2)
    (hb : ∑ i, (b i) ^ 2 ≤ κ * V ^ 2) :
    ∑ i, a i * b i ≤ κ * U * V := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hab := mul_le_mul ha hb (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))
    (mul_nonneg hκ (sq_nonneg U))
  have ht : 0 ≤ κ * U * V := by positivity
  nlinarith

lemma sum_tensor_bound (T : ι → E →L[ℝ] E →L[ℝ] E)
    (energy : ι → E → ℝ) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (he : ∀ u, ∑ i, (energy i u) ^ 2 ≤ κ * ‖u‖ ^ 2)
    (hT : ∀ i u v, ‖T i u v‖ ≤ C * energy i u * energy i v) :
    ‖∑ i, T i‖ ≤ C * κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hκ)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  calc
    ‖(∑ i, T i) u v‖ = ‖∑ i, T i u v‖ := by simp
    _ ≤ ∑ i, ‖T i u v‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * energy i u * energy i v := Finset.sum_le_sum (fun i _ => hT i u v)
    _ = C * ∑ i, energy i u * energy i v := by rw [Finset.mul_sum]; congr 1; funext; ring
    _ ≤ C * (κ * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left
      (sum_product_bound (energy · u) (energy · v) (norm_nonneg u) (norm_nonneg v) hκ (he u) (he v)) hC
    _ = _ := by ring

lemma pair_energy (n : ℕ) (a : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, ((a i.castSucc) ^ 2 + (a i.succ) ^ 2) ≤
      2 * ∑ i : Fin (n + 1), (a i) ^ 2 := by
  rw [Finset.sum_add_distrib]
  have h₁ : ∑ i : Fin n, (a i.castSucc) ^ 2 ≤ ∑ i : Fin (n + 1), (a i) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h₂ : ∑ i : Fin n, (a i.succ) ^ 2 ≤ ∑ i : Fin (n + 1), (a i) ^ 2 := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  linarith

end LongTails.Proofs.SparseTensorBounds
