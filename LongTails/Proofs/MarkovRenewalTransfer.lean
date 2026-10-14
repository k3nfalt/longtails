import LongTails.Proofs.FiniteMarkovOperators
import LongTails.Proofs.OperatorGeneratingSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {B G : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma transferCovariance_smul (M : G →L[ℂ] B) (A : G →L[ℂ] G) (J : B →L[ℂ] G)
    (z : ℂ) (n : ℕ) :
    transferCovariance M (z • A) J n = z ^ n • transferCovariance M A J n := by
  simp only [transferCovariance, smul_pow, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul]

lemma transferCovariance_refresh (M₀ M : G →L[ℂ] B) (D Q : G →L[ℂ] G)
    (J : B →L[ℂ] G) (hQJ : Q.comp J = J) (q α : ℂ) (n : ℕ) :
    transferCovariance M₀ (D * (q • Q + α • J.comp M)) J n =
      q ^ n • transferCovariance M₀ (D * Q) J n +
        ∑ k ∈ Finset.range n, (α * q ^ k) •
          (transferCovariance M₀ (D * Q) J (k + 1) *
            transferCovariance M (D * (q • Q + α • J.comp M)) J (n - 1 - k)) := by
  have hF : D * (q • Q + α • J.comp M) - q • (D * Q) = α • D.comp (J.comp M) := by
    rw [mul_add, mul_smul_comm, mul_smul_comm, add_sub_cancel_left]
    rfl
  have h := transferCovariance_duhamel M₀ M J (D * (q • Q + α • J.comp M))
    (q • (D * Q)) D α hF n
  rw [transferCovariance_smul] at h
  have ht (k : ℕ) : M₀.comp (((q • (D * Q)) ^ k).comp (D.comp J)) =
      q ^ k • transferCovariance M₀ (D * Q) J (k + 1) := by
    rw [smul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      transferCovariance_tail D Q J hQJ]
    rfl
  simp_rw [ht, smul_mul_assoc, smul_smul] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

lemma refresh_last_term (Φ V₀ V : ℕ → B →L[ℂ] B) (q α : ℂ) (hqa : q + α = 1)
    (hV : V 0 = 1)
    (hrec : ∀ n, V₀ n = q ^ n • Φ n + ∑ k ∈ Finset.range n,
      (α * q ^ k) • (Φ (k + 1) * V (n - 1 - k))) (n : ℕ) :
    V₀ (n + 1) = q ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      (α * q ^ k) • (Φ (k + 1) * V (n - k)) := by
  rw [hrec, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, hV, mul_one]
  have he : q ^ (n + 1) + α * q ^ n = q ^ n := by
    rw [pow_succ]
    calc
      _ = q ^ n * (q + α) := by ring
      _ = _ := by rw [hqa, mul_one]
  rw [← add_assoc, add_right_comm, ← add_smul, he]

noncomputable def renewalScaling (α : ℂ) (V : ℕ → B →L[ℂ] B) (n : ℕ) : B →L[ℂ] B :=
  if n = 0 then 1 else α • V n

lemma renewalScaling_zero (α : ℂ) (V : ℕ → B →L[ℂ] B) : renewalScaling α V 0 = 1 := by
  simp [renewalScaling]

lemma renewalScaling_succ (α : ℂ) (V : ℕ → B →L[ℂ] B) (n : ℕ) :
    renewalScaling α V (n + 1) = α • V (n + 1) := by simp [renewalScaling]

lemma renewalScaling_recurrence (Φ V : ℕ → B →L[ℂ] B) (q α : ℂ)
    (hrec : ∀ n, V (n + 1) = q ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      (α * q ^ k) • (Φ (k + 1) * V (n - k))) (n : ℕ) :
    renewalScaling α V (n + 1) = ∑ k ∈ Finset.range (n + 1),
      (α * q ^ k) • (Φ (k + 1) * renewalScaling α V (n - k)) := by
  rw [renewalScaling_succ, hrec, Finset.sum_range_succ]
  simp only [Nat.sub_self, renewalScaling_zero, mul_one, smul_add, smul_smul]
  rw [add_comm, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hnk : n - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
  simp only [renewalScaling, ite_eq_right hnk, mul_smul_comm, smul_smul]
  congr 1
  ring

section Series

variable [CompleteSpace B]

omit [CompleteSpace B] in
lemma summable_norm_operatorSeries (a : ℕ → B →L[ℂ] B) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun k : ℕ => ‖z ^ k • a k‖) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right C).of_nonneg_of_le
    (fun k => norm_nonneg _)
  intro k
  rw [norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_left (ha k) (pow_nonneg (norm_nonneg z) k)

lemma operatorSeries_mul (a b : ℕ → B →L[ℂ] B) {C D : ℝ}
    (ha : ∀ k, ‖a k‖ ≤ C) (hb : ∀ k, ‖b k‖ ≤ D) {z : ℂ} (hz : ‖z‖ < 1) :
    operatorSeries a z * operatorSeries b z =
      operatorSeries (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) z := by
  unfold operatorSeries
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_norm_operatorSeries a ha hz) (summable_norm_operatorSeries b hb hz)]
  apply tsum_congr
  intro n
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, Nat.add_sub_of_le hkn]

lemma operatorSeries_shift (a : ℕ → B →L[ℂ] B) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    operatorSeries a z = a 0 + z • operatorSeries (fun k => a (k + 1)) z := by
  have h := (summable_operatorSeries a ha hz).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, one_smul] at h
  have he : (∑' k : ℕ, z ^ (k + 1) • a (k + 1)) =
      z • operatorSeries (fun k => a (k + 1)) z := by
    rw [operatorSeries, ← tsum_const_smul'']
    apply tsum_congr
    intro k
    rw [smul_smul, pow_succ']
  rw [he] at h
  exact h.symm

lemma operatorSeries_renewal_identity (a u : ℕ → B →L[ℂ] B) {C D : ℝ}
    (ha : ∀ k, ‖a k‖ ≤ C) (hu : ∀ k, ‖u k‖ ≤ D) (hzero : u 0 = 1)
    (hrec : ∀ n, u (n + 1) = ∑ k ∈ Finset.range (n + 1), a k * u (n - k))
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z • operatorSeries a z) * operatorSeries u z = 1 := by
  have h := operatorSeries_shift u hu hz
  rw [hzero] at h
  simp_rw [hrec] at h
  rw [← operatorSeries_mul a u ha hu hz] at h
  rw [sub_mul, one_mul, smul_mul_assoc]
  exact sub_eq_iff_eq_add.mpr h

end Series

end OracleTemplate.MarkovProduct
