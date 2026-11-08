import LongTails.Proofs.BirchResourceChainSmooth

namespace LongTails.Proofs.BirchResourceChain

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Proofs.BirchResourceChainScalars

lemma supported_full {D : ℕ} (x : Point D) : Supported x D :=
  fun i hi => (Nat.not_le_of_lt i.isLt hi).elim

noncomputable def progress {D : ℕ} (x : Point D) : ℕ := by
  classical
  exact Nat.find (show ∃ k, Supported x k from ⟨D, supported_full x⟩)

lemma progress_spec {D : ℕ} (x : Point D) : Supported x (progress x) := by
  classical
  exact Nat.find_spec (show ∃ k, Supported x k from ⟨D, supported_full x⟩)

lemma progress_le {D : ℕ} (x : Point D) {k : ℕ} (hk : Supported x k) : progress x ≤ k := by
  classical
  exact Nat.find_min' (show ∃ k, Supported x k from ⟨D, supported_full x⟩) hk

noncomputable def maskedCoordinate {D : ℕ} (x : Point D) : Point D :=
  if h : progress x < D then
    EuclideanSpace.single ⟨progress x, h⟩ (gradient objective x ⟨progress x, h⟩)
  else 0

noncomputable def noisyGradient {D : ℕ} (p : ℝ) (x : Point D) (coin : Bool) : Point D :=
  gradient objective x + ((if coin then p⁻¹ else 0) - 1) • maskedCoordinate x

lemma noisy_false_support {D : ℕ} (p : ℝ) (x : Point D) :
    Supported (noisyGradient p x false) (progress x) := by
  intro i hi
  unfold noisyGradient maskedCoordinate
  by_cases hd : progress x < D
  · rw [dite_eq_left hd]
    by_cases he : i.val = progress x
    · have he' : i = (⟨progress x, hd⟩ : Fin D) := Fin.ext he
      subst i
      simp
    · have hg := gradient_support (progress_spec x) i (by omega)
      have hn : i ≠ (⟨progress x, hd⟩ : Fin D) := fun e => he (congrArg Fin.val e)
      simp [hg, hn]
  · exact (hd (lt_of_le_of_lt hi i.isLt)).elim

lemma noisy_support {D : ℕ} (p : ℝ) (x : Point D) (coin : Bool) :
    Supported (noisyGradient p x coin) (progress x + 1) := by
  intro i hi
  have hg := gradient_support (progress_spec x) i hi
  have hd : progress x < D := by have := i.isLt; omega
  have hn : i ≠ (⟨progress x, hd⟩ : Fin D) := fun he => by
    have ht : i.val = progress x := congrArg Fin.val he
    omega
  simp [noisyGradient, maskedCoordinate, hd, hg, hn]

lemma right_bounds {D : ℕ} (x : Point D) (j : ℕ) : -1 ≤ rightSlope x j := by
  have hterm (a b : ℝ) : gate a * payoffSlope b ≤ 1 / 2 := by
    have h := mul_le_mul (gate_range a).2 (payoffSlope_range b).2
      (payoffSlope_range b).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  unfold rightSlope
  linarith only [hterm (-coord x j) (-coord x (j + 1)), hterm (coord x j) (coord x (j + 1))]

lemma masked_bound {D : ℕ} (x : Point D) : ‖maskedCoordinate x‖ ≤ 1 := by
  unfold maskedCoordinate
  split
  next hd =>
    let i : Fin D := ⟨progress x, hd⟩
    have hz : coord x i = 0 := coord_zero (progress_spec x) _ le_rfl
    have hgate : gateSlope 0 = 0 := gateSlope_nonpos le_rfl
    have hl : leftSlope x i = 0 := by simp [leftSlope, hz, hgate]
    rw [PiLp.norm_single, Real.norm_eq_abs, grad_split x i, hl]
    have he : (if i.val < D - 1 then (0 : ℝ) else 0) = 0 := by split <;> rfl
    rw [he, add_zero]
    by_cases hi : i.val = 0
    · simp only [hi, ite_true, lt_irrefl, ite_false, add_zero, abs_neg]
      rw [abs_of_nonneg (payoffSlope_range _).1]
      exact (payoffSlope_range _).2
    · rw [ite_eq_right hi, zero_add, ite_eq_left (Nat.pos_of_ne_zero hi),
        abs_of_nonpos (right_nonpos _ _)]
      linarith [right_bounds x (i.val - 1)]
  next => simp

lemma noisy_mean {D : ℕ} {p : ℝ} (hp : 0 < p) (x : Point D) :
    (1 - p) • noisyGradient p x false + p • noisyGradient p x true =
      gradient objective x := by
  simp only [noisyGradient, Bool.false_eq_true, ite_false, ite_true, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  have ha : (1 - p) + p = 1 := by ring
  have hb : (1 - p) * (0 - 1) + p * (p⁻¹ - 1) = 0 := by
    calc
      _ = p * p⁻¹ - 1 := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp.ne', sub_self]
  rw [ha, hb, one_smul, zero_smul, add_zero]

lemma noisy_variance {D : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) (x : Point D) :
    (1 - p) * ‖noisyGradient p x false - gradient objective x‖ ^ 2 +
      p * ‖noisyGradient p x true - gradient objective x‖ ^ 2 ≤ (1 - p) / p := by
  have he : (1 - p) * (0 - 1 : ℝ) ^ 2 + p * (p⁻¹ - 1) ^ 2 = (1 - p) / p := by
    field_simp
    ring
  unfold noisyGradient
  simp only [Bool.false_eq_true, ite_false, ite_true, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, he]
  apply mul_le_of_le_one_right (div_nonneg (sub_nonneg.mpr hp') hp.le)
  simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 (masked_bound x)

end LongTails.Proofs.BirchResourceChain
