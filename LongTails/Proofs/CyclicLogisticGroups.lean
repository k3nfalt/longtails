import LongTails.Proofs.BilinearLogisticDescent
import Mathlib.Analysis.InnerProductSpace.ProdL2

open scoped RealInnerProductSpace
open LongTails.Proofs.BilinearLogisticDescent (loss)

namespace LongTails.Proofs.CyclicLogisticGroups

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Group (E : Type*) := WithLp 2 (ℝ × E)
abbrev Point (E : Type*) := WithLp 2 (Group E × Group E)

noncomputable def value (z : E) (s : Group E) : ℝ := s.fst * ⟪z, s.snd⟫

noncomputable def grad (z : E) (s : Group E) : Group E :=
  WithLp.toLp 2 (⟪z, s.snd⟫, s.fst • z)

noncomputable def imbalance (s : Group E) : ℝ := s.fst ^ 2 - ‖s.snd‖ ^ 2

noncomputable def margin (z r : E) (s : Point E) : ℝ := value z s.fst + value r s.snd

noncomputable def marginGrad (z r : E) (s : Point E) : Point E :=
  WithLp.toLp 2 (grad z s.fst, grad r s.snd)

omit [InnerProductSpace ℝ E] in
lemma group_norm (s : Group E) : ‖s‖ ^ 2 = s.fst ^ 2 + ‖s.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

lemma group_inner (s d : Group E) : ⟪s, d⟫ = s.fst * d.fst + ⟪s.snd, d.snd⟫ := by
  change d.fst * s.fst + _ = s.fst * d.fst + _
  rw [mul_comm d.fst s.fst]

lemma grad_inner (s v : Group E) (z : E) :
    ⟪grad z s, v⟫ = v.fst * ⟪z, s.snd⟫ + s.fst * ⟪z, v.snd⟫ := by
  rw [group_inner]; change ⟪z, s.snd⟫ * v.fst + ⟪s.fst • z, v.snd⟫ = _
  rw [real_inner_smul_left]; ring

lemma margin_euler (s : Point E) (z r : E) : ⟪marginGrad z r s, s⟫ = 2 * margin z r s := by
  change ⟪grad z s.fst, s.fst⟫ + ⟪grad r s.snd, s.snd⟫ = _
  simp only [grad_inner, margin, value]; ring

lemma value_increment (s v : Group E) (z : E) (η : ℝ) :
    value z (s + η • v) = value z s + η * ⟪grad z s, v⟫ + η ^ 2 * value z v := by
  rw [grad_inner]
  simp only [value, WithLp.add_fst, WithLp.smul_fst, smul_eq_mul, WithLp.add_snd,
    WithLp.smul_snd, inner_add_right, real_inner_smul_right]; ring

lemma margin_increment (s v : Point E) (z r : E) (η : ℝ) :
    margin z r (s + η • v) = margin z r s + (η * ⟪marginGrad z r s, v⟫ + η ^ 2 * margin z r v) := by
  change _ = margin z r s + (η * (⟪grad z s.fst, v.fst⟫ + ⟪grad r s.snd, v.snd⟫) + _)
  simp only [margin, WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd,
    value_increment]; ring

lemma grad_norm (s : Group E) (z : E) : ‖grad z s‖ ^ 2 ≤ ‖z‖ ^ 2 * ‖s‖ ^ 2 := by
  rw [group_norm, group_norm]
  change ⟪z, s.snd⟫ ^ 2 + ‖s.fst • z‖ ^ 2 ≤ _
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm z s.snd) 2
  rw [sq_abs, mul_pow] at h
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  linarith

lemma value_bound (s : Group E) {z : E} (hz : ‖z‖ ≤ 1) : |value z s| ≤ ‖s‖ ^ 2 / 2 := by
  have h := (abs_real_inner_le_norm z s.snd).trans
    (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
  simp only [one_mul] at h
  rw [value, abs_mul, group_norm]
  nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg s.fst),
    sq_nonneg (|s.fst| - ‖s.snd‖), sq_abs s.fst]

lemma margin_bound (s : Point E) {z r : E} (hz : ‖z‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    |margin z r s| ≤ ‖s‖ ^ 2 / 2 := by
  rw [margin, WithLp.prod_norm_sq_eq_of_L2]
  linarith [abs_add_le (value z s.fst) (value r s.snd), value_bound s.fst hz,
    value_bound s.snd hr]

lemma group_energy_from_product (s : Group E) :
    ‖s‖ ^ 2 ≤ |imbalance s| + 2 * ‖s.fst • s.snd‖ := by
  rw [group_norm, imbalance, norm_smul, Real.norm_eq_abs]
  by_cases h : |s.fst| ≤ ‖s.snd‖
  · nlinarith [neg_le_abs (s.fst ^ 2 - ‖s.snd‖ ^ 2), sq_abs s.fst,
      mul_le_mul_of_nonneg_left h (abs_nonneg s.fst)]
  · nlinarith [le_abs_self (s.fst ^ 2 - ‖s.snd‖ ^ 2),
      mul_le_mul_of_nonneg_right (le_of_not_ge h) (norm_nonneg s.snd)]

lemma imbalance_step (s d : Group E) (η : ℝ)
    (h : s.fst * d.fst = ⟪s.snd, d.snd⟫) :
    imbalance (s + η • d) = imbalance s + η ^ 2 * imbalance d := by
  simp only [imbalance, WithLp.add_fst, WithLp.smul_fst, smul_eq_mul, WithLp.add_snd,
    WithLp.smul_snd, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [← h]; ring

omit [InnerProductSpace ℝ E] in
lemma abs_imbalance_le (s : Group E) : |imbalance s| ≤ ‖s‖ ^ 2 := by
  rw [imbalance, group_norm, abs_le]
  constructor <;> linarith [sq_nonneg s.fst, sq_nonneg ‖s.snd‖]

end LongTails.Proofs.CyclicLogisticGroups
