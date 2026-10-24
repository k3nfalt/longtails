import LongTails.Setups.CyclicFullWidthPerceptron
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronInstances

open LongTails.Setups.CyclicFullWidthPerceptron

noncomputable def axis {m : ℕ} (j : Fin (m + 1)) : Features (m + 1) :=
  EuclideanSpace.single j 1

noncomputable def residual {m : ℕ} (κ t : ℝ) (j : Fin m) : Features (m + 1) :=
  κ • axis 0 + (t * Real.sqrt (1 - κ ^ 2)) • axis j.succ

lemma axis_norm {m : ℕ} (j : Fin (m + 1)) : ‖axis j‖ = 1 := by simp [axis]

lemma axis_orthogonal {m : ℕ} (j : Fin m) : ⟪axis 0, axis j.succ⟫ = 0 := by
  simp [axis, EuclideanSpace.inner_single_left]

lemma residual_margin {m : ℕ} (κ t : ℝ) (j : Fin m) : ⟪axis 0, residual κ t j⟫ = κ := by
  simp [residual, inner_add_right, inner_smul_right, axis_orthogonal,
    axis_norm]

lemma residual_norm {m : ℕ} (κ t : ℝ) (j : Fin m) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (ht : t ^ 2 = 1) : ‖residual κ t j‖ = 1 := by
  have hκ₂ : 0 ≤ 1 - κ ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hκ₂
  have hn := norm_add_sq_real (κ • axis (0 : Fin (m + 1)))
    ((t * Real.sqrt (1 - κ ^ 2)) • axis j.succ)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, axis_norm, mul_one,
    real_inner_smul_left, real_inner_smul_right, axis_orthogonal, mul_zero, add_zero] at hn
  have he : ‖residual κ t j‖ ^ 2 = 1 := by
    change ‖κ • axis (0 : Fin (m + 1)) + (t * Real.sqrt (1 - κ ^ 2)) • axis j.succ‖ ^ 2 = _
    nlinarith
  nlinarith [norm_nonneg (residual κ t j)]

lemma opposite_inner {m : ℕ} (κ : ℝ) (j : Fin m) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    ⟪residual κ 1 j, residual κ (-1) j⟫ = 2 * κ ^ 2 - 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - κ ^ 2 by nlinarith)
  have ho : ⟪axis j.succ, axis (0 : Fin (m + 1))⟫ = 0 := by
    rw [real_inner_comm]; exact axis_orthogonal j
  simp only [residual, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, axis_orthogonal, ho, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, axis_norm, mul_pow, sq_abs]
  nlinarith

noncomputable def cloudParams (m : ℕ) (κ μ ν : ℝ) : Params := ⟨m + 1, m + m, κ, μ, ν⟩

noncomputable def cloudData (m : ℕ) (κ μ ν : ℝ) :
    Data (cloudParams m κ μ ν).dimension (cloudParams m κ μ ν).count where
  residual := Fin.addCases (residual κ 1) (residual κ (-1))
  offset i := ν * (i.val + 1) / (m + m + 1)

lemma cloud_geometry (m : ℕ) (κ μ ν : ℝ) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hν : 0 ≤ ν) :
    Geometry (cloudParams m κ μ ν) (cloudData m κ μ ν) := by
  dsimp only [Geometry, cloudParams, cloudData]
  refine ⟨?_, ?_, axis 0, axis_norm _, ?_⟩
  · intro i
    have hd : 0 < (m : ℝ) + m + 1 := by positivity
    have hi : (i.val : ℝ) + 1 ≤ (m : ℝ) + m + 1 := by
      have hi : i.val + 1 ≤ m + m + 1 := by have hh := i.isLt; change i.val < m + m at hh; omega
      exact_mod_cast hi
    constructor
    · positivity
    · apply (div_le_iff₀ hd).mpr
      exact mul_le_mul_of_nonneg_left hi hν
  · intro i
    change ‖(Fin.addCases (residual κ 1) (residual κ (-1)) i : Features (m + 1))‖ ≤ 1
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using (residual_norm κ 1 j hκ hκ₁ (by norm_num)).le
    · intro j
      simpa only [Fin.addCases_right] using (residual_norm κ (-1) j hκ hκ₁ (by norm_num)).le
  · intro i
    change κ ≤ ⟪axis 0, Fin.addCases (residual κ 1) (residual κ (-1)) i⟫
    refine Fin.addCases ?_ ?_ i
    · intro j; simp only [Fin.addCases_left, residual_margin, le_refl]
    · intro j; simp only [Fin.addCases_right, residual_margin, le_refl]

lemma residual_pair_sum {m : ℕ} (κ : ℝ) (j : Fin m) :
    residual κ 1 j + residual κ (-1) j = (2 * κ) • axis 0 := by
  unfold residual
  module

lemma residual_pair_difference {m : ℕ} (κ : ℝ) (j : Fin m) :
    residual κ 1 j - residual κ (-1) j = (2 * Real.sqrt (1 - κ ^ 2)) • axis j.succ := by
  unfold residual
  module

lemma residual_margin_upper {m : ℕ} (κ γ : ℝ) (j : Fin m) (z : Features (m + 1))
    (hκ : 0 ≤ κ) (hz : ‖z‖ ≤ 1)
    (hplus : γ ≤ ⟪z, residual κ 1 j⟫) (hminus : γ ≤ ⟪z, residual κ (-1) j⟫) : γ ≤ κ := by
  have hsum : ⟪z, residual κ 1 j⟫ + ⟪z, residual κ (-1) j⟫ = 2 * κ * ⟪z, axis 0⟫ := by
    rw [← inner_add_right, residual_pair_sum, inner_smul_right]
  have hi : ⟪z, axis 0⟫ ≤ 1 := by
    have hh := real_inner_le_norm z (axis (0 : Fin (m + 1)))
    rw [axis_norm, mul_one] at hh
    exact hh.trans hz
  have hm := mul_le_mul_of_nonneg_left hi hκ
  nlinarith

lemma cloud_offsets_positive (m : ℕ) (κ μ ν : ℝ) (hν : 0 < ν) (i : Fin (m + m)) :
    0 < (cloudData m κ μ ν).offset i := by
  change 0 < ν * ((i.val : ℝ) + 1) / ((m : ℝ) + m + 1)
  positivity

end LongTails.Proofs.CyclicPerceptronInstances
