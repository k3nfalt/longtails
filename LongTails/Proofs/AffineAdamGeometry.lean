import LongTails.Setups.AffineHeavyTailedAdam
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineAdamGeometry

open LongTails.Setups.AffineHeavyTailedAdam

lemma sumNorm_nonneg {d : ℕ} (x : Point d) : 0 ≤ sumNorm x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma sumNorm_add {d : ℕ} (x y : Point d) : sumNorm (x + y) ≤ sumNorm x + sumNorm y := by
  simp only [sumNorm, PiLp.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)

lemma sumNorm_le_add_sub {d : ℕ} (x y : Point d) : sumNorm x ≤ sumNorm y + sumNorm (x - y) := by
  have h := sumNorm_add y (x - y)
  rw [show y + (x - y) = x by abel] at h
  exact h

lemma measurable_sumNorm {d : ℕ} : Measurable (sumNorm (d := d)) := by
  unfold sumNorm
  fun_prop

lemma measurable_gradient {d : ℕ} (f : Point d → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma maxNorm_nonneg {d : ℕ} (x : Point d) : 0 ≤ maxNorm x := norm_nonneg _

lemma maxNorm_smul {d : ℕ} (c : ℝ) (x : Point d) :
    maxNorm (c • x) = |c| * maxNorm x := by
  change ‖c • WithLp.ofLp x‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl

lemma coordinate_le_maxNorm {d : ℕ} (x : Point d) (i : Fin d) :
    |x i| ≤ maxNorm x := by
  exact norm_le_pi_norm (WithLp.ofLp x) i

lemma inner_le_dual {d : ℕ} (x y : Point d) :
    ⟪x, y⟫ ≤ sumNorm x * maxNorm y := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [sumNorm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    y i * x i ≤ |y i * x i| := le_abs_self _
    _ = |x i| * |y i| := by rw [abs_mul]; ring
    _ ≤ |x i| * maxNorm y := mul_le_mul_of_nonneg_left
      (coordinate_le_maxNorm y i) (abs_nonneg _)

lemma local_descent {d : ℕ} {f : Point d → ℝ} {L0 L1 : ℝ}
    (hL1 : 0 ≤ L1) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, L1 * maxNorm (y - x) ≤ 1 →
      sumNorm (gradient f y - gradient f x) ≤
        (L0 + L1 * sumNorm (gradient f x)) * maxNorm (y - x))
    (x v : Point d) (hv : L1 * maxNorm v ≤ 1) :
    f (x + v) ≤ f x + ⟪gradient f x, v⟫ +
      (L0 + L1 * sumNorm (gradient f x)) / 2 * maxNorm v ^ 2 := by
  let C := L0 + L1 * sumNorm (gradient f x)
  let F := fun t : ℝ => f (x + t • v)
  let F' := fun t : ℝ => ⟪gradient f (x + t • v), v⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const v |>.const_add x)
    simp only [id_eq, one_smul, toDual_apply_apply] at h
    exact h
  let B := fun t : ℝ => f x + t * ⟪gradient f x, v⟫ + t ^ 2 * (C / 2 * maxNorm v ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪gradient f x, v⟫ + C * maxNorm v ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪gradient f x, v⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (C / 2 * maxNorm v ^ 2)) using 1
    · rfl
    · dsimp; ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ ⟪gradient f x, v⟫ + C * maxNorm v ^ 2 * t := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.le
    have hrad : L1 * maxNorm (x + t • v - x) ≤ 1 := by
      rw [add_sub_cancel_left, maxNorm_smul, abs_of_nonneg ht.1]
      nlinarith [mul_nonneg hL1 (maxNorm_nonneg v)]
    have h := (inner_le_dual (gradient f (x + t • v) - gradient f x) v).trans
      (mul_le_mul_of_nonneg_right (hlip x (x + t • v) hrad) (maxNorm_nonneg v))
    simp only [add_sub_cancel_left, maxNorm_smul, abs_of_nonneg ht.1, inner_sub_left] at h
    dsimp [F', C] at *
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, C] using h

end LongTails.Proofs.AffineAdamGeometry
