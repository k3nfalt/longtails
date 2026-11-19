import LongTails.Proofs.KhintchineSignFamily
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

open Finset
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LinfEmbedding

open LongTails.Proofs.KhintchineSignFamily

variable {p D d : ℕ} [Fact p.Prime] (κ : Coeff p ↪ Fin d)

noncomputable def down : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin D) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2
        (fun i => (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p, sign c i * x (κ c))
      map_add' := by
        intro x y
        ext i
        simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        ext i
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring }

noncomputable def up : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2
        (fun r => (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p,
          if κ c = r then proj c (fun i => w i) else 0)
      map_add' := by
        intro x y
        ext r
        simp only [PiLp.add_apply, proj, add_mul, Finset.sum_add_distrib, ite_add_zero, mul_add]
      map_smul' := by
        intro a x
        ext r
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases h : κ c = r
        · simp only [h, ite_true, proj, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        · simp [h] }

lemma down_apply (x : EuclideanSpace ℝ (Fin d)) (i : Fin D) :
    down (D := D) κ x i = (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p, sign c i * x (κ c) := rfl

lemma up_apply (w : EuclideanSpace ℝ (Fin D)) (r : Fin d) :
    up κ w r = (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p, if κ c = r then proj c (fun i => w i) else 0 :=
  rfl

lemma up_apply_kappa (w : EuclideanSpace ℝ (Fin D)) (c : Coeff p) :
    up κ w (κ c) = (1 / (p : ℝ) ^ 4) * proj c (fun i => w i) := by
  rw [up_apply, Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    rw [ite_eq_right_iff]
    intro h
    exact absurd (κ.injective h) hc'
  · simp

lemma up_apply_of_not_mem (w : EuclideanSpace ℝ (Fin D)) (r : Fin d) (hr : ∀ c, κ c ≠ r) :
    up κ w r = 0 := by
  rw [up_apply]
  simp [hr]

lemma sum_over_kappa (F : Fin d → ℝ) (hF : ∀ r, (∀ c, κ c ≠ r) → F r = 0) :
    ∑ r, F r = ∑ c : Coeff p, F (κ c) := by
  rw [← Finset.sum_map Finset.univ κ F]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  apply hF r
  intro c hc
  exact hr (Finset.mem_map.mpr ⟨c, Finset.mem_univ _, hc⟩)

lemma l1_up (w : EuclideanSpace ℝ (Fin D)) :
    ∑ r, |up κ w r| = (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p, |proj c (fun i => w i)| := by
  rw [sum_over_kappa κ (fun r => |up κ w r|) (fun r hr => by simp [up_apply_of_not_mem κ w r hr])]
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  simp only [up_apply_kappa, abs_mul, Finset.mul_sum, abs_of_pos (one_div_pos.mpr hp4)]

lemma inner_eq_sum' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : ⟪u, v⟫ = ∑ i, u i * v i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma inner_up (w : EuclideanSpace ℝ (Fin D)) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪up κ w, x⟫ = ⟪w, down κ x⟫ := by
  rw [inner_eq_sum', inner_eq_sum']
  rw [sum_over_kappa κ (fun r => up κ w r * x r)
    (fun r hr => by rw [up_apply_of_not_mem κ w r hr, zero_mul])]
  simp only [up_apply_kappa, down_apply, proj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring

variable (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

lemma l1_up_le (w : EuclideanSpace ℝ (Fin D)) : ∑ r, |up κ w r| ≤ ‖w‖ := by
  rw [l1_up, EuclideanSpace.norm_eq]
  have h := sum_abs_proj_le hDp hp2 (fun i => w i)
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by have := (Fact.out : p.Prime).pos; positivity
  have hsq : (∑ i, w i ^ 2) = ∑ i, ‖w i‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [← hsq]
  rw [one_div, inv_mul_le_iff₀ hp4]
  exact h

lemma l1_up_ge (h5 : 5 ≤ p) (w : EuclideanSpace ℝ (Fin D)) : ‖w‖ ≤ 3 * ∑ r, |up κ w r| := by
  rw [l1_up, EuclideanSpace.norm_eq]
  have h := sum_abs_proj_ge hDp hp2 h5 (fun i => w i)
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by have := (Fact.out : p.Prime).pos; positivity
  have hsq : (∑ i, w i ^ 2) = ∑ i, ‖w i‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [← hsq]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)] at h
  have : Real.sqrt (∑ i, w i ^ 2) * (p : ℝ) ^ 4 ≤ 3 * ∑ c : Coeff p, |proj c fun i => w i| := by
    linarith
  calc Real.sqrt (∑ i, w i ^ 2) = Real.sqrt (∑ i, w i ^ 2) * (p : ℝ) ^ 4 * (1 / (p : ℝ) ^ 4) := by
        field_simp
    _ ≤ 3 * (∑ c : Coeff p, |proj c fun i => w i|) * (1 / (p : ℝ) ^ 4) := by
        gcongr
    _ = _ := by ring

lemma down_norm_le (x : EuclideanSpace ℝ (Fin d)) (R : ℝ) (hx : ∀ r, |x r| ≤ R) :
    ‖down (D := D) κ x‖ ≤ R := by
  set u := down (D := D) κ x
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hx (κ (fun _ => 0)))
  have h1 : ‖u‖ ^ 2 = ⟪up κ u, x⟫ := by rw [inner_up, real_inner_self_eq_norm_sq]
  have h2 : ⟪up κ u, x⟫ ≤ R * ∑ r, |up κ u r| := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    calc x r * up κ u r ≤ |x r * up κ u r| := le_abs_self _
      _ = |x r| * |up κ u r| := abs_mul _ _
      _ ≤ R * |up κ u r| := mul_le_mul_of_nonneg_right (hx r) (abs_nonneg _)
  have h3 := l1_up_le κ hDp hp2 u
  have h4 : ‖u‖ ^ 2 ≤ R * ‖u‖ := by
    calc ‖u‖ ^ 2 ≤ R * ∑ r, |up κ u r| := h1 ▸ h2
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_left h3 hR
  by_cases hu : ‖u‖ = 0
  · rw [hu]; exact hR
  · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    nlinarith

lemma second_moment_euclid (w : EuclideanSpace ℝ (Fin D)) :
    ∑ c : Coeff p, proj c (fun i => w i) ^ 2 = A1 p * ‖w‖ ^ 2 := by
  rw [second_moment hDp hp2, EuclideanSpace.real_norm_sq_eq]

lemma proj_sq_le (w : EuclideanSpace ℝ (Fin D)) (c : Coeff p) :
    proj c (fun i => w i) ^ 2 ≤ A1 p * ‖w‖ ^ 2 := by
  rw [← second_moment_euclid hDp hp2 w]
  exact Finset.single_le_sum (f := fun c => proj c (fun i => w i) ^ 2)
    (fun c _ => sq_nonneg _) (Finset.mem_univ c)

omit [Fact (Nat.Prime p)] hDp hp2 in
lemma A1_le_pow (hp : 1 ≤ p) : A1 p ≤ (p : ℝ) ^ 4 := by
  unfold A1
  have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
  nlinarith

lemma up_coord_abs_le (w : EuclideanSpace ℝ (Fin D)) (r : Fin d) : |up κ w r| ≤ ‖w‖ :=
  (Finset.single_le_sum (f := fun r => |up κ w r|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ r)).trans (l1_up_le κ hDp hp2 w)

lemma down_up (w : EuclideanSpace ℝ (Fin D)) :
    down κ (up κ w) = (A1 p / (p : ℝ) ^ 8) • w := by
  ext i
  simp only [down_apply, up_apply_kappa, PiLp.smul_apply, smul_eq_mul, proj]
  have h : ∀ c : Coeff p, sign c i * ((1 / (p : ℝ) ^ 4) * ∑ j, w j * sign c j) =
      (1 / (p : ℝ) ^ 4) * ∑ j, w j * (sign c i * sign c j) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun c _ => h c, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_eq_single i]
  · rw [← Finset.mul_sum, show (fun c : Coeff p => sign c i * sign c i) =
      fun c => sign c i ^ 2 by funext c; ring, sum_sign_sq hDp]
    have : (0 : ℝ) < (p : ℝ) := by have := (Fact.out : p.Prime).pos; exact_mod_cast this
    field_simp
  · intro j _ hji
    rw [← Finset.mul_sum, sum_sign_mul hDp hp2 (Ne.symm hji), mul_zero]
  · simp

end LongTails.Proofs.LinfEmbedding
