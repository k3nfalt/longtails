import LongTails.Proofs.LocalizedMonotoneRadial
import LongTails.Proofs.LocalizedMonotoneChain
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalizedMonotoneConstruction

open LocalizedMonotoneProfile LocalizedMonotoneRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gate (a : ℝ) (u v x : E) : E := profile a ⟪v, x⟫ • u

lemma gate_hasFDerivAt (a : ℝ) (ha : 0 < a) (u v x : E) :
    HasFDerivAt (gate a u v) (slope a ⟪v, x⟫ • InnerProductSpace.rankOne ℝ u v) x := by
  have h := ((profile_hasDerivAt a ⟪v, x⟫ ha).comp_hasFDerivAt x
    (innerSL ℝ v).hasFDerivAt).smul_const u
  convert h using 1
  · rfl
  · ext z
    simp [InnerProductSpace.rankOne_apply, smul_smul]

noncomputable def axis {d : ℕ} (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single i 1

lemma axis_inner {d : ℕ} (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪axis i, x⟫ = x i := by
  rw [axis, EuclideanSpace.inner_single_left]
  simp

noncomputable def chain {d n : ℕ} (a c : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  c • axis (π 0) - gate a (axis (π 0)) (axis (π (Fin.last n))) x +
    ∑ j : Fin n, gate a (axis (π j.succ)) (axis (π j.castSucc)) x

noncomputable def chainJacobian {d n : ℕ} (a : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  -(slope a (x (π (Fin.last n))) • InnerProductSpace.rankOne ℝ (axis (π 0)) (axis (π (Fin.last n)))) +
    ∑ j : Fin n, slope a (x (π j.castSucc)) •
      InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.castSucc))

lemma chain_hasFDerivAt {d n : ℕ} (a c : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (chain a c π) (chainJacobian a π x) x := by
  have h0 := (hasFDerivAt_const (c • axis (π 0)) x).sub
    (gate_hasFDerivAt a ha (axis (π 0)) (axis (π (Fin.last n))) x)
  have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
    gate_hasFDerivAt a ha (axis (π j.succ)) (axis (π j.castSucc)) x)
  convert h0.add hs using 1
  · rfl
  · simp only [chainJacobian, axis_inner, zero_sub]

lemma chain_zero {d n : ℕ} (a c : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    chain a c π x (π 0) = c - profile a (x (π (Fin.last n))) := by
  classical
  simp only [chain, gate, axis_inner]
  simp [axis, π.injective.eq_iff]

lemma chain_succ {d n : ℕ} (a c : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    chain a c π x (π j.succ) = profile a (x (π j.castSucc)) := by
  classical
  simp only [chain, gate, axis_inner]
  simp [axis, Pi.single_apply, π.injective.eq_iff]

lemma chain_outside {d n : ℕ} (a c : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (hi : ∀ j, i ≠ π j) :
    chain a c π x i = 0 := by
  classical
  simp only [chain, gate, axis_inner]
  simp [axis, hi]

lemma norm_sq_supported {d m : ℕ} (π : Fin m ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin d)) (hz : ∀ i, (∀ j, i ≠ π j) → z i = 0) :
    ‖z‖ ^ 2 = ∑ j : Fin m, z (π j) ^ 2 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  symm
  calc
    _ = ∑ i ∈ Finset.univ.map π, z i ^ 2 := by simp
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hzi : z i = 0 := hz i (by
        intro j hij
        apply hi
        exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hij.symm⟩)
      simp [hzi]

lemma chain_difference_sq {d n : ℕ} (a c : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖chain a c π x - chain a c π y‖ ^ 2 =
      ∑ j : Fin (n + 1), (profile a (x (π j)) - profile a (y (π j))) ^ 2 := by
  rw [norm_sq_supported π _ (by
    intro i hi
    simp only [PiLp.sub_apply, chain_outside a c π x i hi, chain_outside a c π y i hi, sub_self])]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [PiLp.sub_apply, chain_zero, chain_succ]
  have he : (c - profile a (x (π (Fin.last n))) - (c - profile a (y (π (Fin.last n))))) ^ 2 =
      (profile a (x (π (Fin.last n))) - profile a (y (π (Fin.last n)))) ^ 2 := by ring
  rw [he]
  ring

lemma chain_nonexpansive {d n : ℕ} (a c : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖chain a c π x - chain a c π y‖ ≤ ‖x - y‖ := by
  have hcoord := pow_le_pow_left₀
    (norm_nonneg (FiniteSumNondualLowerComponents.coordinateMap π (x - y)))
    (FiniteSumNondualLowerComponents.coordinateMap_norm π (x - y)) 2
  rw [EuclideanSpace.real_norm_sq_eq] at hcoord
  have hsq : ‖chain a c π x - chain a c π y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [chain_difference_sq]
    calc
      _ ≤ ∑ j : Fin (n + 1), (x (π j) - y (π j)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := pow_le_pow_left₀
          (abs_nonneg (profile a (x (π j)) - profile a (y (π j))))
          (profile_difference a (x (π j)) (y (π j)) ha) 2
        simpa only [sq_abs] using h
      _ ≤ _ := hcoord
  nlinarith [norm_nonneg (chain a c π x - chain a c π y), norm_nonneg (x - y)]

lemma chainJacobian_zero {d n : ℕ} (a : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x z : EuclideanSpace ℝ (Fin d)) :
    chainJacobian a π x z (π 0) = -slope a (x (π (Fin.last n))) * z (π (Fin.last n)) := by
  classical
  simp only [chainJacobian, add_apply, neg_apply, smul_apply, sum_apply,
    InnerProductSpace.rankOne_apply, axis_inner]
  simp [axis, π.injective.eq_iff]

lemma chainJacobian_succ {d n : ℕ} (a : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x z : EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    chainJacobian a π x z (π j.succ) = slope a (x (π j.castSucc)) * z (π j.castSucc) := by
  classical
  simp only [chainJacobian, add_apply, neg_apply, smul_apply, sum_apply,
    InnerProductSpace.rankOne_apply, axis_inner]
  simp [axis, Pi.single_apply, π.injective.eq_iff]

lemma chainJacobian_outside {d n : ℕ} (a : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x z : EuclideanSpace ℝ (Fin d)) (i : Fin d) (hi : ∀ j, i ≠ π j) :
    chainJacobian a π x z i = 0 := by
  classical
  simp only [chainJacobian, add_apply, neg_apply, smul_apply, sum_apply,
    InnerProductSpace.rankOne_apply, axis_inner]
  simp [axis, hi]

lemma chainJacobian_difference_sq {d n : ℕ} (a : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x y z : EuclideanSpace ℝ (Fin d)) :
    ‖(chainJacobian a π x - chainJacobian a π y) z‖ ^ 2 =
      ∑ j : Fin (n + 1), ((slope a (x (π j)) - slope a (y (π j))) * z (π j)) ^ 2 := by
  rw [norm_sq_supported π _ (by
    intro i hi
    simp only [sub_apply, PiLp.sub_apply, chainJacobian_outside a π x z i hi,
      chainJacobian_outside a π y z i hi, sub_self])]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [sub_apply, PiLp.sub_apply, chainJacobian_zero, chainJacobian_succ, sub_mul]
  ring

lemma chainJacobian_difference {d n : ℕ} (a : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖chainJacobian a π x - chainJacobian a π y‖ ≤ 2 / a * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hcoord := pow_le_pow_left₀
    (norm_nonneg (FiniteSumNondualLowerComponents.coordinateMap π z))
    (FiniteSumNondualLowerComponents.coordinateMap_norm π z) 2
  rw [EuclideanSpace.real_norm_sq_eq] at hcoord
  have hsq : ‖(chainJacobian a π x - chainJacobian a π y) z‖ ^ 2 ≤
      (2 / a * ‖x - y‖) ^ 2 * ‖z‖ ^ 2 := by
    rw [chainJacobian_difference_sq]
    calc
      _ ≤ ∑ j : Fin (n + 1), (2 / a * ‖x - y‖) ^ 2 * z (π j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hp : |x (π j) - y (π j)| ≤ ‖x - y‖ := by
          simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (x - y) (π j)
        have hd := (slope_difference a (x (π j)) (y (π j)) ha).trans
          (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 / a))
        have hs := pow_le_pow_left₀ (abs_nonneg _) hd 2
        rw [sq_abs] at hs
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = (2 / a * ‖x - y‖) ^ 2 * ∑ j : Fin (n + 1), z (π j) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoord (sq_nonneg _)
  have hn : 0 ≤ 2 / a * ‖x - y‖ * ‖z‖ := by positivity
  nlinarith [norm_nonneg ((chainJacobian a π x - chainJacobian a π y) z)]

lemma chainJacobian_norm {d n : ℕ} (a : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖chainJacobian a π x‖ ≤ 1 := by
  have hL : LipschitzWith 1 (chain a 0 π) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro u v
    simpa only [NNReal.coe_one, one_mul] using chain_nonexpansive a 0 ha π u v
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hL
  rw [(chain_hasFDerivAt a 0 ha π x).fderiv] at h
  exact h

noncomputable def rootPoint {d n : ℕ} (M b : ℝ) (π : Fin (n + 1) ↪ Fin d) :
    EuclideanSpace ℝ (Fin d) := ∑ j : Fin (n + 1), (M + (n - j.val : ℕ) * b) • axis (π j)

lemma rootPoint_coordinate {d n : ℕ} (M b : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (j : Fin (n + 1)) : rootPoint M b π (π j) = M + (n - j.val : ℕ) * b := by
  classical
  simp [rootPoint, axis, Pi.single_apply, π.injective.eq_iff]

lemma rootPoint_outside {d n : ℕ} (M b : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (i : Fin d) (hi : ∀ j, i ≠ π j) : rootPoint M b π i = 0 := by
  classical
  simp [rootPoint, axis, hi]

lemma rootPoint_norm_sq {d n : ℕ} (M b : ℝ) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (π : Fin (n + 1) ↪ Fin d) :
    ‖rootPoint M b π‖ ^ 2 ≤ (n + 1) * (M + n * b) ^ 2 := by
  rw [norm_sq_supported π _ (rootPoint_outside M b π)]
  simp only [rootPoint_coordinate]
  calc
    _ ≤ ∑ _j : Fin (n + 1), (M + n * b) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (by positivity)
      have h : ((n - j.val : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n j.val
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h hb)
    _ = _ := by simp

lemma chain_root {d n : ℕ} (a M : ℝ) (ha : 0 < a) (hM : 2 * a ≤ M)
    (hn : 1 ≤ n) (π : Fin (n + 1) ↪ Fin d) :
    chain a (2 * M + (n - 1 : ℕ) * (3 * a / 2)) π (rootPoint M (3 * a / 2) π) =
      rootPoint M (3 * a / 2) π := by
  classical
  ext i
  by_cases hi : ∃ j, i = π j
  · obtain ⟨j, rfl⟩ := hi
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [chain_zero, rootPoint_coordinate, rootPoint_coordinate]
      simp only [Fin.val_last, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero,
        Fin.val_zero, Nat.sub_zero]
      rw [profile_affine a M ha hM]
      have hn' : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub hn]
        norm_num
      rw [hn']
      ring
    · rw [chain_succ, rootPoint_coordinate, rootPoint_coordinate]
      have hp : 2 * a ≤ M + (n - j.castSucc.val : ℕ) * (3 * a / 2) := by
        have : 0 ≤ (n - j.castSucc.val : ℕ) * (3 * a / 2) := by positivity
        linarith
      rw [profile_affine a _ ha hp]
      have he : n - j.castSucc.val = (n - j.succ.val) + 1 := by
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      rw [he, Nat.cast_add, Nat.cast_one]
      ring
  · have hi' : ∀ j, i ≠ π j := by simpa only [not_exists] using hi
    rw [chain_outside _ _ π _ i hi', rootPoint_outside _ _ π i hi']

end LongTails.Proofs.LocalizedMonotoneConstruction
