import LongTails.Proofs.RelativeHessianGuard

namespace LongTails.Proofs.RelativeHessianFirstSmall

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry RelativeHessianGuard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma edge_coordinate_nonpos {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (i : Fin m) (j : Fin (m + 1)) :
    ⟪gradient (edge (v i.castSucc) (v i.succ)) x, v j⟫ ≤ 0 := by
  classical
  have h₁ : 0 ≤ ⟪v i.castSucc, v j⟫ := by rw [orthonormal_iff_ite.mp hv]; split_ifs <;> norm_num
  have h₂ : 0 ≤ ⟪v i.succ, v j⟫ := by rw [orthonormal_iff_ite.mp hv]; split_ifs <;> norm_num
  have ho := mul_nonpos_of_nonpos_of_nonneg
    (RelativeHessianChain.outgoing_nonpos ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫) h₁
  have hi := mul_nonneg (mul_nonneg (add_nonneg (gate_bounds ⟪v i.castSucc, x⟫).1 (gate_bounds (-⟪v i.castSucc, x⟫)).1)
    (density_bounds ⟪v i.succ, x⟫).1.le) h₂
  rw [edge_gradient, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  linarith

lemma gradient_decomposition {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    gradient (value v) x = coefficient • x - density ⟪v 0, x⟫ • v 0 +
      ∑ i : Fin m, gradient (edge (v i.castSucc) (v i.succ)) x := by
  rw [RelativeHessianGuard.gradient_eq, chain_gradient]
  simp_rw [edge_gradient]
  module

lemma first_small {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (j : Fin (m + 1)) (hj : |⟪v j, x⟫| ≤ 1 / 5)
    (hprev : ∀ i < j, 1 / 5 < |⟪v i, x⟫|) :
    ⟪gradient (value v) x, v j⟫ ≤ -7 / 10 := by
  classical
  have he (i : Fin m) := edge_coordinate_nonpos hv x i j
  have hsmall := small_gradient hj
  rw [gradient_decomposition, inner_add_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, sum_inner, ← real_inner_comm x (v j)]
  rcases Fin.eq_zero_or_eq_succ j with hz | ⟨k, rfl⟩
  · subst j
    have hs := Finset.sum_nonpos (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => he i)
    rw [orthonormal_iff_ite.mp hv]
    simp only [ite_true, mul_one]
    linarith
  · have hki : k.castSucc < k.succ := by simp
    have hp := RelativeHessianChain.saturated_pair (hprev k.castSucc hki).le
    have hne : k.castSucc ≠ k.succ := by intro h; have := congrArg Fin.val h; simp at this
    have hk : ⟪gradient (edge (v k.castSucc) (v k.succ)) x, v k.succ⟫ = -density ⟪v k.succ, x⟫ := by
      rw [edge_gradient, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hv, hp]
      simp [hne]
    have hs : (∑ i : Fin m, ⟪gradient (edge (v i.castSucc) (v i.succ)) x, v k.succ⟫) ≤
        ⟪gradient (edge (v k.castSucc) (v k.succ)) x, v k.succ⟫ := by
      have h := Finset.sum_le_sum_of_subset_of_nonpos
        (show ({k} : Finset (Fin m)) ⊆ Finset.univ by simp)
        (fun i _ _ => he i)
      simpa using h
    rw [hk] at hs
    have hzero : 0 ≤ ⟪v 0, v k.succ⟫ := by
      rw [orthonormal_iff_ite.mp hv]
      split_ifs <;> norm_num
    have hanchor := mul_nonneg (density_bounds ⟪v 0, x⟫).1.le hzero
    linarith

lemma gradient_norm {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v)
    (x : E) (hex : ∃ i, |⟪v i, x⟫| ≤ 1 / 5) :
    7 / 10 ≤ ‖gradient (value v) x‖ := by
  classical
  let s : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => |⟪v i, x⟫| ≤ 1 / 5)
  have hs : s.Nonempty := by rcases hex with ⟨i, hi⟩; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let j := s.min' hs
  have hj : |⟪v j, x⟫| ≤ 1 / 5 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hp : ∀ i < j, 1 / 5 < |⟪v i, x⟫| := by
    intro i hi
    by_contra hn
    have hm : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hn⟩
    have hmin := Finset.min'_le s i hm
    exact (not_le_of_gt hi) hmin
  have h := first_small hv x j hj hp
  have hn := (abs_le.mp (abs_real_inner_le_norm (gradient (value v) x) (v j))).1
  rw [hv.norm_eq_one, mul_one] at hn
  linarith

lemma absolute_third {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x‖ ≤ (2 : ℝ) ^ 55 := by
  rw [third_eq]
  exact RelativeHessianJetBounds.chain_bound v (fun i => (hv.norm_eq_one i).le) (bessel hv) x

lemma relative_third {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (value v))) x‖ ≤ (2 : ℝ) ^ 56 * ‖gradient (value v) x‖ := by
  by_cases hx : ∀ i, 1 / 5 ≤ |⟪v i, x⟫|
  · exact (relative_plateau hv x hx).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  · have he : ∃ i, |⟪v i, x⟫| ≤ 1 / 5 := by
      push Not at hx
      rcases hx with ⟨i, hi⟩
      exact ⟨i, hi.le⟩
    have hg := gradient_norm hv x he
    have ht := absolute_third hv x
    linarith

lemma initial_gradient {m : ℕ} (v : Fin (m + 1) → E) :
    gradient (value v) 0 = -v 0 := by
  obtain ⟨hg, hgs, _, _⟩ := gate_flat (by norm_num : (0 : ℝ) ≤ 1 / 10)
  rw [RelativeHessianGuard.gradient_eq, chain_gradient]
  simp [RelativeHessianChain.outgoing, hg, hgs, density]

end LongTails.Proofs.RelativeHessianFirstSmall
