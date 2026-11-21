import LongTails.Proofs.HessianPLWell
import LongTails.Proofs.RelativeHessianLocalized

namespace LongTails.Proofs.HessianPLChain

open scoped RealInnerProductSpace BigOperators
open RelativeHessianArctan RelativeHessianGate RelativeHessianGeometry HessianPLWell

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def rest {m : ℕ} (v : Fin (m + 1) → E) (x : E) : ℝ :=
  ‖x‖ ^ 2 - ∑ j, ⟪v j, x⟫ ^ 2

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma rest_nonneg {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    0 ≤ rest v x := by
  have h := RelativeHessianGuard.bessel hv x
  unfold rest
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma value_decomposition {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    RelativeHessianGuard.value v x - (m + 1 : ℕ) * bottom =
      coefficient / 2 * rest v x + (well ⟪v 0, x⟫ - bottom) +
        ∑ i : Fin m, (coefficient / 2 * ⟪v i.succ, x⟫ ^ 2 +
          RelativeHessianChain.link ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ - bottom) := by
  have hs : ∑ j : Fin (m + 1), ⟪v j, x⟫ ^ 2 =
      ⟪v 0, x⟫ ^ 2 + ∑ i : Fin m, ⟪v i.succ, x⟫ ^ 2 := Fin.sum_univ_succ _
  unfold RelativeHessianGuard.value chain rest well FullGeneralizedSmoothZeroQuery.quadratic
  simp only [edge_eq, RidgeJets.value, sub_zero]
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  ring

noncomputable def chainCoord {m : ℕ} (v : Fin (m + 1) → E) (x : E) (j : Fin (m + 1)) : ℝ :=
  ⟪gradient (chain v) x, v j⟫

lemma guard_coord {m : ℕ} (v : Fin (m + 1) → E) (x : E) (j : Fin (m + 1)) :
    ⟪gradient (RelativeHessianGuard.value v) x, v j⟫ =
      coefficient * ⟪v j, x⟫ + chainCoord v x j := by
  rw [RelativeHessianGuard.gradient_eq, inner_add_left, real_inner_smul_left,
    ← real_inner_comm x (v j)]
  unfold chainCoord
  ring

lemma chain_gradient_sum {m : ℕ} (v : Fin (m + 1) → E) (x : E) :
    gradient (chain v) x = -density ⟪v 0, x⟫ • v 0 +
      ∑ i : Fin m, gradient (edge (v i.castSucc) (v i.succ)) x := by
  rw [chain_gradient]
  simp_rw [edge_gradient]

lemma chainCoord_nonpos {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E)
    (j : Fin (m + 1)) : chainCoord v x j ≤ 0 := by
  classical
  unfold chainCoord
  rw [chain_gradient_sum, inner_add_left, real_inner_smul_left, sum_inner]
  have h0 : 0 ≤ ⟪v 0, v j⟫ := by
    rw [orthonormal_iff_ite.mp hv]
    split_ifs <;> norm_num
  have hd := (density_bounds ⟪v 0, x⟫).1
  have hs := Finset.sum_nonpos (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    RelativeHessianFirstSmall.edge_coordinate_nonpos hv x i j)
  nlinarith [mul_nonneg hd.le h0]

lemma edge_coord {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) (i : Fin m)
    (j : Fin (m + 1)) :
    ⟪gradient (edge (v i.castSucc) (v i.succ)) x, v j⟫ =
      RelativeHessianChain.outgoing ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ *
          (if i.castSucc = j then 1 else 0) -
        (gate ⟪v i.castSucc, x⟫ + gate (-⟪v i.castSucc, x⟫)) * density ⟪v i.succ, x⟫ *
          (if i.succ = j then 1 else 0) := by
  classical
  rw [edge_gradient, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hv]

lemma chainCoord_lower {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E)
    (j : Fin (m + 1)) (hj : 1 / 5 ≤ |⟪v j, x⟫|) : -2 ≤ chainCoord v x j := by
  classical
  unfold chainCoord
  rw [chain_gradient_sum, inner_add_left, real_inner_smul_left, sum_inner]
  have h0 : ⟪v 0, v j⟫ ≤ 1 ∧ 0 ≤ ⟪v 0, v j⟫ := by
    rw [orthonormal_iff_ite.mp hv]
    split_ifs <;> norm_num
  have hd := density_bounds ⟪v 0, x⟫
  have hterm (i : Fin m) : -(if i.succ = j then (1 : ℝ) else 0) ≤
        ⟪gradient (edge (v i.castSucc) (v i.succ)) x, v j⟫ := by
    rw [edge_coord hv x i j]
    have hg1 := gate_bounds ⟪v i.castSucc, x⟫
    have hg2 := gate_bounds (-⟪v i.castSucc, x⟫)
    have hdd := density_bounds ⟪v i.succ, x⟫
    have hG0 : 0 ≤ (gate ⟪v i.castSucc, x⟫ + gate (-⟪v i.castSucc, x⟫)) *
        density ⟪v i.succ, x⟫ := mul_nonneg (add_nonneg hg1.1 hg2.1) hdd.1.le
    have hG : (gate ⟪v i.castSucc, x⟫ + gate (-⟪v i.castSucc, x⟫)) *
        density ⟪v i.succ, x⟫ ≤ 1 := by
      have h := mul_le_mul (gate_pair_le_one ⟪v i.castSucc, x⟫) hdd.2 hdd.1.le
        (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have ho : RelativeHessianChain.outgoing ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ *
        (if i.castSucc = j then (1 : ℝ) else 0) = 0 := by
      by_cases h : i.castSucc = j
      · rw [h, outgoing_plateau hj, zero_mul]
      · rw [ite_eq_right h, mul_zero]
    rw [ho]
    split_ifs <;> simp only [mul_one, mul_zero, sub_zero, zero_sub] <;> linarith
  have hsu : (∑ i : Fin m, if i.succ = j then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_one.mpr (by
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.succ_injective _ (ha.trans hb.symm))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hterm i)
  rw [Finset.sum_neg_distrib] at hs
  have hp : density ⟪v 0, x⟫ * ⟪v 0, v j⟫ ≤ 1 := by
    have h := mul_le_mul hd.2 h0.1 h0.2 (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  nlinarith

noncomputable def proj {m : ℕ} (v : Fin (m + 1) → E) : E →L[ℝ] E :=
  ∑ j, (innerSL ℝ (v j)).smulRight (v j)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma proj_apply {m : ℕ} (v : Fin (m + 1) → E) (u : E) :
    proj v u = ∑ j, ⟪v j, u⟫ • v j := by
  simp [proj]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma proj_basis {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (k : Fin (m + 1)) :
    proj v (v k) = v k := by
  classical
  rw [proj_apply]
  simp [orthonormal_iff_ite.mp hv]

lemma proj_chain {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    proj v (gradient (chain v) x) = gradient (chain v) x := by
  rw [chain_gradient]
  simp only [map_add, map_sum, map_sub, map_smul, proj_basis hv]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma residual_sq {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (u : E) :
    ‖u - proj v u‖ ^ 2 = ‖u‖ ^ 2 - ∑ j, ⟪v j, u⟫ ^ 2 := by
  have hp : ⟪u, proj v u⟫ = ∑ j, ⟪v j, u⟫ ^ 2 := by
    rw [proj_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_right, real_inner_comm (v j) u]
    ring
  have hpp : ‖proj v u‖ ^ 2 = ∑ j, ⟪v j, u⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, proj_apply, hv.inner_sum]
    simp [sq]
  rw [norm_sub_sq_real, hp, hpp]
  ring

lemma guard_gradient_sq {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    ‖gradient (RelativeHessianGuard.value v) x‖ ^ 2 =
      ∑ j, ⟪gradient (RelativeHessianGuard.value v) x, v j⟫ ^ 2 +
        coefficient ^ 2 * rest v x := by
  have hres : gradient (RelativeHessianGuard.value v) x -
      proj v (gradient (RelativeHessianGuard.value v) x) = coefficient • (x - proj v x) := by
    rw [RelativeHessianGuard.gradient_eq, map_add, map_smul, proj_chain hv]
    module
  have h1 := residual_sq hv (gradient (RelativeHessianGuard.value v) x)
  have h2 := residual_sq hv x
  rw [hres, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, h2] at h1
  have hc : ∀ j, ⟪v j, gradient (RelativeHessianGuard.value v) x⟫ =
      ⟪gradient (RelativeHessianGuard.value v) x, v j⟫ := fun j => real_inner_comm _ _
  simp only [hc] at h1
  unfold rest
  linarith

theorem guard_pl {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) :
    RelativeHessianGuard.value v x - (m + 1 : ℕ) * bottom ≤
      2 ^ 9 * (m + 1 : ℕ) * ‖gradient (RelativeHessianGuard.value v) x‖ ^ 2 := by
  classical
  have hdec := value_decomposition v x
  have hsq := guard_gradient_sq hv x
  have hrest := rest_nonneg hv x
  obtain ⟨g, hg⟩ : ∃ g : Fin (m + 1) → ℝ,
      ∀ j, g j = ⟪gradient (RelativeHessianGuard.value v) x, v j⟫ := ⟨_, fun _ => rfl⟩
  simp only [← hg] at hsq
  have hG7 : (∃ i, |⟪v i, x⟫| ≤ 1 / 5) →
      7 / 10 ≤ ‖gradient (RelativeHessianGuard.value v) x‖ :=
    RelativeHessianFirstSmall.gradient_norm hv x
  have hGc : ∀ j, |g j| ≤ ‖gradient (RelativeHessianGuard.value v) x‖ := by
    intro j
    have h := abs_real_inner_le_norm (gradient (RelativeHessianGuard.value v) x) (v j)
    rwa [hv.norm_eq_one, mul_one, ← hg j] at h
  obtain ⟨R, hR, hR0⟩ : ∃ R : ℝ, R = ‖gradient (RelativeHessianGuard.value v) x‖ ∧ 0 ≤ R :=
    ⟨_, rfl, norm_nonneg _⟩
  rw [← hR] at hsq hG7 hGc ⊢
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hN] at hdec ⊢
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast Nat.succ_pos m
  have hNm : N = (m : ℝ) + 1 := by
    rw [hN]
    push_cast
    ring
  have hgsum : ∑ j, g j ^ 2 = g 0 ^ 2 + ∑ i : Fin m, g i.succ ^ 2 := Fin.sum_univ_succ _
  have hgs0 : 0 ≤ ∑ j, g j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have har := half_le_sq_mul hrest
  have har0 : 0 ≤ coefficient ^ 2 * rest v x := mul_nonneg (sq_nonneg _) hrest
  have hQ0 : 0 ≤ R ^ 2 := sq_nonneg R
  have hNQ1 : R ^ 2 ≤ N * R ^ 2 := le_mul_of_one_le_left hQ0 hN1
  have h512 : (2 : ℝ) ^ 9 = 512 := by norm_num
  rw [h512]
  by_cases hall : ∀ j, 1 / 5 < ⟪v j, x⟫
  · have habs : ∀ i, 1 / 5 ≤ |⟪v i, x⟫| := fun i => (hall i).le.trans (le_abs_self _)
    have hgj : ∀ j, g j = RelativeHessianArctan.slope coefficient ⟪v j, x⟫ := fun j =>
      (hg j).trans (RelativeHessianGuard.gradient_coordinate_plateau hv x habs j)
    have h0 : well ⟪v 0, x⟫ - bottom ≤ 1 / 2 * g 0 ^ 2 := by
      rw [hgj 0]
      exact well_gap_le (by linarith [hall 0])
    have hi : ∀ i : Fin m, coefficient / 2 * ⟪v i.succ, x⟫ ^ 2 +
        RelativeHessianChain.link ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ - bottom ≤
          1 / 2 * g i.succ ^ 2 := by
      intro i
      rw [link_saturated (hall i.castSucc).le, hgj i.succ]
      have h := well_gap_le (t := ⟪v i.succ, x⟫) (by linarith [hall i.succ])
      unfold well at h
      linarith
    have hS := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hi i)
    rw [← Finset.mul_sum] at hS
    linarith
  · push Not at hall
    obtain ⟨j0, hj0⟩ := hall
    have hGnorm : 1 / 25 ≤ R ^ 2 := by
      by_cases hex : ∃ i, |⟪v i, x⟫| ≤ 1 / 5
      · have h := sq_lower (by norm_num : (0 : ℝ) ≤ 7 / 10) (hG7 hex)
        norm_num at h
        linarith
      · push Not at hex
        have hneg : ⟪v j0, x⟫ < -(1 / 5) := by
          rcases lt_abs.mp (hex j0) with h1 | h1 <;> linarith
        have hle : g j0 ≤ -(1 / 5) := by
          rw [hg j0, guard_coord v x j0]
          exact negative_coordinate hneg (chainCoord_nonpos hv x j0)
        have hlow := (abs_le.mp (hGc j0)).1
        have h := sq_lower (by norm_num : (0 : ℝ) ≤ 1 / 5) (show (1 / 5 : ℝ) ≤ R by linarith)
        norm_num at h
        linarith
    have hy : ∀ j, ⟪v j, x⟫ ^ 2 ≤ 2 * g j ^ 2 + 8 := by
      intro j
      by_cases hj : 1 / 5 ≤ |⟪v j, x⟫|
      · exact coordinate_sq_le ((hg j).trans (guard_coord v x j)) (chainCoord_nonpos hv x j)
          (chainCoord_lower hv x j hj)
      · exact small_sq_le (lt_of_not_ge hj) (g j)
    have h0 := anchor_bracket_le ⟪v 0, x⟫
    have hS := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      link_bracket_le ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫)
    have hY := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (m + 1)))) => hy j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hY
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hS
    have hysum : ∑ j : Fin (m + 1), ⟪v j, x⟫ ^ 2 =
        ⟪v 0, x⟫ ^ 2 + ∑ i : Fin m, ⟪v i.succ, x⟫ ^ 2 := Fin.sum_univ_succ _
    rw [← hN] at hY
    have hNQ2 := mul_le_mul_of_nonneg_left hGnorm (show (0 : ℝ) ≤ N by linarith)
    linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma guard_unfinished {m : ℕ} {v : Fin (m + 1) → E} (hv : Orthonormal ℝ v) (x : E) (r : ℕ)
    (hsmall : ∀ j : Fin (m + 1), r ≤ j.val → |⟪v j, x⟫| ≤ 1 / 10) :
    (m : ℝ) - r ≤ RelativeHessianGuard.value v x - (m + 1 : ℕ) * bottom := by
  classical
  have hdec := value_decomposition v x
  have hrest := rest_nonneg hv x
  have ha := coefficient_bounds
  have hb := bottom_bounds
  have h0 : 0 ≤ well ⟪v 0, x⟫ - bottom := sub_nonneg.mpr (bottom_le_well _)
  have hi : ∀ i : Fin m, (if r ≤ i.val then (1 : ℝ) else 0) ≤
      coefficient / 2 * ⟪v i.succ, x⟫ ^ 2 +
        RelativeHessianChain.link ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫ - bottom := by
    intro i
    split_ifs with h
    · rw [link_flat (hsmall i.castSucc (by simpa using h))]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ coefficient / 2 by linarith)
        (sq_nonneg ⟪v i.succ, x⟫)]
    · linarith [link_bracket ⟪v i.castSucc, x⟫ ⟪v i.succ, x⟫]
  have hS := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hi i)
  have hcount : (m : ℝ) - r ≤ ∑ i : Fin m, (if r ≤ i.val then (1 : ℝ) else 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if r ≤ i then (1 : ℝ) else 0) m]
    by_cases hr : r ≤ m
    · calc (m : ℝ) - r = ((Finset.Ico r m).card : ℝ) := by
            rw [Nat.card_Ico, Nat.cast_sub hr]
        _ = ∑ i ∈ Finset.Ico r m, (if r ≤ i then (1 : ℝ) else 0) := by
            rw [Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_Ico.mp hi).1)]
            simp
        _ ≤ ∑ i ∈ Finset.range m, (if r ≤ i then (1 : ℝ) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
            · intro i _ _
              split_ifs <;> norm_num
    · push Not at hr
      have hle : (m : ℝ) - r ≤ 0 := by
        have h : (m : ℝ) ≤ r := by exact_mod_cast hr.le
        linarith
      exact hle.trans (Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num))
  have hcoef : 0 ≤ coefficient / 2 * rest v x :=
    mul_nonneg (by linarith) hrest
  linarith

end LongTails.Proofs.HessianPLChain
