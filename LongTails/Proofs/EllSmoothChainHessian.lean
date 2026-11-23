import LongTails.Proofs.EllSmoothChain

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.EllSmoothChainHessian

open LongTails.Proofs.EllSmoothProfiles
open LongTails.Proofs.AbcChainProfiles (pos rr abs_sub_le_sum pos_nonneg pos_of_nonneg pos_of_nonpos)
open LongTails.Proofs.EllSmoothChain

variable (S : Shape) {n : ℕ}

lemma linkA_hasFDerivAt (i j : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => linkA S (x i) (x j))
      (linkAA S (u i) (u j) • prj i + linkAB S (u i) (u j) • prj j) u := by
  have h1 := comp_neg_coord_hasFDerivAt i u (dpsi_hasDerivAt (-u i))
  have h2 := comp_neg_coord_hasFDerivAt j u (phi_hasDerivAt S (-u j))
  have h3 := comp_coord_hasFDerivAt i u (dpsi_hasDerivAt (u i))
  have h4 := comp_coord_hasFDerivAt j u (phi_hasDerivAt S (u j))
  have h := ((h1.mul h2).neg).sub (h3.mul h4)
  refine h.congr_fderiv ?_
  ext v
  simp only [linkAA, linkAB, add_apply, smul_apply,
    sub_apply, neg_apply, smul_eq_mul, prj_apply]
  ring

lemma linkB_hasFDerivAt (i j : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => linkB S (x i) (x j))
      (linkAB S (u i) (u j) • prj i + linkBB S (u i) (u j) • prj j) u := by
  have h1 := comp_neg_coord_hasFDerivAt i u (psi_hasDerivAt (-u i))
  have h2 := comp_neg_coord_hasFDerivAt j u (dphi_hasDerivAt S (-u j))
  have h3 := comp_coord_hasFDerivAt i u (psi_hasDerivAt (u i))
  have h4 := comp_coord_hasFDerivAt j u (dphi_hasDerivAt S (u j))
  have h := ((h1.mul h2).neg).sub (h3.mul h4)
  refine h.congr_fderiv ?_
  ext v
  simp only [linkAB, linkBB, add_apply, smul_apply,
    sub_apply, neg_apply, smul_eq_mul, prj_apply]
  ring

noncomputable def rowFirst (u : Chain n) : Fin (n + 1) → (Chain n →L[ℝ] ℝ) :=
  Fin.cases ((-ddphi S (u 0)) • prj 0) (fun _ => 0)

noncomputable def rowA (u : Chain n) : Fin (n + 1) → (Chain n →L[ℝ] ℝ) :=
  Fin.lastCases 0 (fun i : Fin n => linkAA S (u i.castSucc) (u i.succ) • prj i.castSucc +
    linkAB S (u i.castSucc) (u i.succ) • prj i.succ)

noncomputable def rowB (u : Chain n) : Fin (n + 1) → (Chain n →L[ℝ] ℝ) :=
  Fin.cases 0 (fun i : Fin n => linkAB S (u i.castSucc) (u i.succ) • prj i.castSucc +
    linkBB S (u i.castSucc) (u i.succ) • prj i.succ)

lemma fieldFirst_hasFDerivAt (k : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => fieldFirst S x k) (rowFirst S u k) u := by
  induction k using Fin.cases with
  | zero =>
    simp only [fieldFirst, rowFirst, Fin.cases_zero]
    have h := (comp_coord_hasFDerivAt (0 : Fin (n + 1)) u (dphi_hasDerivAt S (u 0))).neg
    refine h.congr_fderiv ?_
    exact (neg_smul _ _).symm
  | succ i =>
    simp only [fieldFirst, rowFirst, Fin.cases_succ]
    exact hasFDerivAt_const _ _

lemma fieldA_hasFDerivAt (k : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => fieldA S x k) (rowA S u k) u := by
  induction k using Fin.lastCases with
  | last =>
    simp only [fieldA, rowA, Fin.lastCases_last]
    exact hasFDerivAt_const _ _
  | cast i =>
    simp only [fieldA, rowA, Fin.lastCases_castSucc]
    exact linkA_hasFDerivAt S i.castSucc i.succ u

lemma fieldB_hasFDerivAt (k : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => fieldB S x k) (rowB S u k) u := by
  induction k using Fin.cases with
  | zero =>
    simp only [fieldB, rowB, Fin.cases_zero]
    exact hasFDerivAt_const _ _
  | succ i =>
    simp only [fieldB, rowB, Fin.cases_succ]
    exact linkB_hasFDerivAt S i.castSucc i.succ u

lemma field_coord_hasFDerivAt (k : Fin (n + 1)) (u : Chain n) :
    HasFDerivAt (fun x : Chain n => field S x k)
      (rowFirst S u k + rowA S u k + rowB S u k) u :=
  ((fieldFirst_hasFDerivAt S k u).add (fieldA_hasFDerivAt S k u)).add (fieldB_hasFDerivAt S k u)

lemma field_differentiableAt (u : Chain n) : DifferentiableAt ℝ (field S) u :=
  differentiableAt_euclidean.mpr (fun k => (field_coord_hasFDerivAt S k u).differentiableAt)

lemma field_hasFDerivAt (u : Chain n) :
    HasFDerivAt (field S) (fderiv ℝ (field S) u) u := (field_differentiableAt S u).hasFDerivAt

lemma fderiv_field_apply (u v : Chain n) (k : Fin (n + 1)) :
    (fderiv ℝ (field S) u v) k = (rowFirst S u k + rowA S u k + rowB S u k) v := by
  have h1 := hasFDerivWithinAt_univ.mp
    ((hasFDerivWithinAt_euclidean (t := Set.univ)).mp
      (field_hasFDerivAt S u).hasFDerivWithinAt k)
  have h2 := field_coord_hasFDerivAt S k u
  have h3 := h1.unique h2
  have h4 := congrArg (fun L : Chain n →L[ℝ] ℝ => L v) h3
  simpa using h4

lemma sum_rowFirst_sq (u v : Chain n) :
    ∑ k, (rowFirst S u k v) ^ 2 = (ddphi S (u 0) * v 0) ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp [rowFirst, prj_apply]

lemma sum_rowA_sq (u v : Chain n) :
    ∑ k, (rowA S u k v) ^ 2 = ∑ i : Fin n,
      (linkAA S (u i.castSucc) (u i.succ) * v i.castSucc +
        linkAB S (u i.castSucc) (u i.succ) * v i.succ) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp [rowA, prj_apply]

lemma sum_rowB_sq (u v : Chain n) :
    ∑ k, (rowB S u k v) ^ 2 = ∑ i : Fin n,
      (linkAB S (u i.castSucc) (u i.succ) * v i.castSucc +
        linkBB S (u i.castSucc) (u i.succ) * v i.succ) ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp [rowB, prj_apply]

lemma two_term_sq (a b x y A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    (a * x + b * y) ^ 2 ≤ 2 * A ^ 2 * x ^ 2 + 2 * B ^ 2 * y ^ 2 := by
  have h1 : a ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have h2 : b ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  nlinarith [sq_nonneg (a * x - b * y), mul_le_mul_of_nonneg_right h1 (sq_nonneg x),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg y)]

lemma fderiv_field_norm_le (u : Chain n) : ‖fderiv ℝ (field S) u‖ ≤ 1000 / S.th := by
  have hth := S.hth
  have hth' := S.hth'
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hinv : 4 ≤ 1 / S.th ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsq : ‖fderiv ℝ (field S) u v‖ ^ 2 ≤ (1000 / S.th * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hpt (k : Fin (n + 1)) : (fderiv ℝ (field S) u v k) ^ 2 ≤
        3 * ((rowFirst S u k v) ^ 2 + (rowA S u k v) ^ 2 + (rowB S u k v) ^ 2) := by
      rw [fderiv_field_apply]
      simp only [add_apply]
      nlinarith [sq_nonneg (rowFirst S u k v - rowA S u k v),
        sq_nonneg (rowFirst S u k v - rowB S u k v), sq_nonneg (rowA S u k v - rowB S u k v)]
    have h1 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_rowFirst_sq,
      sum_rowA_sq, sum_rowB_sq] at h1
    have hc := AbcChain.sum_castSucc_sq_le (fun k => v k)
    have hu := AbcChain.sum_succ_sq_le (fun k => v k)
    have hz := AbcChain.zero_sq_le (fun k => v k)
    have hnv : ∑ k, v k ^ 2 = ‖v‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq v).symm
    have h0 : (ddphi S (u 0) * v 0) ^ 2 ≤ (4 / S.th) ^ 2 * v 0 ^ 2 := by
      have hd := ddphi_abs_le S (u 0)
      have : ddphi S (u 0) ^ 2 ≤ (4 / S.th) ^ 2 := by
        rw [← sq_abs (ddphi S (u 0))]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hA : ∑ i : Fin n, (linkAA S (u i.castSucc) (u i.succ) * v i.castSucc +
        linkAB S (u i.castSucc) (u i.succ) * v i.succ) ^ 2 ≤
        ∑ i : Fin n, (2 * 720 ^ 2 * v i.castSucc ^ 2 + 2 * 10 ^ 2 * v i.succ ^ 2) :=
      Finset.sum_le_sum (fun i _ => two_term_sq _ _ _ _ _ _ (linkAA_abs S _ _) (linkAB_abs S _ _))
    have hB : ∑ i : Fin n, (linkAB S (u i.castSucc) (u i.succ) * v i.castSucc +
        linkBB S (u i.castSucc) (u i.succ) * v i.succ) ^ 2 ≤
        ∑ i : Fin n, (2 * 10 ^ 2 * v i.castSucc ^ 2 + 2 * (8 / S.th) ^ 2 * v i.succ ^ 2) :=
      Finset.sum_le_sum (fun i _ => two_term_sq _ _ _ _ _ _ (linkAB_abs S _ _) (linkBB_abs S _ _))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hA hB
    have e1 : (4 / S.th) ^ 2 = 16 * (1 / S.th ^ 2) := by ring
    have e2 : (8 / S.th) ^ 2 = 64 * (1 / S.th ^ 2) := by ring
    have e3 : (1000 / S.th * ‖v‖) ^ 2 = 1000000 * (1 / S.th ^ 2) * ‖v‖ ^ 2 := by
      ring
    rw [e1] at h0
    rw [e2] at hB
    rw [e3]
    have hv0 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hI : 0 ≤ 1 / S.th ^ 2 := by positivity
    have hs1 := Finset.sum_nonneg (fun (i : Fin n) (_ : i ∈ Finset.univ) => sq_nonneg (v i.castSucc))
    have hs2 := Finset.sum_nonneg (fun (i : Fin n) (_ : i ∈ Finset.univ) => sq_nonneg (v i.succ))
    have hz0 : 0 ≤ v 0 ^ 2 := sq_nonneg _
    rw [hnv] at hc hu hz
    nlinarith [mul_le_mul_of_nonneg_left hc hI, mul_le_mul_of_nonneg_left hu hI,
      mul_le_mul_of_nonneg_left hz hI, mul_le_mul_of_nonneg_right hinv hv0]
  exact le_of_sq_le_sq hsq (by positivity)

lemma rowA_of_fin (u : Chain n) (hfin : ∀ k : Fin (n + 1), 1 ≤ |u k|) (k : Fin (n + 1)) :
    rowA S u k = 0 := by
  induction k using Fin.lastCases with
  | last => simp [rowA]
  | cast i =>
    simp only [rowA, Fin.lastCases_castSucc]
    rw [linkAA_of_large S _ (hfin i.castSucc), linkAB_of_large S _ (hfin i.castSucc)]
    simp

lemma fieldA_of_fin (u : Chain n) (hfin : ∀ k : Fin (n + 1), 1 ≤ |u k|) (k : Fin (n + 1)) :
    fieldA S u k = 0 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i =>
    simp only [fieldA, Fin.lastCases_castSucc]
    exact linkA_of_large S _ (hfin i.castSucc)

lemma row_fin_bound (u v : Chain n) (hfin : ∀ k : Fin (n + 1), 1 ≤ |u k|) (k : Fin (n + 1)) :
    |(rowFirst S u k + rowA S u k + rowB S u k) v| ≤
      (36 / S.th * |field S u k| ^ (2 - S.th) + S.mu) * |v k| := by
  rw [rowA_of_fin S u hfin k, field_apply, fieldA_of_fin S u hfin k]
  induction k using Fin.cases with
  | zero =>
    simp only [rowFirst, rowB, fieldFirst, fieldB, Fin.cases_zero, add_zero,
      smul_apply, prj_apply, smul_eq_mul, abs_mul, abs_neg]
    rw [abs_of_nonneg (dphi_nonneg S (u 0))]
    exact mul_le_mul_of_nonneg_right (ddphi_relative S (u 0)) (abs_nonneg _)
  | succ i =>
    simp only [rowFirst, rowB, fieldFirst, fieldB, Fin.cases_succ, add_zero, zero_add,
      add_apply, smul_apply, prj_apply, smul_eq_mul]
    rw [linkAB_of_large S _ (hfin i.castSucc), zero_mul, zero_add, abs_mul]
    exact mul_le_mul_of_nonneg_right (linkBB_relative S _ (hfin i.castSucc)) (abs_nonneg _)

lemma fderiv_field_relative (u : Chain n) (hfin : ∀ k : Fin (n + 1), 1 ≤ |u k|) :
    ‖fderiv ℝ (field S) u‖ ≤ 36 / S.th * ‖field S u‖ ^ (2 - S.th) + S.mu := by
  have hth := S.hth
  have hth' := S.hth'
  have hmu := S.hmu
  have hexp : (0 : ℝ) ≤ 2 - S.th := by linarith
  have hc0 : 0 ≤ 36 / S.th * ‖field S u‖ ^ (2 - S.th) + S.mu := by
    have := Real.rpow_nonneg (norm_nonneg (field S u)) (2 - S.th)
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hc0
  intro v
  have hsq : ‖fderiv ℝ (field S) u v‖ ^ 2 ≤
      ((36 / S.th * ‖field S u‖ ^ (2 - S.th) + S.mu) * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq v,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [fderiv_field_apply]
    have h1 := row_fin_bound S u v hfin k
    have h2 : 36 / S.th * |field S u k| ^ (2 - S.th) + S.mu ≤
        36 / S.th * ‖field S u‖ ^ (2 - S.th) + S.mu := by
      have := Real.rpow_le_rpow (abs_nonneg _) (abs_coord_le (field S u) k) hexp
      have h36 : (0 : ℝ) ≤ 36 / S.th := by positivity
      nlinarith
    have h3 : |(rowFirst S u k + rowA S u k + rowB S u k) v| ≤
        (36 / S.th * ‖field S u‖ ^ (2 - S.th) + S.mu) * |v k| :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [mul_pow, sq_abs, sq_abs] at h4
    exact h4
  exact le_of_sq_le_sq hsq (mul_nonneg hc0 (norm_nonneg v))

lemma fderiv_field_bound (u : Chain n) :
    ‖fderiv ℝ (field S) u‖ ≤
      1000 / S.th * min 1 (‖field S u‖ ^ (2 - S.th)) + S.mu := by
  have hth := S.hth
  have hth' := S.hth'
  have hmu := S.hmu
  have hglob := fderiv_field_norm_le S u
  have hx0 : 0 ≤ ‖field S u‖ ^ (2 - S.th) := Real.rpow_nonneg (norm_nonneg _) _
  have hc : (0 : ℝ) ≤ 1000 / S.th := by positivity
  by_cases hfin : ∀ k : Fin (n + 1), 1 ≤ |u k|
  · rcases le_total 1 (‖field S u‖ ^ (2 - S.th)) with h1 | h1
    · rw [min_eq_left h1]
      linarith
    · rw [min_eq_right h1]
      have hrel := fderiv_field_relative S u hfin
      have h36 : 36 / S.th ≤ 1000 / S.th := by gcongr; norm_num
      nlinarith
  · push Not at hfin
    have h1 := field_norm_ge_one S u hfin
    have h2 : 1 ≤ ‖field S u‖ ^ (2 - S.th) := Real.one_le_rpow h1 (by linarith)
    rw [min_eq_left h2]
    linarith

end LongTails.Proofs.EllSmoothChainHessian
