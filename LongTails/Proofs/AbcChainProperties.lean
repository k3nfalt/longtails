import LongTails.Proofs.AbcChain

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcChainProperties

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.AbcChain

variable {n : ℕ}

lemma coord_sq_le (x : Chain n) (k : Fin (n + 1)) : x k ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ k)

lemma abs_coord_le (x : Chain n) (k : Fin (n + 1)) : |x k| ≤ ‖x‖ := by
  have h := coord_sq_le x k
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (x k), norm_nonneg x]

lemma fieldFirst_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldFirst u k ≤ 0 := by
  induction k using Fin.cases with
  | zero => simp only [fieldFirst, Fin.cases_zero]; linarith [dphi_nonneg (u 0)]
  | succ i => simp [fieldFirst]

lemma fieldA_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldA u k ≤ 0 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_nonpos _ _

lemma fieldB_nonpos (u : Chain n) (k : Fin (n + 1)) : fieldB u k ≤ 0 := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i => simp only [fieldB, Fin.cases_succ]; exact linkB_nonpos _ _

lemma field_nonpos (u : Chain n) (k : Fin (n + 1)) : field u k ≤ 0 := by
  rw [field_apply]
  linarith [fieldFirst_nonpos u k, fieldA_nonpos u k, fieldB_nonpos u k]

lemma fieldFirst_abs (u : Chain n) (k : Fin (n + 1)) : |fieldFirst u k| ≤ 1 := by
  induction k using Fin.cases with
  | zero =>
    simp only [fieldFirst, Fin.cases_zero, abs_neg, abs_of_nonneg (dphi_nonneg _)]
    exact dphi_le_one _
  | succ i => simp [fieldFirst]

lemma fieldA_abs (u : Chain n) (k : Fin (n + 1)) : |fieldA u k| ≤ 24 := by
  induction k using Fin.lastCases with
  | last => simp [fieldA]
  | cast i => simp only [fieldA, Fin.lastCases_castSucc]; exact linkA_abs _ _

lemma fieldB_abs (u : Chain n) (k : Fin (n + 1)) : |fieldB u k| ≤ 2 := by
  induction k using Fin.cases with
  | zero => simp [fieldB]
  | succ i => simp only [fieldB, Fin.cases_succ]; exact linkB_abs _ _

lemma field_abs (u : Chain n) (k : Fin (n + 1)) : |field u k| ≤ 27 := by
  rw [field_apply]
  calc _ ≤ |fieldFirst u k| + |fieldA u k| + |fieldB u k| := abs_add_three _ _ _
    _ ≤ 27 := by linarith [fieldFirst_abs u k, fieldA_abs u k, fieldB_abs u k]

lemma field_norm_sq (u : Chain n) : ‖field u‖ ^ 2 ≤ 729 * (n + 1) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _k : Fin (n + 1), (729 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have h := field_abs u k
        nlinarith [sq_abs (field u k), abs_nonneg (field u k)]
    _ = 729 * (n + 1) := by simp; ring

lemma dphi_of_two_le_abs {t : ℝ} (h : 2 ≤ |t|) : dphi t = 0 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h; exact dphi_of_two_le h
  · rw [abs_of_neg ht] at h; exact dphi_of_le_neg_two (by linarith)

lemma dpsi_of_two_le_abs {t : ℝ} (h : 2 ≤ |t|) : dpsi t = 0 ∧ dpsi (-t) = 0 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at h
    exact ⟨dpsi_of_ge (by linarith), dpsi_of_le (by linarith)⟩
  · rw [abs_of_neg ht] at h
    exact ⟨dpsi_of_le (by linarith), dpsi_of_ge (by linarith)⟩

lemma field_of_large (u : Chain n) (k : Fin (n + 1)) (hk : 2 ≤ |u k|) : field u k = 0 := by
  have hneg : 2 ≤ |-u k| := by rwa [abs_neg]
  have h0 : fieldFirst u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldFirst, dphi_of_two_le_abs hk]
    | succ i => simp [fieldFirst]
  have hA : fieldA u k = 0 := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i =>
      simp only [fieldA, Fin.lastCases_castSucc, linkA, (dpsi_of_two_le_abs hk).1,
        (dpsi_of_two_le_abs hk).2]
      ring
  have hB : fieldB u k = 0 := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ, linkB, dphi_of_two_le_abs hk, dphi_of_two_le_abs hneg]
      ring
  rw [field_apply, h0, hA, hB]
  ring

lemma inner_field_self (u : Chain n) : -54 * (n + 1) ≤ ⟪field u, u⟫ := by
  have h : ⟪field u, u⟫ = ∑ k, field u k * u k := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [h]
  calc (-54 * (n + 1) : ℝ) = ∑ _k : Fin (n + 1), (-54 : ℝ) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : 2 ≤ |u k|
      · rw [field_of_large u k hk]; norm_num
      · push Not at hk
        have h1 := field_abs u k
        have h2 : |field u k * u k| ≤ 54 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (field u k), abs_nonneg (u k)]
        linarith [neg_abs_le (field u k * u k)]

lemma exists_first_small (u : Chain n) (h : |u (Fin.last n)| < 1) :
    ∃ j : Fin (n + 1), |u j| < 1 ∧ ∀ i : Fin (n + 1), i < j → 1 ≤ |u i| := by
  classical
  let s := Finset.univ.filter (fun j : Fin (n + 1) => |u j| < 1)
  have hs : s.Nonempty := ⟨Fin.last n, by simp [s, h]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
  intro i hi
  by_contra hc
  push Not at hc
  exact absurd (s.min'_le i (by simp [s, hc])) (not_le.mpr hi)

lemma field_large_coordinate (u : Chain n) (h : |u (Fin.last n)| < 1) :
    ∃ k : Fin (n + 1), field u k ≤ -1 := by
  obtain ⟨j, hj, hmin⟩ := exists_first_small u h
  have habs := hj
  rw [abs_lt] at habs
  refine ⟨j, ?_⟩
  induction j using Fin.cases with
  | zero =>
    rw [field_apply]
    have h0 : fieldFirst u 0 = -dphi (u 0) := by simp [fieldFirst]
    have hB : fieldB u 0 = 0 := by simp [fieldB]
    rw [h0, hB, dphi_of_abs_le hj.le]
    linarith [fieldA_nonpos u 0]
  | succ i =>
    have hprev := hmin i.castSucc Fin.castSucc_lt_succ
    rw [field_apply]
    have h0 : fieldFirst u i.succ = 0 := by simp [fieldFirst]
    have hB : fieldB u i.succ = linkB (u i.castSucc) (u i.succ) := by simp [fieldB]
    rw [h0, hB]
    have hd1 : dphi (u i.succ) = 1 := dphi_of_abs_le hj.le
    have hd2 : dphi (-u i.succ) = 1 := dphi_of_abs_le (by rw [abs_neg]; exact hj.le)
    have hl : linkB (u i.castSucc) (u i.succ) ≤ -1 := by
      unfold linkB
      rw [hd1, hd2]
      rcases le_or_gt 0 (u i.castSucc) with hp | hp
      · rw [abs_of_nonneg hp] at hprev
        rw [psi_of_ge hprev]
        linarith [psi_nonneg (-u i.castSucc)]
      · rw [abs_of_neg hp] at hprev
        rw [psi_of_ge (by linarith : (1 : ℝ) ≤ -u i.castSucc)]
        linarith [psi_nonneg (u i.castSucc)]
    linarith [fieldA_nonpos u i.succ]

lemma chain_ge (u : Chain n) : -3 * (n + 1) ≤ chain u := by
  unfold chain
  have h1 := phi_le (u 0)
  have h2 : ∑ i : Fin n, (-3 : ℝ) ≤ ∑ i : Fin n, link (u i.castSucc) (u i.succ) :=
    Finset.sum_le_sum (fun i _ => link_ge _ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  linarith

lemma chain_le (u : Chain n) : chain u ≤ 3 * (n + 1) := by
  unfold chain
  have h1 := phi_nonneg (u 0)
  have h2 : ∑ i : Fin n, link (u i.castSucc) (u i.succ) ≤ ∑ i : Fin n, (3 : ℝ) :=
    Finset.sum_le_sum (fun i _ => link_le _ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  linarith

lemma chain_gap (u : Chain n) (m : ℕ)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) : -3 * (m + 1) ≤ chain u := by
  classical
  unfold chain
  have h1 := phi_le (u 0)
  have hterm (i : Fin n) : (if i.val < m then (-3 : ℝ) else 0) ≤ link (u i.castSucc) (u i.succ) := by
    split_ifs with hi
    · exact link_ge _ _
    · rw [link_of_small _ (hs i.castSucc (by simp only [Fin.val_castSucc]; omega))]
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hcard : ((Finset.univ.filter (fun i : Fin n => i.val < m)).card : ℝ) ≤ m := by
    have : (Finset.univ.filter (fun i : Fin n => i.val < m)).card ≤ m := by
      calc _ ≤ (Finset.range m).card := by
            apply Finset.card_le_card_of_injOn (fun i => i.val)
            · intro i hi
              simpa using (Finset.mem_filter.mp hi).2
            · intro a _ b _ hab
              exact Fin.ext hab
        _ = m := Finset.card_range m
    exact_mod_cast this
  rw [← Finset.sum_filter] at h2
  simp only [Finset.sum_const, nsmul_eq_mul] at h2
  nlinarith

noncomputable def twoPoint : Chain n := WithLp.toLp 2 (fun _ => (2 : ℝ))

lemma chain_twoPoint : chain (twoPoint (n := n)) = -3 * (n + 1) := by
  simp only [chain, twoPoint, link, phi_of_two_le (le_refl (2 : ℝ)),
    psi_of_ge (by norm_num : (1 : ℝ) ≤ 2), psi_of_le (by norm_num : (-2 : ℝ) ≤ 1 / 2)]
  simp
  ring

lemma twoPoint_norm_sq : ‖(twoPoint (n := n))‖ ^ 2 = 4 * (n + 1) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [twoPoint]
  ring

lemma chain_zero : chain (0 : Chain n) = -3 / 2 := by
  simp only [chain, PiLp.zero_apply, link, neg_zero, psi_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    phi_zero]
  simp
  norm_num

end LongTails.Proofs.AbcChainProperties
