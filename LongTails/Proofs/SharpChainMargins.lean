import LongTails.Proofs.SharpChainInstance

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SharpChainMargins

open MintyChainGeometry SharpChainGeometry SharpChainInstance

variable {d k : ℕ}

set_option hygiene false in
local notation "E" => EuclideanSpace ℝ (Fin d)

section Tail

variable (μ0 D : ℝ)

lemma tail_range (hμ0 : μ0 ^ 2 < 1) :
    ∀ n, n ≤ k → ∑ j ∈ Finset.range (k + 1),
      (if k - n ≤ j then tgtN μ0 D k j ^ 2 else 0) = gap μ0 D (k - n) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [tgtN]
    · intro j hj
      rw [ite_eq_right (by simp at hj; omega)]
  | succ n ih =>
    intro hn
    have hm : k - (n + 1) + 1 = k - n := by omega
    have hsplit : ∀ j, (if k - (n + 1) ≤ j then tgtN μ0 D k j ^ 2 else 0) =
        (if k - n ≤ j then tgtN μ0 D k j ^ 2 else 0) +
          (if j = k - (n + 1) then tgtN μ0 D k j ^ 2 else 0) := by
      intro j
      by_cases h1 : j = k - (n + 1)
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h1, zero_add]
      · by_cases h2 : k - n ≤ j
        · rw [ite_eq_left (by omega), ite_eq_left h2, ite_eq_right h1, add_zero]
        · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h1, add_zero]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ih (by omega), Finset.sum_ite_eq' (Finset.range (k + 1))]
    rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
    have ht : tgtN μ0 D k (k - (n + 1)) = -(μ0 * gap μ0 D (k - (n + 1))) := by
      unfold tgtN
      rw [ite_eq_left (by omega)]
    rw [ht, ← hm, gap_succ_sq μ0 D hμ0]
    ring

lemma tail_sum (hμ0 : μ0 ^ 2 < 1) (m : ℕ) (hm : m ≤ k) :
    ∑ j : Fin (k + 1), (if m ≤ j.val then tgt μ0 D j ^ 2 else 0) = gap μ0 D m ^ 2 := by
  have h := tail_range (k := k) μ0 D hμ0 (k - m) (by omega)
  rw [Nat.sub_sub_self hm] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  rfl

lemma tgt_norm_sq (hμ0 : μ0 ^ 2 < 1) :
    ∑ j : Fin (k + 1), tgt μ0 D j ^ 2 = D ^ 2 := by
  have h := tail_sum (k := k) μ0 D hμ0 0 (Nat.zero_le _)
  simp only [Nat.zero_le, ↓reduceIte] at h
  rw [h, gap_sq μ0 D hμ0, pow_zero, mul_one]

end Tail

section Zero

variable (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d)

noncomputable def tailPart (t : ℕ) (u : E) : Fin (k + 1) → ℝ :=
  fun j => if t ≤ j.val then u (π j) else 0

noncomputable def zeroTail (t : ℕ) (u : E) : E := u - lift π (tailPart π t u)

lemma zeroTail_apply (t : ℕ) (u : E) (j : Fin (k + 1)) :
    zeroTail π t u (π j) = if t ≤ j.val then 0 else u (π j) := by
  unfold zeroTail
  rw [PiLp.sub_apply, lift_apply]
  unfold tailPart
  split_ifs <;> ring

lemma dev_zeroTail (t : ℕ) (u : E) (j : Fin (k + 1)) :
    dev μ0 D π (zeroTail π t u) j = if t ≤ j.val then -tgt μ0 D j else dev μ0 D π u j := by
  unfold dev
  rw [zeroTail_apply]
  split_ifs <;> ring

lemma zeroTail_dist_sq (t : ℕ) (u : E) :
    ‖u - zeroTail π t u‖ ^ 2 = ∑ j : Fin (k + 1), tailPart π t u j ^ 2 := by
  unfold zeroTail
  rw [sub_sub_cancel, norm_lift_sq]

lemma zeroTail_dist (t : ℕ) (u : E) (η : ℝ) (hη : 0 ≤ η)
    (hs : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ η) :
    ‖u - zeroTail π t u‖ ≤ (k + 1) * η := by
  have h := zeroTail_dist_sq π t u
  have hb : ∑ j : Fin (k + 1), tailPart π t u j ^ 2 ≤ ((k : ℝ) + 1) * η ^ 2 := by
    calc ∑ j : Fin (k + 1), tailPart π t u j ^ 2 ≤ ∑ _j : Fin (k + 1), η ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          unfold tailPart
          split_ifs with hj
          · rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hs j hj) 2
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            positivity
      _ = ((k : ℝ) + 1) * η ^ 2 := by simp
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hsq : ‖u - zeroTail π t u‖ ^ 2 ≤ ((k + 1) * η) ^ 2 := by
    rw [h]
    refine hb.trans ?_
    rw [mul_pow]
    nlinarith [sq_nonneg η]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

lemma dev_norm_sq (u : E) : ‖lift π (dev μ0 D π u)‖ ^ 2 = ∑ j, dev μ0 D π u j ^ 2 :=
  norm_lift_sq π _

lemma chainRoot_zeroTail (hμ0 : μ0 ^ 2 < 1) (t : ℕ) (u : E) (m : Fin (k + 1)) (hm : t ≤ m.val) :
    chainRoot μ0 D π m (zeroTail π t u) = ‖lift π (dev μ0 D π (zeroTail π t u))‖ := by
  unfold chainRoot
  rw [← Real.sqrt_sq (norm_nonneg (lift π (dev μ0 D π (zeroTail π t u))))]
  congr 1
  rw [norm_lift_sq, norm_lift_sq, ← tail_sum (k := k) μ0 D hμ0 m.val (by omega), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mask]
  by_cases hj : j.val < m.val
  · rw [ite_eq_left hj, ite_eq_right (by omega)]
    ring
  · rw [ite_eq_right hj, ite_eq_left (by omega), dev_zeroTail, ite_eq_left (by omega)]
    ring

lemma chainVal_zeroTail (hμ0 : μ0 ^ 2 < 1) (t : ℕ) (u : E) (m : Fin (k + 1)) (hm : t ≤ m.val) :
    chainVal μ0 D π m (zeroTail π t u) =
      μ0 * ‖lift π (dev μ0 D π (zeroTail π t u))‖ - offset μ0 D k m.val := by
  unfold chainVal
  rw [chainRoot_zeroTail μ0 D π hμ0 t u m hm, zeroTail_apply, ite_eq_left hm]
  ring

lemma dev_zeroTail_lower (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) (t : ℕ) (ht : t ≤ k) (u : E) :
    gap μ0 D t ≤ ‖lift π (dev μ0 D π (zeroTail π t u))‖ := by
  have hsq : gap μ0 D t ^ 2 ≤ ‖lift π (dev μ0 D π (zeroTail π t u))‖ ^ 2 := by
    rw [norm_lift_sq, ← tail_sum μ0 D hμ0 t ht]
    apply Finset.sum_le_sum
    intro j _
    rw [dev_zeroTail]
    split_ifs
    · rw [neg_sq]
    · positivity
  exact (pow_le_pow_iff_left₀ (gap_pos μ0 D hμ0 hD t).le (norm_nonneg _) two_ne_zero).mp hsq

end Zero

section Margins

variable (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d)

lemma chainVal_lip (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (m : Fin (k + 1)) (u v : E) :
    |chainVal μ0 D π m u - chainVal μ0 D π m v| ≤ 3 / 2 * ‖u - v‖ := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  have hg : ∀ x, ‖chainGrad μ0 D π m x‖ ≤ 3 / 2 :=
    fun x => (chainGrad_norm μ0 D π hμ hμ0 hD m x).trans (by linarith)
  have h1 := lipschitz_of_subgradient (chainVal μ0 D π m) (chainGrad μ0 D π m) (3 / 2)
    (chain_subgradient μ0 D π hμ hμ0 hD m) hg v u
  have h2 := lipschitz_of_subgradient (chainVal μ0 D π m) (chainGrad μ0 D π m) (3 / 2)
    (chain_subgradient μ0 D π hμ hμ0 hD m) hg u v
  rw [norm_sub_rev v u] at h2
  rw [abs_le]
  constructor <;> linarith

lemma radialVal_lip (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (u v : E) :
    |radialVal μ0 D π u - radialVal μ0 D π v| ≤ 3 / 2 * ‖u - v‖ := by
  have hg : ∀ x, ‖radialGrad μ0 D π x‖ ≤ 3 / 2 :=
    fun x => (radialGrad_norm μ0 D π hμ x).trans (by linarith)
  have h1 := lipschitz_of_subgradient (radialVal μ0 D π) (radialGrad μ0 D π) (3 / 2)
    (radial_subgradient μ0 D π hμ) hg v u
  have h2 := lipschitz_of_subgradient (radialVal μ0 D π) (radialGrad μ0 D π) (3 / 2)
    (radial_subgradient μ0 D π hμ) hg u v
  rw [norm_sub_rev v u] at h2
  rw [abs_le]
  constructor <;> linarith

noncomputable def threshold (μ0 D : ℝ) (k : ℕ) : ℝ := μ0 * gap μ0 D k / (32 * ((k : ℝ) + 1) ^ 2)

lemma near_margin (hμ : 0 < μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (t : ℕ) (ht : t ≤ k) (u : E)
    (hs : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ threshold μ0 D k) :
    (∀ m : Fin (k + 1), t < m.val → chainVal μ0 D π m u < (bestUpTo μ0 D π u t).1) ∧
      radialVal μ0 D π u < (bestUpTo μ0 D π u t).1 := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hgk := gap_pos μ0 D hμ0 hD k
  have hγpos : 0 < μ0 * gap μ0 D k / (4 * ((k : ℝ) + 1)) := by positivity
  have hδ : ‖u - zeroTail π t u‖ ≤ μ0 * gap μ0 D k / (4 * ((k : ℝ) + 1)) / 8 := by
    have h := zeroTail_dist π t u (threshold μ0 D k) (by unfold threshold; positivity) hs
    refine h.trans (le_of_eq ?_)
    unfold threshold
    field_simp
    ring
  have htk : t < k + 1 := by omega
  obtain ⟨-, -, -, hmax⟩ := best_spec μ0 D π u t ht
  have hbest : chainVal μ0 D π ⟨t, htk⟩ u ≤ (bestUpTo μ0 D π u t).1 := hmax ⟨t, htk⟩ le_rfl
  have h0 := chainVal_lip μ0 D π hμ.le hμ1 hD ⟨t, htk⟩ u (zeroTail π t u)
  have hw0 := chainVal_zeroTail μ0 D π hμ0 t u ⟨t, htk⟩ le_rfl
  dsimp only at hw0
  have hμg : 0 < μ0 * gap μ0 D k := mul_pos hμ hgk
  have hN := dev_zeroTail_lower μ0 D π hμ0 hD t ht u
  have hgt : gap μ0 D k ≤ gap μ0 D t := gap_anti μ0 D hμ0 hD ht
  have hNk : μ0 * gap μ0 D k ≤ μ0 * ‖lift π (dev μ0 D π (zeroTail π t u))‖ :=
    mul_le_mul_of_nonneg_left (hgt.trans hN) hμ.le
  rw [abs_le] at h0
  refine ⟨?_, ?_⟩
  · intro m hm
    have h1 := chainVal_lip μ0 D π hμ.le hμ1 hD m u (zeroTail π t u)
    have hw1 := chainVal_zeroTail μ0 D π hμ0 t u m hm.le
    have hoff : offset μ0 D k t + μ0 * gap μ0 D k / (4 * ((k : ℝ) + 1)) ≤ offset μ0 D k m.val := by
      unfold offset
      have : (t : ℝ) + 1 ≤ m.val := by exact_mod_cast hm
      nlinarith
    rw [abs_le] at h1
    linarith
  · have h1 := radialVal_lip μ0 D π hμ.le hμ1 u (zeroTail π t u)
    have hoff : offset μ0 D k t ≤ μ0 * gap μ0 D k / 4 - μ0 * gap μ0 D k / (4 * ((k : ℝ) + 1)) := by
      unfold offset
      have hm0 : (t : ℝ) ≤ k := by exact_mod_cast ht
      have e : μ0 * gap μ0 D k / (4 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) = μ0 * gap μ0 D k / 4 := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hm0 hγpos.le]
    unfold radialVal at h1 ⊢
    rw [abs_le] at h1
    linarith

lemma chainVal_at_zero (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (m : Fin (k + 1)) :
    chainVal μ0 D π m 0 ≤ μ0 * D := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  unfold chainVal chainRoot
  have hr : ‖lift π (mask m.val (dev μ0 D π 0))‖ ^ 2 + gap μ0 D m.val ^ 2 = D ^ 2 := by
    rw [norm_lift_sq, ← tail_sum (k := k) μ0 D hμ0 m.val (by omega), ← tgt_norm_sq (k := k) μ0 D hμ0,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mask, dev, PiLp.zero_apply, zero_sub]
    split_ifs <;> first | omega | ring
  rw [hr, Real.sqrt_sq hD.le]
  simp only [PiLp.zero_apply, add_zero]
  have : 0 ≤ offset μ0 D k m.val := by
    unfold offset
    have := gap_pos μ0 D hμ0 hD k
    positivity
  linarith

lemma radialVal_at_zero (hμ0 : μ0 ^ 2 < 1) :
    radialVal μ0 D π 0 = μ0 / 2 * |D| := by
  unfold radialVal
  have h : ‖lift π (dev μ0 D π 0)‖ ^ 2 = D ^ 2 := by
    rw [norm_lift_sq, ← tgt_norm_sq (k := k) μ0 D hμ0]
    apply Finset.sum_congr rfl
    intro j _
    simp [dev]
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

lemma far_dominates (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (u : E) (hu : 8 * D < ‖u‖) :
    (∀ m : Fin (k + 1), chainVal μ0 D π m u < coneVal D u) ∧ radialVal μ0 D π u < coneVal D u := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  unfold coneVal
  refine ⟨fun m => ?_, ?_⟩
  · have h1 := chainVal_lip μ0 D π hμ hμ1 hD m u 0
    have h2 := chainVal_at_zero μ0 D π hμ hμ1 hD m
    rw [sub_zero, abs_le] at h1
    nlinarith
  · have h1 := radialVal_lip μ0 D π hμ hμ1 u 0
    have h2 := radialVal_at_zero μ0 D π hμ0
    rw [abs_of_pos hD] at h2
    rw [sub_zero, abs_le] at h1
    nlinarith

theorem answer_eq_partial (hμ : 0 < μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (t : ℕ) (ht : t ≤ k)
    (u : E) (hs : ‖u‖ ≤ 8 * D → ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ threshold μ0 D k) :
    answer μ0 D π u = partialAnswer μ0 D π t u := by
  by_cases hf : 8 * D < ‖u‖
  · obtain ⟨hc, hr⟩ := far_dominates μ0 D π hμ.le hμ1 hD u hf
    obtain ⟨m, -, he, -⟩ := best_spec μ0 D π u k le_rfl
    obtain ⟨m', -, he', -⟩ := best_spec μ0 D π u t ht
    have hk : (bestUpTo μ0 D π u k).1 < coneVal D u := by rw [he]; exact hc m
    have htt : (bestUpTo μ0 D π u t).1 ≤ coneVal D u := by rw [he']; exact (hc m').le
    unfold answer partialAnswer
    rw [ite_eq_left (max_le hk.le hr.le), ite_eq_left htt]
  · obtain ⟨hc, hr⟩ := near_margin μ0 D π hμ hμ1 hD t ht u (hs (not_lt.mp hf))
    have hst := best_stable μ0 D π u t ht hc
    unfold answer partialAnswer
    rw [hst, max_eq_left hr.le]
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact absurd hr.le h2

end Margins

end LongTails.Proofs.SharpChainMargins
