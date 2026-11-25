import LongTails.Proofs.NcPlFlat

open scoped BigOperators

namespace LongTails.Proofs.NcPlTrunc

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL LongTails.Proofs.NcPlSchedule
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat

noncomputable def tr (s : ℕ) (c : ℕ → ℝ) (p : ℕ) : ℝ := if p < s then c p else 0

lemma tr_lt {s p : ℕ} (c : ℕ → ℝ) (h : p < s) : tr s c p = c p := by
  unfold tr
  rw [ite_eq_left h]

lemma tr_ge {s p : ℕ} (c : ℕ → ℝ) (h : s ≤ p) : tr s c p = 0 := by
  unfold tr
  rw [ite_eq_right (by omega)]

lemma tr_abs_le (s : ℕ) (c : ℕ → ℝ) (p : ℕ) : |tr s c p| ≤ |c p| := by
  unfold tr
  split_ifs
  · exact le_rfl
  · rw [abs_zero]
    exact abs_nonneg _

section BlockData

variable {n : ℕ} {r : ℕ → ℝ}

lemma rw_ext {y y' : ℕ → ℝ} (h : ∀ j, j ≤ n → y j = y' j) (s t : ℝ) :
    rwd n r s t y = rwd n r s t y' ∧ rwDs n r s t y = rwDs n r s t y' ∧
      rwDt n r s t y = rwDt n r s t y' ∧
      ∀ k, k ≤ n → rwGrad n r s t y k = rwGrad n r s t y' k := by
  have hg : ∀ k, k ≤ n → gprev r y k = gprev r y' k := fun k hk => gprev_congr h hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold rwd rewardVal
    rw [h n le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hg j hjn, h j hjn]
  · unfold rwDs
    rw [h n le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hg j hjn, h j hjn]
  · unfold rwDt
    rw [h n le_rfl]
  · intro k hk
    unfold rwGrad rewardGrad cval
    rw [hg k hk, h k hk]
    by_cases hkn : k < n
    · rw [ite_eq_left hkn, ite_eq_left hkn, h (k + 1) (by omega)]
    · rw [ite_eq_right hkn, ite_eq_right hkn]

lemma data_zero {v : ℝ} (hv : v ≤ 1 / 2) (t : ℝ) (y : ℕ → ℝ) :
    blockU n r v t y = 0 ∧ (∀ k, rwGrad n r (sig n v) t y k = 0) ∧ blockDt n r v t y = 0 ∧
      blockDv n r v t y = 0 ∧ compU n v = 0 ∧ compDv n v = 0 := by
  have hs : sig n v = 0 := sig_of_le hv
  have hd : dsig n v = 0 := dsig_of_le hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold blockU
    rw [hs]
    exact rw_of_nonpos le_rfl t y
  · intro k
    rw [hs]
    exact rwGrad_of_nonpos le_rfl t y k
  · unfold blockDt
    rw [hs]
    exact rwDt_of_nonpos le_rfl t y
  · unfold blockDv
    rw [hd, mul_zero]
  · unfold compU
    rw [hs]
    exact comp_of_le le_rfl
  · unfold compDv
    rw [hd, mul_zero]

lemma data_congr {y y' : ℕ → ℝ} {J : ℕ} (hJ : J ≤ n) (hr : ∀ j, j ≤ n → 0 < r j)
    (hag : ∀ j, j ≤ J → y j = y' j) (hy : ∀ j, J ≤ j → j ≤ n → y j ≤ r j)
    (hy' : ∀ j, J ≤ j → j ≤ n → y' j ≤ r j) (v t t' : ℝ) :
    blockU n r v t y = blockU n r v t' y' ∧
      (∀ k, k ≤ n → rwGrad n r (sig n v) t y k = rwGrad n r (sig n v) t' y' k) ∧
      blockDt n r v t y = 0 ∧ blockDt n r v t' y' = 0 ∧
      blockDv n r v t y = blockDv n r v t' y' ∧
      (∀ k, J < k → k ≤ n → rwGrad n r (sig n v) t y k = 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rw_congr hJ hr hag hy hy' (sig n v) t t'
  refine ⟨h1, h5, h3, h4, ?_, h6⟩
  unfold blockDv
  rw [h2]

lemma block_cases (i s : ℕ) : i * (n + 2) + n + 1 ≤ s ∨ s < i * (n + 2) ∨
    (i * (n + 2) ≤ s ∧ s < i * (n + 2) + n + 1) := by
  generalize i * (n + 2) = P
  omega

lemma prev_tr (a : ℕ → ℝ) {i s : ℕ} (h : i * (n + 2) ≤ s) :
    prevRead (uOf n (tr (s + 1) a)) i = prevRead (uOf n a) i := by
  cases i with
  | zero => rw [prevRead_zero, prevRead_zero]
  | succ i' =>
    rw [prevRead_succ, prevRead_succ]
    unfold uOf
    have e := Nat.add_one_mul i' (n + 2)
    apply tr_lt
    generalize i' * (n + 2) = P at *
    generalize (i' + 1) * (n + 2) = Q at *
    omega

theorem block_trunc {ρ θ : ℝ} (hθρ : θ ≤ ρ) (hρ0 : 0 < ρ) (hr : ∀ j, j ≤ n → ρ ≤ r j)
    (a b : ℕ → ℝ) (s : ℕ) (ha : ∀ p, s ≤ p → |a p| ≤ 1 / 2) (hb : ∀ p, s ≤ p → |b p| ≤ θ)
    (i : ℕ) :
    blockU n r (prevRead (uOf n (tr (s + 1) a)) i) (uOf n (tr (s + 1) a) i)
        (wOf n (tr (s + 1) b) i) =
      blockU n r (prevRead (uOf n a) i) (uOf n a i) (wOf n b i) ∧
    (∀ j, j ≤ n → gW n r (uOf n (tr (s + 1) a)) (wOf n (tr (s + 1) b)) i j =
      gW n r (uOf n a) (wOf n b) i j) ∧
    blockDt n r (prevRead (uOf n (tr (s + 1) a)) i) (uOf n (tr (s + 1) a) i)
        (wOf n (tr (s + 1) b) i) =
      blockDt n r (prevRead (uOf n a) i) (uOf n a i) (wOf n b i) ∧
    blockDv n r (prevRead (uOf n (tr (s + 1) a)) i) (uOf n (tr (s + 1) a) i)
        (wOf n (tr (s + 1) b) i) =
      blockDv n r (prevRead (uOf n a) i) (uOf n a i) (wOf n b i) ∧
    compU n (prevRead (uOf n (tr (s + 1) a)) i) = compU n (prevRead (uOf n a) i) ∧
    compDv n (prevRead (uOf n (tr (s + 1) a)) i) = compDv n (prevRead (uOf n a) i) ∧
    (∀ j, j ≤ n → s < i * (n + 2) + j → gW n r (uOf n a) (wOf n b) i j = 0) ∧
    (s < i * (n + 2) + (n + 1) →
      blockDt n r (prevRead (uOf n a) i) (uOf n a i) (wOf n b i) = 0) := by
  rcases block_cases (n := n) i s with h | h | ⟨h1, h2⟩
  · have hv := prev_tr (n := n) a (i := i) (s := s) (by omega)
    have ht : uOf n (tr (s + 1) a) i = uOf n a i := by
      unfold uOf
      exact tr_lt a (by omega)
    have hw : ∀ j, j ≤ n → wOf n (tr (s + 1) b) i j = wOf n b i j := fun j hj => by
      unfold wOf
      exact tr_lt b (by omega)
    obtain ⟨e1, e2, e3, e4⟩ := rw_ext (r := r) hw (sig n (prevRead (uOf n a) i)) (uOf n a i)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold blockU
      rw [hv, ht]
      exact e1
    · intro j hj
      unfold gW
      rw [hv, ht]
      exact e4 j hj
    · unfold blockDt
      rw [hv, ht]
      exact e3
    · unfold blockDv
      rw [hv, ht, e2]
    · rw [hv]
    · rw [hv]
    · intro j hj hlt
      exact absurd hlt (by omega)
    · intro hlt
      exact absurd hlt (by omega)
  · cases i with
    | zero =>
      rw [Nat.zero_mul] at h
      exact absurd h (Nat.not_lt_zero _)
    | succ i' =>
      have e := Nat.add_one_mul i' (n + 2)
      have hpos : s ≤ i' * (n + 2) + (n + 1) := by
        generalize i' * (n + 2) = P at *
        generalize (i' + 1) * (n + 2) = Q at *
        omega
      have hv1 : prevRead (uOf n a) (i' + 1) ≤ 1 / 2 := by
        rw [prevRead_succ]
        unfold uOf
        exact (le_abs_self _).trans (ha _ hpos)
      have hv2 : prevRead (uOf n (tr (s + 1) a)) (i' + 1) ≤ 1 / 2 := by
        rw [prevRead_succ]
        unfold uOf
        exact (le_abs_self _).trans ((tr_abs_le _ _ _).trans (ha _ hpos))
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := data_zero (r := r) hv1 (uOf n a (i' + 1))
        (wOf n b (i' + 1))
      obtain ⟨y1, y2, y3, y4, y5, y6⟩ := data_zero (r := r) hv2 (uOf n (tr (s + 1) a) (i' + 1))
        (wOf n (tr (s + 1) b) (i' + 1))
      refine ⟨by rw [z1, y1], fun j _ => ?_, by rw [z3, y3], by rw [z4, y4], by rw [z5, y5],
        by rw [z6, y6], fun j _ _ => ?_, fun _ => z3⟩
      · unfold gW
        rw [z2 j, y2 j]
      · unfold gW
        exact z2 j
  · have hv := prev_tr (n := n) a (i := i) (s := s) h1
    obtain ⟨J, hJ⟩ : ∃ J, s = i * (n + 2) + J := ⟨s - i * (n + 2), by omega⟩
    have hJn : J ≤ n := by omega
    have hrpos : ∀ j, j ≤ n → 0 < r j := fun j hj => lt_of_lt_of_le hρ0 (hr j hj)
    have hag : ∀ j, j ≤ J → wOf n b i j = wOf n (tr (s + 1) b) i j := fun j hj => by
      unfold wOf
      exact (tr_lt b (by omega)).symm
    have hy : ∀ j, J ≤ j → j ≤ n → wOf n b i j ≤ r j := fun j hj hjn => by
      unfold wOf
      exact ((le_abs_self _).trans (hb _ (by omega))).trans (hθρ.trans (hr j hjn))
    have hy' : ∀ j, J ≤ j → j ≤ n → wOf n (tr (s + 1) b) i j ≤ r j := fun j hj hjn => by
      unfold wOf
      exact ((le_abs_self _).trans ((tr_abs_le _ _ _).trans (hb _ (by omega)))).trans
        (hθρ.trans (hr j hjn))
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := data_congr hJn hrpos hag hy hy'
      (prevRead (uOf n a) i) (uOf n a i) (uOf n (tr (s + 1) a) i)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => c3⟩
    · rw [hv]
      exact c1.symm
    · intro j hj
      unfold gW
      rw [hv]
      exact (c2 j hj).symm
    · rw [hv, c3, c4]
    · rw [hv]
      exact c5.symm
    · rw [hv]
    · rw [hv]
    · intro j hj hlt
      unfold gW
      exact c6 j (by omega) hj

end BlockData

section Global

variable {m n : ℕ} {r : ℕ → ℝ} {ρ θ : ℝ}

theorem rF_trunc (hθρ : θ ≤ ρ) (hρ0 : 0 < ρ) (hr : ∀ j, j ≤ n → ρ ≤ r j)
    (a b : ℕ → ℝ) (s : ℕ) (ha : ∀ p, s ≤ p → |a p| ≤ 1 / 2) (hb : ∀ p, s ≤ p → |b p| ≤ θ) :
    rF m n r (tr (s + 1) a) (tr (s + 1) b) = rF m n r a b := by
  unfold rF rhat
  apply Finset.sum_congr rfl
  intro i _
  exact (block_trunc hθρ hρ0 hr a b s ha hb i).1

theorem gB_trunc (hθρ : θ ≤ ρ) (hρ0 : 0 < ρ) (hr : ∀ j, j ≤ n → ρ ≤ r j)
    (a b : ℕ → ℝ) (s : ℕ) (ha : ∀ p, s ≤ p → |a p| ≤ 1 / 2) (hb : ∀ p, s ≤ p → |b p| ≤ θ)
    (p : ℕ) :
    (if p < s + 1 then gB n r (tr (s + 1) a) (tr (s + 1) b) p else 0) = gB n r a b p := by
  unfold gB
  by_cases hx : p % (n + 2) = n + 1
  · rw [ite_eq_left hx, ite_eq_left hx, ite_self]
  · rw [ite_eq_right hx, ite_eq_right hx]
    have hj : p % (n + 2) ≤ n := by
      have := Nat.mod_lt p (show 0 < n + 2 by omega)
      omega
    have hpe : p / (n + 2) * (n + 2) + p % (n + 2) = p := Nat.div_add_mod' p (n + 2)
    obtain ⟨_, q2, _, _, _, _, z2, _⟩ := block_trunc hθρ hρ0 hr a b s ha hb (p / (n + 2))
    by_cases hps : p < s + 1
    · rw [ite_eq_left hps]
      exact q2 _ hj
    · rw [ite_eq_right hps]
      exact (z2 _ hj (by omega)).symm

theorem gA_trunc (hθρ : θ ≤ ρ) (hρ0 : 0 < ρ) (hr : ∀ j, j ≤ n → ρ ≤ r j)
    (a b : ℕ → ℝ) (c : ℝ) (s : ℕ) (ha : ∀ p, s ≤ p → |a p| ≤ 1 / 2)
    (hb : ∀ p, s ≤ p → |b p| ≤ θ) (p : ℕ) :
    (if p < s + 1 then gA m n r (tr (s + 1) a) (tr (s + 1) b) c p else 0) = gA m n r a b c p := by
  unfold gA
  by_cases hx : p % (n + 2) = n + 1
  · rw [ite_eq_left hx, ite_eq_left hx]
    have hpe : p / (n + 2) * (n + 2) + (n + 1) = p := by
      have := Nat.div_add_mod' p (n + 2)
      omega
    obtain ⟨_, _, q3, _, _, _, _, z3⟩ := block_trunc hθρ hρ0 hr a b s ha hb (p / (n + 2))
    obtain ⟨_, _, _, q4, _, q6, _, _⟩ := block_trunc hθρ hρ0 hr a b s ha hb (p / (n + 2) + 1)
    rw [prevRead_succ, prevRead_succ] at q4 q6
    by_cases hps : p < s + 1
    · rw [ite_eq_left hps]
      unfold gAu gUR gUC
      rw [q3, q4, q6]
    · rw [ite_eq_right hps]
      have hui : uOf n a (p / (n + 2)) ≤ 1 / 2 := by
        unfold uOf
        rw [hpe]
        exact (le_abs_self _).trans (ha p (by omega))
      obtain ⟨_, _, _, d4, _, d6⟩ := data_zero (r := r) hui (uOf n a (p / (n + 2) + 1))
        (wOf n b (p / (n + 2) + 1))
      unfold gAu gUR gUC
      rw [z3 (by omega), d4, d6]
      simp only [ite_self, add_zero, mul_zero, sub_zero]
  · rw [ite_eq_right hx, ite_eq_right hx, ite_self]

lemma tr_full {K : ℕ} (c : ℕ → ℝ) (hc : ∀ p, K ≤ p → c p = 0) : tr K c = c := by
  funext p
  unfold tr
  by_cases hp : p < K
  · rw [ite_eq_left hp]
  · rw [ite_eq_right hp, hc p (by omega)]

lemma uOf_tr_succ (a : ℕ → ℝ) {s : ℕ} (hs : s % (n + 2) ≠ n + 1) :
    uOf n (tr (s + 1) a) = uOf n (tr s a) := by
  funext i
  unfold uOf tr
  have hne : i * (n + 2) + (n + 1) ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact pos_mod n i (Nat.lt_succ_self _)
  by_cases hlt : i * (n + 2) + (n + 1) < s
  · rw [ite_eq_left hlt, ite_eq_left (by omega)]
  · rw [ite_eq_right hlt, ite_eq_right (by omega)]

lemma tr_succ_sub (b : ℕ → ℝ) (s K : ℕ) :
    ∑ p ∈ Finset.range K, (tr (s + 1) b p - tr s b p) ^ 2 ≤ b s ^ 2 := by
  have e : ∀ p ∈ Finset.range K, (tr (s + 1) b p - tr s b p) ^ 2 =
      if p = s then b s ^ 2 else 0 := by
    intro p _
    unfold tr
    by_cases hp : p = s
    · rw [hp, ite_eq_left (Nat.lt_succ_self s), ite_eq_right (lt_irrefl s), ite_eq_left rfl,
        sub_zero]
    · rw [ite_eq_right hp]
      by_cases hlt : p < s
      · rw [ite_eq_left hlt, ite_eq_left (by omega), sub_self]
        norm_num
      · rw [ite_eq_right hlt, ite_eq_right (by omega), sub_self]
        norm_num
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

lemma wt_bulk {k : ℕ} (hk : 2 * k ≤ n) : wt (n + 1) k = 1 / ((n : ℝ) + 1) := by
  unfold wt
  push_cast
  apply max_eq_left
  have h1 : (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n + 1)
    exact_mod_cast this.le
  have h2 : (2 : ℝ) ^ (n + 1) ≤ (4 : ℝ) ^ (n + 1 - k) := by
    have e : (4 : ℝ) ^ (n + 1 - k) = (2 : ℝ) ^ (2 * (n + 1 - k)) := by
      rw [pow_mul]
      norm_num
    rw [e]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have e3 : (1 / 4 : ℝ) ^ (n + 1 - k) = 1 / (4 : ℝ) ^ (n + 1 - k) := by
    rw [one_div, inv_pow, one_div]
  rw [e3]
  exact one_div_le_one_div_of_le (by positivity) (h1.trans h2)

end Global

end LongTails.Proofs.NcPlTrunc
