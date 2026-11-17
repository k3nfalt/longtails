import LongTails.Proofs.AbcChainProperties

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcChainMask

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.AbcChain
open LongTails.Proofs.AbcChainProperties

variable {n : ℕ}

lemma sum_fieldFirst_sq (u v : Chain n) :
    ∑ k, (fieldFirst u k - fieldFirst v k) ^ 2 = (dphi (u 0) - dphi (v 0)) ^ 2 := by
  rw [Fin.sum_univ_succ]; simp [fieldFirst]; ring

lemma sum_fieldA_sq (u v : Chain n) :
    ∑ k, (fieldA u k - fieldA v k) ^ 2 = ∑ i : Fin n,
      (linkA (u i.castSucc) (u i.succ) - linkA (v i.castSucc) (v i.succ)) ^ 2 := by
  rw [Fin.sum_univ_castSucc]; simp [fieldA]

lemma sum_fieldB_sq (u v : Chain n) :
    ∑ k, (fieldB u k - fieldB v k) ^ 2 = ∑ i : Fin n,
      (linkB (u i.castSucc) (u i.succ) - linkB (v i.castSucc) (v i.succ)) ^ 2 := by
  rw [Fin.sum_univ_succ]; simp [fieldB]

lemma sq_two_le (x y y' a b : ℝ) (h : |x| ≤ a * |y| + b * |y'|) :
    x ^ 2 ≤ 2 * a ^ 2 * y ^ 2 + 2 * b ^ 2 * y' ^ 2 := by
  have h0 := abs_nonneg x
  have hy := abs_nonneg y
  have hy' := abs_nonneg y'
  have hs : x ^ 2 ≤ (a * |y| + b * |y'|) ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (a * |y| - b * |y'|), sq_abs y, sq_abs y']

lemma field_lipschitz (u v : Chain n) : ‖field u - field v‖ ≤ 1000 * ‖u - v‖ := by
  have hsq : ‖field u - field v‖ ^ 2 ≤ 1000 ^ 2 * ‖u - v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have hc := sum_castSucc_sq_le (fun k => (u - v) k)
    have hu := sum_succ_sq_le (fun k => (u - v) k)
    have hz := zero_sq_le (fun k => (u - v) k)
    simp only [PiLp.sub_apply] at hc hu hz ⊢
    have hpt (k : Fin (n + 1)) : (field u k - field v k) ^ 2 ≤
        3 * ((fieldFirst u k - fieldFirst v k) ^ 2 + (fieldA u k - fieldA v k) ^ 2 +
          (fieldB u k - fieldB v k) ^ 2) := by
      rw [field_apply, field_apply]
      nlinarith [sq_nonneg (fieldFirst u k - fieldFirst v k - (fieldA u k - fieldA v k)),
        sq_nonneg (fieldFirst u k - fieldFirst v k - (fieldB u k - fieldB v k)),
        sq_nonneg (fieldA u k - fieldA v k - (fieldB u k - fieldB v k))]
    have h1 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_fieldFirst_sq,
      sum_fieldA_sq, sum_fieldB_sq] at h1
    have h0 : (dphi (u 0) - dphi (v 0)) ^ 2 ≤ 16 * (u 0 - v 0) ^ 2 := by
      have h := dphi_lipschitz (u 0) (v 0)
      nlinarith [sq_abs (dphi (u 0) - dphi (v 0)), sq_abs (u 0 - v 0),
        abs_nonneg (dphi (u 0) - dphi (v 0)), abs_nonneg (u 0 - v 0)]
    have hA : ∑ i : Fin n, (linkA (u i.castSucc) (u i.succ) - linkA (v i.castSucc) (v i.succ)) ^ 2
        ≤ ∑ i : Fin n, (2 * 384 ^ 2 * (u i.castSucc - v i.castSucc) ^ 2 +
          2 * 8 ^ 2 * (u i.succ - v i.succ) ^ 2) :=
      Finset.sum_le_sum (fun i _ => sq_two_le _ _ _ _ _ (linkA_lipschitz _ _ _ _))
    have hB : ∑ i : Fin n, (linkB (u i.castSucc) (u i.succ) - linkB (v i.castSucc) (v i.succ)) ^ 2
        ≤ ∑ i : Fin n, (2 * 8 ^ 2 * (u i.castSucc - v i.castSucc) ^ 2 +
          2 * 8 ^ 2 * (u i.succ - v i.succ) ^ 2) :=
      Finset.sum_le_sum (fun i _ => sq_two_le _ _ _ _ _ (linkB_lipschitz _ _ _ _))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hA hB
    nlinarith
  nlinarith [norm_nonneg (field u - field v), norm_nonneg (u - v)]

noncomputable def trunc (m : ℕ) (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun i => if i.val < m then u i else 0)

noncomputable def knownField (m : ℕ) (u : Chain n) : Chain n :=
  WithLp.toLp 2 (fun k => if k.val + 1 < m ∨ n + 1 ≤ m then field u k else 0)

lemma trunc_apply (m : ℕ) (u : Chain n) (i : Fin (n + 1)) :
    trunc m u i = if i.val < m then u i else 0 := rfl

lemma knownField_apply (m : ℕ) (u : Chain n) (k : Fin (n + 1)) :
    knownField m u k = if k.val + 1 < m ∨ n + 1 ≤ m then field u k else 0 := rfl

lemma field_congr (u v : Chain n) (k : Fin (n + 1))
    (h : ∀ j : Fin (n + 1), j.val ≤ k.val + 1 → u j = v j) : field u k = field v k := by
  rw [field_apply, field_apply]
  have h0 : u 0 = v 0 := h 0 (by simp)
  have hF : fieldFirst u k = fieldFirst v k := by simp only [fieldFirst, h0]
  have hA : fieldA u k = fieldA v k := by
    induction k using Fin.lastCases with
    | last => simp [fieldA]
    | cast i =>
      simp only [fieldA, Fin.lastCases_castSucc]
      rw [h i.castSucc (by simp), h i.succ (by simp)]
  have hB : fieldB u k = fieldB v k := by
    induction k using Fin.cases with
    | zero => simp [fieldB]
    | succ i =>
      simp only [fieldB, Fin.cases_succ]
      rw [h i.castSucc (by simp; omega), h i.succ (by simp)]
  rw [hF, hA, hB]

lemma knownField_trunc (m : ℕ) (u : Chain n) : knownField m (trunc m u) = knownField m u := by
  ext k
  rw [knownField_apply, knownField_apply]
  split_ifs with hk
  · apply field_congr
    intro j hj
    rw [trunc_apply]
    rcases hk with hk | hk
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_left (by omega)]
  · rfl

lemma trunc_congr (m : ℕ) (u v : Chain n) (h : ∀ i : Fin (n + 1), i.val < m → u i = v i) :
    trunc m u = trunc m v := by
  ext i
  rw [trunc_apply, trunc_apply]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma knownField_congr (m : ℕ) (u v : Chain n) (h : ∀ i : Fin (n + 1), i.val < m → u i = v i) :
    knownField m u = knownField m v := by
  rw [← knownField_trunc m u, ← knownField_trunc m v, trunc_congr m u v h]

lemma knownField_full (m : ℕ) (u : Chain n) (hm : n + 1 ≤ m) : knownField m u = field u := by
  ext k
  rw [knownField_apply, ite_eq_left (Or.inr hm)]

lemma trunc_full (m : ℕ) (u : Chain n) (hm : n + 1 ≤ m) : trunc m u = u := by
  ext i
  rw [trunc_apply, ite_eq_left (by omega)]

lemma knownField_norm_le (m : ℕ) (u : Chain n) : ‖knownField m u‖ ≤ ‖field u‖ := by
  have h : ‖knownField m u‖ ^ 2 ≤ ‖field u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro k _
    rw [knownField_apply]
    split_ifs
    · exact le_rfl
    · simp [sq_nonneg]
  nlinarith [norm_nonneg (knownField m u), norm_nonneg (field u)]

lemma trunc_norm_le (m : ℕ) (u : Chain n) : ‖trunc m u‖ ≤ ‖u‖ := by
  have h : ‖trunc m u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro k _
    rw [trunc_apply]
    split_ifs
    · exact le_rfl
    · simp [sq_nonneg]
  nlinarith [norm_nonneg (trunc m u), norm_nonneg u]

lemma indicator_sum_le (n : ℕ) (c : ℝ) (hc : 0 ≤ c) (P : Fin (n + 1) → Prop) [DecidablePred P]
    (hP : ∀ a b, P a → P b → a = b) :
    ∑ k : Fin (n + 1), (if P k then c else 0) ≤ c := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hP a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have : ((Finset.univ.filter P).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  nlinarith

lemma secret_field_bound (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    ‖field u - knownField m u‖ ≤ 28 := by
  classical
  have hpt (k : Fin (n + 1)) : (field u k - knownField m u k) ^ 2 ≤
      (if k.val + 1 = m then (729 : ℝ) else 0) + (if k.val = m then (9 : ℝ) else 0) := by
    rw [knownField_apply]
    by_cases hk : k.val + 1 < m ∨ n + 1 ≤ m
    · rw [ite_eq_left hk, sub_self]
      split_ifs <;> norm_num
    · rw [ite_eq_right hk, sub_zero]
      push Not at hk
      have hab := field_abs u k
      by_cases h1 : k.val + 1 = m
      · rw [ite_eq_left h1]
        have : (field u k) ^ 2 ≤ 729 := by nlinarith [sq_abs (field u k), abs_nonneg (field u k)]
        have h2 : (if k.val = m then (9 : ℝ) else 0) ≥ 0 := by split_ifs <;> norm_num
        linarith
      · rw [ite_eq_right h1]
        have hkm : m ≤ k.val := by omega
        have hsm := hs k hkm
        have hA : fieldA u k = 0 := by
          induction k using Fin.lastCases with
          | last => simp [fieldA]
          | cast i =>
            simp only [fieldA, Fin.lastCases_castSucc]
            exact linkA_of_small _ hsm
        by_cases h2 : k.val = m
        · rw [ite_eq_left h2]
          have hb : |field u k| ≤ 3 := by
            rw [field_apply, hA, add_zero]
            calc _ ≤ |fieldFirst u k| + |fieldB u k| := abs_add_le _ _
              _ ≤ 3 := by linarith [fieldFirst_abs u k, fieldB_abs u k]
          nlinarith [sq_abs (field u k), abs_nonneg (field u k)]
        · rw [ite_eq_right h2]
          have hgt : m + 1 ≤ k.val := by omega
          have hF : fieldFirst u k = 0 := by
            induction k using Fin.cases with
            | zero => simp at hgt
            | succ i => simp [fieldFirst]
          have hB : fieldB u k = 0 := by
            induction k using Fin.cases with
            | zero => simp [fieldB]
            | succ i =>
              simp only [fieldB, Fin.cases_succ]
              exact linkB_of_small _ (hs i.castSucc (by simp at hgt ⊢; omega))
          rw [field_apply, hF, hA, hB]
          norm_num
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
  rw [Finset.sum_add_distrib] at hsum
  have i1 := indicator_sum_le n 729 (by norm_num) (fun k : Fin (n + 1) => k.val + 1 = m)
    (fun a b ha hb => Fin.ext (by omega))
  have i2 := indicator_sum_le n 9 (by norm_num) (fun k : Fin (n + 1) => k.val = m)
    (fun a b ha hb => Fin.ext (by omega))
  have hsq : ‖field u - knownField m u‖ ^ 2 ≤ 28 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply]
    linarith
  nlinarith [norm_nonneg (field u - knownField m u)]

lemma link_trunc_close (a b : ℝ) (hb : |b| ≤ 1 / 4) : |link a b - link a 0| ≤ 1 / 2 := by
  have e : link a b - link a 0 = psi (-a) * (phi (-b) - phi 0) - psi a * (phi b - phi 0) := by
    simp only [link, neg_zero]; ring
  rw [e]
  have h1 := phi_lipschitz (-b) 0
  have h2 := phi_lipschitz b 0
  simp only [sub_zero, abs_neg] at h1 h2
  have k1 : |psi (-a) * (phi (-b) - phi 0)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    nlinarith [psi_le_one (-a), psi_nonneg (-a), abs_nonneg (phi (-b) - phi 0)]
  have k2 : |psi a * (phi b - phi 0)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    nlinarith [psi_le_one a, psi_nonneg a, abs_nonneg (phi b - phi 0)]
  calc _ ≤ |psi (-a) * (phi (-b) - phi 0)| + |psi a * (phi b - phi 0)| := abs_sub_le_sum _ _
    _ ≤ 1 / 2 := by linarith

lemma chain_trunc_close (m : ℕ) (u : Chain n)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |u i| ≤ 1 / 4) :
    |chain u - chain (trunc m u)| ≤ 1 / 2 := by
  classical
  have hlink (i : Fin n) : |link (u i.castSucc) (u i.succ) -
      link (trunc m u i.castSucc) (trunc m u i.succ)| ≤ if i.val + 1 = m then 1 / 2 else 0 := by
    rw [trunc_apply, trunc_apply]
    by_cases h1 : i.val + 1 < m
    · rw [ite_eq_left (by simp; omega), ite_eq_left (by simp; omega), sub_self, abs_zero]
      split_ifs <;> norm_num
    · by_cases h2 : i.val + 1 = m
      · rw [ite_eq_left (by simp; omega), ite_eq_right (by simp; omega), ite_eq_left h2]
        exact link_trunc_close _ _ (hs i.succ (by simp; omega))
      · rw [ite_eq_right h2, ite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
        rw [link_of_small _ (hs i.castSucc (by simp; omega)),
          link_of_small _ (by norm_num : |(0 : ℝ)| ≤ 1 / 4)]
        simp
  have hfirst : |-phi (u 0) - -phi (trunc m u 0)| ≤ if m = 0 then 1 / 4 else 0 := by
    rw [trunc_apply]
    by_cases hm : m = 0
    · rw [ite_eq_left hm, ite_eq_right (by simp [hm])]
      have h := phi_lipschitz (u 0) 0
      have hu := hs 0 (by simp [hm])
      rw [show -phi (u 0) - -phi 0 = -(phi (u 0) - phi 0) by ring, abs_neg]
      simp only [sub_zero] at h
      linarith
    · rw [ite_eq_right hm, ite_eq_left (by simp; omega), sub_self, abs_zero]
  have hsum : |∑ i : Fin n, (link (u i.castSucc) (u i.succ) -
      link (trunc m u i.castSucc) (trunc m u i.succ))| ≤
      ∑ i : Fin n, (if i.val + 1 = m then (1 / 2 : ℝ) else 0) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hlink i))
  have hind : ∑ i : Fin n, (if i.val + 1 = m then (1 / 2 : ℝ) else 0) ≤
      if m = 0 then 0 else 1 / 2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun i : Fin n => i.val + 1 = m)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact Fin.ext (by have := (Finset.mem_filter.mp ha).2; have := (Finset.mem_filter.mp hb).2; omega)
    split_ifs with hm
    · have he : Finset.univ.filter (fun i : Fin n => i.val + 1 = m) = ∅ := by
        ext i; simp [hm]
      rw [he]; simp
    · have : ((Finset.univ.filter (fun i : Fin n => i.val + 1 = m)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      nlinarith
  have e : chain u - chain (trunc m u) = (-phi (u 0) - -phi (trunc m u 0)) +
      ∑ i : Fin n, (link (u i.castSucc) (u i.succ) -
        link (trunc m u i.castSucc) (trunc m u i.succ)) := by
    simp only [chain, Finset.sum_sub_distrib]; ring
  rw [e]
  calc _ ≤ |-phi (u 0) - -phi (trunc m u 0)| + _ := abs_add_le _ _
    _ ≤ 1 / 2 := by split_ifs at hfirst hind <;> linarith

end LongTails.Proofs.AbcChainMask
