import LongTails.Proofs.NcPlChainPL

open scoped BigOperators

namespace LongTails.Proofs.NcPlFlat

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlSchedule LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL

section Reindex

lemma sum_range_mul (H : ℕ → ℝ) (M b : ℕ) :
    ∑ p ∈ Finset.range (M * b), H p =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range b, H (i * b + j) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

variable (n : ℕ)

lemma pos_mod (i : ℕ) {j : ℕ} (hj : j < n + 2) : (i * (n + 2) + j) % (n + 2) = j :=
  Nat.mul_add_mod_of_lt hj

lemma pos_div (i : ℕ) {j : ℕ} (hj : j < n + 2) : (i * (n + 2) + j) / (n + 2) = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt hj,
    Nat.zero_add]

lemma sum_upos (F : ℕ → ℝ) (m : ℕ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (if p % (n + 2) = n + 1 then F p else 0) =
      ∑ i ∈ Finset.range (m + 1), F (i * (n + 2) + (n + 1)) := by
  rw [sum_range_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range_succ, pos_mod n i (Nat.lt_succ_self (n + 1)), ite_eq_left rfl]
  have hz : ∑ j ∈ Finset.range (n + 1),
      (if (i * (n + 2) + j) % (n + 2) = n + 1 then F (i * (n + 2) + j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [pos_mod n i (by omega), ite_eq_right (by omega)]
  rw [hz, zero_add]

lemma sum_wpos (G : ℕ → ℝ) (m : ℕ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (if p % (n + 2) = n + 1 then 0 else G p) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), G (i * (n + 2) + j) := by
  rw [sum_range_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range_succ, pos_mod n i (Nat.lt_succ_self (n + 1)), ite_eq_left rfl, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n + 1 := Finset.mem_range.mp hj
  rw [pos_mod n i (by omega), ite_eq_right (by omega)]

lemma sum_upos_le (F : ℕ → ℝ) (hF : ∀ p, 0 ≤ F p) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), F (i * (n + 2) + (n + 1)) ≤
      ∑ p ∈ Finset.range ((m + 1) * (n + 2)), F p := by
  rw [← sum_upos]
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact le_rfl
  · exact hF p

lemma sum_wpos_le (G : ℕ → ℝ) (hG : ∀ p, 0 ≤ G p) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), G (i * (n + 2) + j) ≤
      ∑ p ∈ Finset.range ((m + 1) * (n + 2)), G p := by
  rw [← sum_wpos]
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact hG p
  · exact le_rfl

end Reindex

section Defs

variable (m n : ℕ) (r : ℕ → ℝ)

noncomputable def uOf (a : ℕ → ℝ) (i : ℕ) : ℝ := a (i * (n + 2) + (n + 1))

noncomputable def wOf (b : ℕ → ℝ) (i j : ℕ) : ℝ := b (i * (n + 2) + j)

noncomputable def rF (a b : ℕ → ℝ) : ℝ := rhat m n r (uOf n a) (wOf n b)

noncomputable def cF (a : ℕ → ℝ) : ℝ := csum m n (uOf n a)

noncomputable def theta (a b : ℕ → ℝ) (c : ℝ) : ℝ := c * rF m n r a b - cF m n a

noncomputable def gAu (a b : ℕ → ℝ) (c : ℝ) (i : ℕ) : ℝ :=
  c * gUR m n r (uOf n a) (wOf n b) i - gUC m n (uOf n a) i

noncomputable def gA (a b : ℕ → ℝ) (c : ℝ) (p : ℕ) : ℝ :=
  if p % (n + 2) = n + 1 then gAu m n r a b c (p / (n + 2)) else 0

noncomputable def gB (a b : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p % (n + 2) = n + 1 then 0 else gW n r (uOf n a) (wOf n b) (p / (n + 2)) (p % (n + 2))

end Defs

section Models

variable {m n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma sum_u_sq_le (a a' : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), (uOf n a' i - uOf n a i) ^ 2 ≤
      ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (a' p - a p) ^ 2 :=
  sum_upos_le n (fun p => (a' p - a p) ^ 2) (fun _ => sq_nonneg _) m

lemma sum_w_sq_le (b b' : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (wOf n b' i j - wOf n b i j) ^ 2 ≤
      ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (b' p - b p) ^ 2 :=
  sum_wpos_le n (fun p => (b' p - b p) ^ 2) (fun _ => sq_nonneg _) m

lemma sum_gA_mul (a b : ℕ → ℝ) (c : ℝ) (δ : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p * δ p =
      ∑ i ∈ Finset.range (m + 1), gAu m n r a b c i * δ (i * (n + 2) + (n + 1)) := by
  have e1 : ∀ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p * δ p =
      if p % (n + 2) = n + 1 then gAu m n r a b c (p / (n + 2)) * δ p else 0 := by
    intro p _
    unfold gA
    split_ifs
    · rfl
    · rw [zero_mul]
  rw [Finset.sum_congr rfl e1, sum_upos n (fun p => gAu m n r a b c (p / (n + 2)) * δ p)]
  apply Finset.sum_congr rfl
  intro i _
  rw [pos_div n i (Nat.lt_succ_self (n + 1))]

lemma sum_gB_mul (a b : ℕ → ℝ) (δ : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * δ p =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        gW n r (uOf n a) (wOf n b) i j * δ (i * (n + 2) + j) := by
  have e1 : ∀ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * δ p =
      if p % (n + 2) = n + 1 then 0 else
        gW n r (uOf n a) (wOf n b) (p / (n + 2)) (p % (n + 2)) * δ p := by
    intro p _
    unfold gB
    split_ifs
    · rw [zero_mul]
    · rfl
  rw [Finset.sum_congr rfl e1,
    sum_wpos n (fun p => gW n r (uOf n a) (wOf n b) (p / (n + 2)) (p % (n + 2)) * δ p)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n + 1 := Finset.mem_range.mp hj
  rw [pos_div n i (by omega), pos_mod n i (by omega)]

theorem theta_model_a (S : Scales n r ρ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a a' b : ℕ → ℝ) :
    |theta m n r a' b c - theta m n r a b c -
        ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p * (a' p - a p)| ≤
      2 ^ 17 * ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (a' p - a p) ^ 2 := by
  have h1 := rhat_model_u (m := m) S (uOf n a) (uOf n a') (wOf n b)
  have h2 := csum_model (m := m) (n := n) (uOf n a) (uOf n a')
  have hsq := sum_u_sq_le (m := m) (n := n) a a'
  have hU0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), (uOf n a' i - uOf n a i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p * (a' p - a p) =
      c * ∑ k ∈ Finset.range (m + 1), gUR m n r (uOf n a) (wOf n b) k * (uOf n a' k - uOf n a k) -
        ∑ k ∈ Finset.range (m + 1), gUC m n (uOf n a) k * (uOf n a' k - uOf n a k) := by
    rw [sum_gA_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (c * gUR m n r (uOf n a) (wOf n b) i - gUC m n (uOf n a) i) *
      (uOf n a' i - uOf n a i) = _
    ring
  have e : theta m n r a' b c - theta m n r a b c -
      ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p * (a' p - a p) =
      c * (rhat m n r (uOf n a') (wOf n b) - rhat m n r (uOf n a) (wOf n b) -
        ∑ k ∈ Finset.range (m + 1), gUR m n r (uOf n a) (wOf n b) k * (uOf n a' k - uOf n a k)) -
      (csum m n (uOf n a') - csum m n (uOf n a) -
        ∑ k ∈ Finset.range (m + 1), gUC m n (uOf n a) k * (uOf n a' k - uOf n a k)) := by
    rw [hsum]
    unfold theta rF cF
    ring
  rw [e]
  refine (abs_sub_le_sum _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hc0]
  have h3 := mul_le_mul hc1 h1 (abs_nonneg _) zero_le_one
  nlinarith

theorem theta_model_b (S : Scales n r ρ) (a b b' : ℕ → ℝ) (c : ℝ) :
    |theta m n r a b' c - theta m n r a b c -
        c * ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * (b' p - b p)| ≤
      |c| * (104 / ρ ^ 2 * ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (b' p - b p) ^ 2) := by
  have h1 := rhat_model_w (m := m) S (uOf n a) (wOf n b) (wOf n b')
  have hsq := sum_w_sq_le (m := m) (n := n) b b'
  have hρ : 0 ≤ 104 / ρ ^ 2 := by
    have := S.hρ
    positivity
  have e : theta m n r a b' c - theta m n r a b c -
      c * ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * (b' p - b p) =
      c * (rhat m n r (uOf n a) (wOf n b') - rhat m n r (uOf n a) (wOf n b) -
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          gW n r (uOf n a) (wOf n b) i j * (wOf n b' i j - wOf n b i j)) := by
    have hs : ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p * (b' p - b p) =
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          gW n r (uOf n a) (wOf n b) i j * (wOf n b' i j - wOf n b i j) :=
      sum_gB_mul a b (fun p => b' p - b p)
    rw [hs]
    unfold theta rF
    ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (h1.trans (mul_le_mul_of_nonneg_left hsq hρ)) (abs_nonneg c)

lemma gAu_abs {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b : ℕ → ℝ) (i : ℕ) :
    |gAu m n r a b c i| ≤ 193 := by
  unfold gAu
  have h1 := gUR_abs (m := m) (n := n) (r := r) (uOf n a) (wOf n b) i
  have h2 := gUC_abs (m := m) (n := n) (uOf n a) i
  refine (abs_sub_le_sum _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hc0]
  nlinarith [abs_nonneg (gUR m n r (uOf n a) (wOf n b) i)]

lemma sum_gA_sq (a b : ℕ → ℝ) (c : ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p ^ 2 =
      ∑ i ∈ Finset.range (m + 1), gAu m n r a b c i ^ 2 := by
  have h := sum_gA_mul (m := m) (n := n) (r := r) a b c (fun p => gA m n r a b c p)
  have e : ∀ i ∈ Finset.range (m + 1), gAu m n r a b c i * gA m n r a b c (i * (n + 2) + (n + 1)) =
      gAu m n r a b c i ^ 2 := by
    intro i _
    unfold gA
    rw [pos_mod n i (Nat.lt_succ_self (n + 1)), ite_eq_left rfl,
      pos_div n i (Nat.lt_succ_self (n + 1))]
    ring
  rw [Finset.sum_congr rfl e] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  ring

lemma gA_sq_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gA m n r a b c p ^ 2 ≤ 2 ^ 16 * ((m : ℝ) + 1) := by
  rw [sum_gA_sq]
  have hterm : ∀ i ∈ Finset.range (m + 1), gAu m n r a b c i ^ 2 ≤ 2 ^ 16 := by
    intro i _
    have h := gAu_abs (m := m) (n := n) (r := r) hc0 hc1 a b i
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    norm_num at h2 ⊢
    linarith
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h
  linarith

lemma sum_gB_sq (a b : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p ^ 2 =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        gW n r (uOf n a) (wOf n b) i j ^ 2 := by
  have h := sum_gB_mul (m := m) (n := n) (r := r) a b (fun p => gB n r a b p)
  have e : ∀ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      gW n r (uOf n a) (wOf n b) i j * gB n r a b (i * (n + 2) + j) =
      ∑ j ∈ Finset.range (n + 1), gW n r (uOf n a) (wOf n b) i j ^ 2 := by
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    unfold gB
    rw [pos_mod n i (by omega), ite_eq_right (by omega), pos_div n i (by omega)]
    ring
  rw [Finset.sum_congr rfl e] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  ring

lemma sig_sq_le (v : ℝ) : sig n v ^ 2 ≤ 16 := by
  have h0 := sig_nonneg (n := n) v
  have h1 : sig n v ≤ 4 := by
    unfold sig
    have := psi_le_one v
    have := psi_nonneg v
    have := smax_le (n := n)
    have := smax_pos (n := n)
    nlinarith
  nlinarith

lemma gB_sq_le (S : Scales n r ρ) (a b : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), gB n r a b p ^ 2 ≤ 2 ^ 20 * ((m : ℝ) + 1) := by
  rw [sum_gB_sq]
  have hterm : ∀ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      gW n r (uOf n a) (wOf n b) i j ^ 2 ≤ 2 ^ 20 := by
    intro i _
    have h := rwGrad_sq_le S (sig n (prevRead (uOf n a) i)) (uOf n a i) (wOf n b i)
    have h2 := sig_sq_le (n := n) (prevRead (uOf n a) i)
    unfold gW
    linarith
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h
  linarith

lemma rF_nonneg (a b : ℕ → ℝ) : 0 ≤ rF m n r a b := rhat_nonneg _ _

lemma cF_nonneg (a : ℕ → ℝ) : 0 ≤ cF m n a := csum_nonneg _

lemma rF_le_cF (a b : ℕ → ℝ) : rF m n r a b ≤ cF m n a := rhat_le_csum _ _

lemma cF_le (a : ℕ → ℝ) : cF m n a ≤ 6 * ((m : ℝ) + 1) := csum_le _

theorem gA_lip (S : Scales n r ρ) {c c' : ℝ} (hc1 : |c'| ≤ 1) (a a' b b' : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (gA m n r a' b' c' p - gA m n r a b c p) ^ 2 ≤
      2 ^ 33 * (∑ p ∈ Finset.range ((m + 1) * (n + 2)), (a' p - a p) ^ 2 +
        ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (b' p - b p) ^ 2) +
      2 ^ 15 * ((m : ℝ) + 1) * (c' - c) ^ 2 := by
  have hA := sum_u_sq_le (m := m) (n := n) a a'
  have hB := sum_w_sq_le (m := m) (n := n) b b'
  have h1 := gUR_lip (m := m) S (uOf n a) (uOf n a') (wOf n b) (wOf n b')
  have h2 := gUC_lip (m := m) (n := n) (uOf n a) (uOf n a')
  have e1 : ∀ p ∈ Finset.range ((m + 1) * (n + 2)),
      (gA m n r a' b' c' p - gA m n r a b c p) ^ 2 =
      if p % (n + 2) = n + 1 then
        (gAu m n r a' b' c' (p / (n + 2)) - gAu m n r a b c (p / (n + 2))) ^ 2 else 0 := by
    intro p _
    unfold gA
    split_ifs
    · rfl
    · norm_num
  rw [Finset.sum_congr rfl e1, sum_upos n (fun p =>
    (gAu m n r a' b' c' (p / (n + 2)) - gAu m n r a b c (p / (n + 2))) ^ 2)]
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (gAu m n r a' b' c' ((i * (n + 2) + (n + 1)) / (n + 2)) -
        gAu m n r a b c ((i * (n + 2) + (n + 1)) / (n + 2))) ^ 2 ≤
      3 * ((gUR m n r (uOf n a') (wOf n b') i - gUR m n r (uOf n a) (wOf n b) i) ^ 2 +
        9409 * (c' - c) ^ 2 + (gUC m n (uOf n a') i - gUC m n (uOf n a) i) ^ 2) := by
    intro i _
    rw [pos_div n i (Nat.lt_succ_self (n + 1))]
    unfold gAu
    have hg := gUR_abs (m := m) (n := n) (r := r) (uOf n a) (wOf n b) i
    have e : c' * gUR m n r (uOf n a') (wOf n b') i - gUC m n (uOf n a') i -
        (c * gUR m n r (uOf n a) (wOf n b) i - gUC m n (uOf n a) i) =
        c' * (gUR m n r (uOf n a') (wOf n b') i - gUR m n r (uOf n a) (wOf n b) i) +
          (c' - c) * gUR m n r (uOf n a) (wOf n b) i +
          -(gUC m n (uOf n a') i - gUC m n (uOf n a) i) := by ring
    rw [e]
    refine (sq_add3 _ _ _).trans ?_
    have t1 : (c' * (gUR m n r (uOf n a') (wOf n b') i - gUR m n r (uOf n a) (wOf n b) i)) ^ 2 ≤
        (gUR m n r (uOf n a') (wOf n b') i - gUR m n r (uOf n a) (wOf n b) i) ^ 2 := by
      rw [mul_pow]
      have hc2 : c' ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hc1 2
        rw [sq_abs] at this
        linarith
      exact mul_le_of_le_one_left (sq_nonneg _) hc2
    have t2 : ((c' - c) * gUR m n r (uOf n a) (wOf n b) i) ^ 2 ≤ 9409 * (c' - c) ^ 2 := by
      rw [mul_pow]
      have hg2 : gUR m n r (uOf n a) (wOf n b) i ^ 2 ≤ 9409 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hg 2
        rw [sq_abs] at this
        linarith
      nlinarith [sq_nonneg (c' - c)]
    have t3 : (-(gUC m n (uOf n a') i - gUC m n (uOf n a) i)) ^ 2 =
        (gUC m n (uOf n a') i - gUC m n (uOf n a) i) ^ 2 := by ring
    rw [t3]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  have hc0 : 0 ≤ (c' - c) ^ 2 := sq_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hmc := mul_nonneg hm0 hc0
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), (uOf n a' i - uOf n a i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (wOf n b' i j - wOf n b i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

theorem gB_lip (S : Scales n r ρ) (a a' b b' : ℕ → ℝ) :
    ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (gB n r a' b' p - gB n r a b p) ^ 2 ≤
      2 ^ 25 * (∑ p ∈ Finset.range ((m + 1) * (n + 2)), (a' p - a p) ^ 2 +
        ∑ p ∈ Finset.range ((m + 1) * (n + 2)), (b' p - b p) ^ 2) := by
  have hA := sum_u_sq_le (m := m) (n := n) a a'
  have hB := sum_w_sq_le (m := m) (n := n) b b'
  have h1 := gW_lip (m := m) S (uOf n a) (uOf n a') (wOf n b) (wOf n b')
  have e1 : ∀ p ∈ Finset.range ((m + 1) * (n + 2)),
      (gB n r a' b' p - gB n r a b p) ^ 2 =
      if p % (n + 2) = n + 1 then 0 else
        (gW n r (uOf n a') (wOf n b') (p / (n + 2)) (p % (n + 2)) -
          gW n r (uOf n a) (wOf n b) (p / (n + 2)) (p % (n + 2))) ^ 2 := by
    intro p _
    unfold gB
    split_ifs
    · norm_num
    · rfl
  rw [Finset.sum_congr rfl e1, sum_wpos n (fun p =>
    (gW n r (uOf n a') (wOf n b') (p / (n + 2)) (p % (n + 2)) -
      gW n r (uOf n a) (wOf n b) (p / (n + 2)) (p % (n + 2))) ^ 2)]
  have e2 : ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (gW n r (uOf n a') (wOf n b') ((i * (n + 2) + j) / (n + 2)) ((i * (n + 2) + j) % (n + 2)) -
        gW n r (uOf n a) (wOf n b) ((i * (n + 2) + j) / (n + 2)) ((i * (n + 2) + j) % (n + 2))) ^ 2 =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (gW n r (uOf n a') (wOf n b') i j - gW n r (uOf n a) (wOf n b) i j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [pos_div n i (by omega), pos_mod n i (by omega)]
  rw [e2]
  refine h1.trans ?_
  linarith

end Models

end LongTails.Proofs.NcPlFlat
