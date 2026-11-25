import LongTails.Proofs.NcPlSchedule
import LongTails.Proofs.NcPlCalc

open scoped BigOperators

namespace LongTails.Proofs.NcPlBlock

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL LongTails.Proofs.NcPlSchedule LongTails.Proofs.NcPlCalc

noncomputable def rs (n1 N k : ℕ) : ℝ := max (1 / (n1 : ℝ)) ((1 / 2 : ℝ) ^ (N - 1 - k))

lemma rs_pos (n1 N k : ℕ) : 0 < rs n1 N k :=
  lt_of_lt_of_le (by positivity) (le_max_right _ _)

lemma rs_ge (n1 N k : ℕ) : 1 / (n1 : ℝ) ≤ rs n1 N k := le_max_left _ _

lemma rs_le_one {n1 : ℕ} (hn1 : 0 < n1) (N k : ℕ) : rs n1 N k ≤ 1 := by
  apply max_le
  · rw [div_le_one (by exact_mod_cast hn1)]
    exact_mod_cast hn1
  · exact pow_le_one₀ (by norm_num) (by norm_num)

lemma rs_sq {n1 N k : ℕ} (hN : N = n1 * n1) (hk : k < N) : rs n1 N k ^ 2 = wt N (k + 1) := by
  have h1 : (0 : ℝ) ≤ 1 / (n1 : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N - 1 - k) := by positivity
  have e1 : (1 / (n1 : ℝ)) ^ 2 = 1 / (N : ℝ) := by
    rw [hN]
    push_cast
    rw [div_pow, one_pow, sq]
  have e2 : ((1 / 2 : ℝ) ^ (N - 1 - k)) ^ 2 = (1 / 4 : ℝ) ^ (N - (k + 1)) := by
    have : N - 1 - k = N - (k + 1) := by omega
    rw [this, ← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold rs wt
  rcases le_total (1 / (n1 : ℝ)) ((1 / 2 : ℝ) ^ (N - 1 - k)) with h | h
  · have hsq := pow_le_pow_left₀ h1 h 2
    rw [max_eq_right h, ← e1, ← e2, max_eq_right hsq]
  · have hsq := pow_le_pow_left₀ h2 h 2
    rw [max_eq_left h, ← e1, ← e2, max_eq_left hsq]

lemma rs_last {n1 N : ℕ} (hn1 : 0 < n1) : rs n1 N (N - 1) = 1 := by
  unfold rs
  rw [Nat.sub_self, pow_zero]
  apply max_eq_right
  rw [div_le_one (by exact_mod_cast hn1)]
  exact_mod_cast hn1

noncomputable def afun (t : ℝ) : ℝ := 4 - phi t

noncomputable def dafun (t : ℝ) : ℝ := -dphi t

lemma afun_hasDerivAt (t : ℝ) : HasDerivAt afun (dafun t) t := by
  have h : HasDerivAt (fun x : ℝ => 4 - phi x) (-dphi t) t := (phi_hasDerivAt t).const_sub 4
  exact h

lemma afun_ge (t : ℝ) : 1 ≤ afun t := by
  have := phi_le t
  unfold afun
  linarith

lemma afun_le (t : ℝ) : afun t ≤ 4 := by
  have := phi_nonneg t
  unfold afun
  linarith

lemma afun_nonneg (t : ℝ) : 0 ≤ afun t := le_trans zero_le_one (afun_ge t)

lemma dafun_nonpos (t : ℝ) : dafun t ≤ 0 := neg_nonpos.mpr (dphi_nonneg t)

lemma dafun_abs (t : ℝ) : |dafun t| ≤ 1 := by
  rw [dafun, abs_neg, abs_of_nonneg (dphi_nonneg t)]
  exact dphi_le_one t

lemma afun_lipschitz (a b : ℝ) : |afun a - afun b| ≤ |a - b| := by
  have h := phi_lipschitz a b
  have e : afun a - afun b = -(phi a - phi b) := by unfold afun; ring
  rw [e, abs_neg]
  exact h

lemma dafun_lipschitz (a b : ℝ) : |dafun a - dafun b| ≤ 4 * |a - b| := by
  have h := dphi_lipschitz a b
  have e : dafun a - dafun b = -(dphi a - dphi b) := by unfold dafun; ring
  rw [e, abs_neg]
  exact h

section Defs

variable (n : ℕ) (r : ℕ → ℝ)

noncomputable def rewardVal (α : ℕ → ℝ) (β : ℝ) (y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), α j * gprev r y j * push (y j / r j) + β * gate (y n / r n)

noncomputable def rewardGrad (α : ℕ → ℝ) (β : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  α k * gprev r y k * dpush (y k / r k) / r k + cval n α β r y k * dgate (y k / r k) / r k

noncomputable def rwd (s t : ℝ) (y : ℕ → ℝ) : ℝ :=
  rewardVal n r (alphaSeq (n + 1) s) (ampT (n + 1) s * afun t) y

noncomputable def rwGrad (s t : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  rewardGrad n r (alphaSeq (n + 1) s) (ampT (n + 1) s * afun t) y k

noncomputable def rwDs (s t : ℝ) (y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * damp (n + 1) j s * gprev r y j * push (y j / r j) +
    dampT (n + 1) s * afun t * gate (y n / r n)

noncomputable def rwDt (s t : ℝ) (y : ℕ → ℝ) : ℝ :=
  ampT (n + 1) s * dafun t * gate (y n / r n)

noncomputable def comp (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * amp (n + 1) j s + 4 * ampT (n + 1) s

noncomputable def dcomp (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * damp (n + 1) j s + 4 * dampT (n + 1) s

variable {n r}

lemma blockVal_eq_reward (lam Lam r0 : ℝ) (α : ℕ → ℝ) (β : ℝ) (y : ℕ → ℝ) :
    blockVal n lam Lam r0 α β r y = rewardVal n r α β y -
      ∑ j ∈ Finset.range (n + 1), (lam * y j ^ 2 / 2 + Lam / 2 * pos (-y j - r0 / 2) ^ 2) := by
  unfold blockVal rewardVal
  rw [← sub_add_eq_add_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma blockGrad_eq_reward (lam Lam r0 : ℝ) (α : ℕ → ℝ) (β : ℝ) (y : ℕ → ℝ) (k : ℕ) :
    blockGrad n lam Lam r0 α β r y k =
      rewardGrad n r α β y k - lam * y k + Lam * pos (-y k - r0 / 2) := by
  unfold blockGrad rewardGrad
  ring

lemma rw_nonneg (s t : ℝ) (y : ℕ → ℝ) : 0 ≤ rwd n r s t y := by
  unfold rwd rewardVal
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (alphaSeq_nonneg s j) (gprev_nonneg r y j)) (push_nonneg _)
  · exact mul_nonneg (mul_nonneg (ampT_nonneg s) (afun_nonneg t)) (gate_nonneg _)

lemma rw_le_comp (s t : ℝ) (y : ℕ → ℝ) : rwd n r s t y ≤ comp n s := by
  unfold rwd rewardVal comp
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    have h0 := alphaSeq_nonneg (N := n + 1) s j
    have h1 : alphaSeq (n + 1) s j * gprev r y j ≤ alphaSeq (n + 1) s j :=
      mul_le_of_le_one_right h0 (gprev_le_one r y j)
    have h2 : alphaSeq (n + 1) s j * gprev r y j * push (y j / r j) ≤
        alphaSeq (n + 1) s j * gprev r y j :=
      mul_le_of_le_one_right (mul_nonneg h0 (gprev_nonneg r y j)) (push_le_one _)
    exact h2.trans h1
  · have h0 := ampT_nonneg (N := n + 1) s
    have h1 : ampT (n + 1) s * afun t ≤ ampT (n + 1) s * 4 :=
      mul_le_mul_of_nonneg_left (afun_le t) h0
    have h2 : ampT (n + 1) s * afun t * gate (y n / r n) ≤ ampT (n + 1) s * afun t :=
      mul_le_of_le_one_right (mul_nonneg h0 (afun_nonneg t)) (gate_le_one _)
    linarith

lemma comp_nonneg (s : ℝ) : 0 ≤ comp n s := by
  unfold comp
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (wt_pos j).le (amp_nonneg j s)
  · exact mul_nonneg (by norm_num) (ampT_nonneg s)

lemma comp_le (s : ℝ) : comp n s ≤ 6 := by
  unfold comp
  have h1 : ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * amp (n + 1) j s ≤ cum (n + 1) (n + 1) := by
    unfold cum
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_of_le_one_right (wt_pos j).le (amp_le_one j s)
  have h2 := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  have h3 := ampT_le_one (N := n + 1) s
  linarith

lemma comp_of_le {s : ℝ} (hs : s ≤ 0) : comp n s = 0 := by
  unfold comp
  rw [ampT_of_le (le_trans hs (cum_nonneg _ _)), mul_zero, add_zero]
  apply Finset.sum_eq_zero
  intro j _
  rw [amp_of_le (le_trans hs (cum_nonneg _ _)), mul_zero]

lemma dcomp_of_le {s : ℝ} (hs : s ≤ 0) : dcomp n s = 0 := by
  unfold dcomp
  rw [dampT_of_le (le_trans hs (cum_nonneg _ _)), mul_zero, add_zero]
  apply Finset.sum_eq_zero
  intro j _
  rw [damp_of_le (le_trans hs (cum_nonneg _ _)), mul_zero]

lemma rwDs_nonneg (s t : ℝ) (y : ℕ → ℝ) : 0 ≤ rwDs n r s t y := by
  unfold rwDs
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (mul_nonneg (wt_pos j).le (damp_nonneg j s))
      (gprev_nonneg r y j)) (push_nonneg _)
  · exact mul_nonneg (mul_nonneg (dampT_nonneg s) (afun_nonneg t)) (gate_nonneg _)

lemma rwDs_le_dcomp (s t : ℝ) (y : ℕ → ℝ) : rwDs n r s t y ≤ dcomp n s := by
  unfold rwDs dcomp
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    have h0 : 0 ≤ wt (n + 1) j * damp (n + 1) j s := mul_nonneg (wt_pos j).le (damp_nonneg j s)
    have h1 : wt (n + 1) j * damp (n + 1) j s * gprev r y j ≤ wt (n + 1) j * damp (n + 1) j s :=
      mul_le_of_le_one_right h0 (gprev_le_one r y j)
    have h2 : wt (n + 1) j * damp (n + 1) j s * gprev r y j * push (y j / r j) ≤
        wt (n + 1) j * damp (n + 1) j s * gprev r y j :=
      mul_le_of_le_one_right (mul_nonneg h0 (gprev_nonneg r y j)) (push_le_one _)
    exact h2.trans h1
  · have h0 := dampT_nonneg (N := n + 1) s
    have h1 : dampT (n + 1) s * afun t ≤ dampT (n + 1) s * 4 :=
      mul_le_mul_of_nonneg_left (afun_le t) h0
    have h2 : dampT (n + 1) s * afun t * gate (y n / r n) ≤ dampT (n + 1) s * afun t :=
      mul_le_of_le_one_right (mul_nonneg h0 (afun_nonneg t)) (gate_le_one _)
    linarith

lemma dcomp_le (s : ℝ) : dcomp n s ≤ 6 := by
  unfold dcomp
  have h1 : ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * damp (n + 1) j s ≤ cum (n + 1) (n + 1) := by
    unfold cum
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_of_le_one_right (wt_pos j).le (damp_le_one j s)
  have h2 := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  have h3 := dampT_le_one (N := n + 1) s
  linarith

lemma dcomp_nonneg (s : ℝ) : 0 ≤ dcomp n s := by
  unfold dcomp
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (wt_pos j).le (damp_nonneg j s)
  · exact mul_nonneg (by norm_num) (dampT_nonneg s)

lemma rwDt_nonpos (s t : ℝ) (y : ℕ → ℝ) : rwDt n r s t y ≤ 0 := by
  unfold rwDt
  have h := mul_nonneg (ampT_nonneg (N := n + 1) s) (gate_nonneg (y n / r n))
  have hd := dafun_nonpos t
  nlinarith

lemma rwDt_abs (s t : ℝ) (y : ℕ → ℝ) : |rwDt n r s t y| ≤ 1 := by
  unfold rwDt
  rw [abs_mul, abs_mul, abs_of_nonneg (ampT_nonneg s), abs_of_nonneg (gate_nonneg _)]
  have h1 := ampT_le_one (N := n + 1) s
  have h2 := dafun_abs t
  have h3 := gate_le_one (y n / r n)
  have h4 := ampT_nonneg (N := n + 1) s
  have h5 := gate_nonneg (y n / r n)
  have h6 : ampT (n + 1) s * |dafun t| ≤ 1 := by nlinarith [abs_nonneg (dafun t)]
  nlinarith [mul_nonneg h4 (abs_nonneg (dafun t))]

lemma comp_hasDerivAt (s : ℝ) : HasDerivAt (comp n) (dcomp n s) s := by
  have h1 : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range (n + 1), wt (n + 1) j * amp (n + 1) j x)
      (∑ j ∈ Finset.range (n + 1), wt (n + 1) j * damp (n + 1) j s) s :=
    HasDerivAt.fun_sum fun j _ => (amp_hasDerivAt j s).const_mul (wt (n + 1) j)
  have h2 : HasDerivAt (fun x : ℝ => 4 * ampT (n + 1) x) (4 * dampT (n + 1) s) s :=
    (ampT_hasDerivAt s).const_mul 4
  exact h1.add h2

lemma rw_hasDerivAt_s (s t : ℝ) (y : ℕ → ℝ) :
    HasDerivAt (fun x => rwd n r x t y) (rwDs n r s t y) s := by
  have h1 : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      alphaSeq (n + 1) x j * gprev r y j * push (y j / r j))
      (∑ j ∈ Finset.range (n + 1),
        wt (n + 1) j * damp (n + 1) j s * gprev r y j * push (y j / r j)) s :=
    HasDerivAt.fun_sum fun j _ =>
      ((((amp_hasDerivAt j s).const_mul (wt (n + 1) j)).mul_const (gprev r y j)).mul_const
        (push (y j / r j)))
  have h2 : HasDerivAt (fun x : ℝ => ampT (n + 1) x * afun t * gate (y n / r n))
      (dampT (n + 1) s * afun t * gate (y n / r n)) s :=
    ((ampT_hasDerivAt s).mul_const (afun t)).mul_const (gate (y n / r n))
  exact h1.add h2

lemma rw_hasDerivAt_t (s t : ℝ) (y : ℕ → ℝ) :
    HasDerivAt (fun x => rwd n r s x y) (rwDt n r s t y) t := by
  have h2 : HasDerivAt (fun x : ℝ => ampT (n + 1) s * afun x * gate (y n / r n))
      (ampT (n + 1) s * dafun t * gate (y n / r n)) t :=
    ((afun_hasDerivAt t).const_mul (ampT (n + 1) s)).mul_const (gate (y n / r n))
  have h := h2.const_add (∑ j ∈ Finset.range (n + 1),
    alphaSeq (n + 1) s j * gprev r y j * push (y j / r j))
  exact h

end Defs

end LongTails.Proofs.NcPlBlock
