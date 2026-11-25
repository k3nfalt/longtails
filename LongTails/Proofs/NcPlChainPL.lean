import LongTails.Proofs.NcPlChain

open scoped BigOperators

namespace LongTails.Proofs.NcPlChainPL

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL LongTails.Proofs.NcPlSchedule LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain

noncomputable def lamOf (n : ℕ) : ℝ := 1 / (2048 * ((n : ℝ) + 1))

lemma lamOf_pos (n : ℕ) : 0 < lamOf n := by
  unfold lamOf
  positivity

lemma lamOf_le_one (n : ℕ) : lamOf n ≤ 1 := by
  unfold lamOf
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

noncomputable def hb (lam ρ v : ℝ) : ℝ := -(lam * v ^ 2 / 2) - rr (-v - ρ / 2)

noncomputable def dhb (lam ρ v : ℝ) : ℝ := -(lam * v) + pos (-v - ρ / 2)

lemma rr_nonneg (s : ℝ) : 0 ≤ rr s := by
  unfold rr
  positivity

lemma hb_model {lam : ℝ} (hlam : 0 ≤ lam) (ρ v v' : ℝ) :
    |hb lam ρ v' - hb lam ρ v - dhb lam ρ v * (v' - v)| ≤ (lam / 2 + 1 / 2) * (v' - v) ^ 2 := by
  have h := rr_model (-v - ρ / 2) (-v' - ρ / 2)
  have e2 : (-v' - ρ / 2 - (-v - ρ / 2)) ^ 2 = (v' - v) ^ 2 := by ring
  rw [e2] at h
  have e : hb lam ρ v' - hb lam ρ v - dhb lam ρ v * (v' - v) =
      -(lam / 2 * (v' - v) ^ 2) - (rr (-v' - ρ / 2) - rr (-v - ρ / 2) -
        pos (-v - ρ / 2) * (-v' - ρ / 2 - (-v - ρ / 2))) := by
    unfold hb dhb
    ring
  rw [e]
  have h2 := abs_le.mp h
  have h3 : 0 ≤ lam / 2 * (v' - v) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2]

lemma dhb_lip {lam : ℝ} (hlam : 0 ≤ lam) (ρ a b : ℝ) :
    |dhb lam ρ a - dhb lam ρ b| ≤ (lam + 1) * |a - b| := by
  have h := pos_lipschitz (-a - ρ / 2) (-b - ρ / 2)
  have e1 : -a - ρ / 2 - (-b - ρ / 2) = -(a - b) := by ring
  rw [e1, abs_neg] at h
  have e : dhb lam ρ a - dhb lam ρ b =
      -(lam * (a - b)) + (pos (-a - ρ / 2) - pos (-b - ρ / 2)) := by
    unfold dhb
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_of_nonneg hlam]
  linarith

lemma hb_le_zero {lam : ℝ} (hlam : 0 ≤ lam) (ρ v : ℝ) : hb lam ρ v ≤ 0 := by
  unfold hb
  have h1 := rr_nonneg (-v - ρ / 2)
  have h2 : 0 ≤ lam * v ^ 2 / 2 := by positivity
  linarith

lemma hb_zero (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : hb lam ρ 0 = 0 := by
  unfold hb rr
  rw [pos_of_nonpos (by linarith)]
  ring

lemma dhb_zero (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : dhb lam ρ 0 = 0 := by
  unfold dhb
  rw [pos_of_nonpos (by linarith)]
  ring

lemma hb_eq (lam ρ v : ℝ) : hb lam ρ v = -(lam * v ^ 2 / 2) - pos (-v - ρ / 2) ^ 2 / 2 := rfl

lemma hb_eq_hpot (lam ρ r v : ℝ) : hpot lam 1 ρ 0 r v = hb lam ρ v := by
  unfold hpot hb rr
  ring

lemma dhb_eq_dhpot (lam ρ r v : ℝ) : dhpot lam 1 ρ 0 r v = dhb lam ρ v := by
  unfold dhpot dhb
  ring

lemma hb_pl {lam ρ : ℝ} (hlam : 0 < lam) (hl1 : lam ≤ 1) (hρ : 0 < ρ) (v w : ℝ) :
    hb lam ρ w - hb lam ρ v ≤ 5 / (2 * lam) * dhb lam ρ v ^ 2 := by
  have h := hpot_sub_le (lam := lam) (Lam := 1) (r0 := ρ) (α := 0) (r := ρ) hlam hl1 hρ.le
    le_rfl hρ le_rfl (by positivity) v w
  rw [hb_eq_hpot, hb_eq_hpot, dhb_eq_dhpot] at h
  exact h

lemma dhb_mul_self (lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (v : ℝ) :
    dhb lam ρ v * v ≤ -(lam * v ^ 2) - pos (-v - ρ / 2) ^ 2 := by
  unfold dhb
  rcases le_total 0 (-v - ρ / 2) with h | h
  · rw [pos_of_nonneg h]
    nlinarith
  · rw [pos_of_nonpos h]
    nlinarith

section Block

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

noncomputable def bval (n : ℕ) (r : ℕ → ℝ) (ρ v t : ℝ) (y : ℕ → ℝ) : ℝ :=
  rwd n r (sig n v) t y + ∑ j ∈ Finset.range (n + 1), hb (lamOf n) ρ (y j)

noncomputable def bgrad (n : ℕ) (r : ℕ → ℝ) (ρ v t : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  rwGrad n r (sig n v) t y k + dhb (lamOf n) ρ (y k)

lemma bval_eq (v t : ℝ) (y : ℕ → ℝ) :
    bval n r ρ v t y = blockVal n (lamOf n) 1 ρ (alphaSeq (n + 1) (sig n v))
      (ampT (n + 1) (sig n v) * afun t) r y := by
  rw [blockVal_eq_reward]
  unfold bval rwd
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hb_eq]
  ring

lemma bgrad_eq (v t : ℝ) (y : ℕ → ℝ) (k : ℕ) :
    bgrad n r ρ v t y k = blockGrad n (lamOf n) 1 ρ (alphaSeq (n + 1) (sig n v))
      (ampT (n + 1) (sig n v) * afun t) r y k := by
  rw [blockGrad_eq_reward]
  unfold bgrad rwGrad dhb
  ring

lemma alpha_le_scale (S : Scales n r ρ) (s : ℝ) {j : ℕ} (hj : j ≤ n) :
    alphaSeq (n + 1) s j ≤ 3 * 1 * r j ^ 2 := by
  have h := alphaSeq_le (N := n + 1) (k := j) (by omega) s
  rw [S.sq j hj]
  have := wt_pos (N := n + 1) (j + 1)
  linarith

theorem block_pl_chain (S : Scales n r ρ) (v t : ℝ) (y y' : ℕ → ℝ) :
    bval n r ρ v t y' - bval n r ρ v t y ≤
      147 / lamOf n * ∑ k ∈ Finset.range (n + 1), bgrad n r ρ v t y k ^ 2 := by
  rw [bval_eq, bval_eq]
  have hsum : ∑ k ∈ Finset.range (n + 1), bgrad n r ρ v t y k ^ 2 =
      ∑ k ∈ Finset.range (n + 1), blockGrad n (lamOf n) 1 ρ (alphaSeq (n + 1) (sig n v))
        (ampT (n + 1) (sig n v) * afun t) r y k ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by rw [bgrad_eq])
  rw [hsum]
  refine block_pl (lamOf_pos n) (lamOf_le_one n) S.hρ S.ge (fun j _ => alphaSeq_nonneg _ j)
    (fun j hj => alpha_le_scale S _ hj) (mul_nonneg (ampT_nonneg _) (afun_nonneg t)) ?_ ?_ y y'
  · intro j hj h
    have h1 := schedule_H1 (lam := lamOf n) (b := afun t) rfl hj h
    rw [S.sq j hj]
    exact h1
  · intro J hJ h
    have h1 := schedule_H2 (lam := lamOf n) (afun_nonneg t) (afun_le t) rfl hJ h
    rw [S.sq J hJ]
    exact h1

theorem block_open_chain (S : Scales n r ρ) {v : ℝ} (hv : 1 ≤ v) (t : ℝ) (y : ℕ → ℝ)
    (hzero : ∀ k, k ≤ n → bgrad n r ρ v t y k = 0) : gate (y n / r n) = 1 := by
  have h := block_open (lamOf_pos n) S.hρ S.ge (fun j _ => alphaSeq_nonneg (sig n v) j)
    (fun j hj => alpha_le_scale S _ hj) (mul_nonneg (ampT_nonneg (sig n v)) (afun_nonneg t))
    (fun j hj h => by
      have h1 := schedule_H1 (lam := lamOf n) (b := afun t) rfl hj h
      rw [S.sq j hj]
      exact h1) y
    (fun k hk => by rw [← bgrad_eq]; exact hzero k hk) n le_rfl
  rw [NcPlBlockPL.chat, ite_eq_right (lt_irrefl n)] at h
  have hs : sig n v = smax (n + 1) := sig_of_ge hv
  have hT : ampT (n + 1) (sig n v) = 1 := by
    rw [hs]
    exact ampT_full le_rfl
  rw [hT, one_mul] at h
  have ha := afun_ge t
  rcases mul_eq_zero.mp h with h0 | h0
  · linarith
  · linarith

lemma dpush_mul_le (u : ℝ) : dpush u * u ≤ 1 := by
  rcases le_or_gt u 3 with h | h
  · have h1 := dpush_le u
    have h2 := dpush_nonneg u
    rcases le_or_gt u 0 with h0 | h0
    · nlinarith
    · nlinarith
  · rw [dpush_of_ge h.le, zero_mul]
    norm_num

lemma dgate_mul_le (u : ℝ) : dgate u * u ≤ 4 := by
  rcases le_or_gt u 2 with h | h
  · have h1 := dgate_le u
    have h2 := dgate_nonneg u
    rcases le_or_gt u 0 with h0 | h0
    · nlinarith
    · nlinarith
  · rw [dgate_of_ge h.le, zero_mul]
    norm_num

lemma term_bound {A C u ρ' y : ℝ} (hr : 0 < ρ') (hy : y = u * ρ') (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) :
    (A * dpush u / ρ' + C * dgate u / ρ') * y ≤ A + 4 * C := by
  have e : (A * dpush u / ρ' + C * dgate u / ρ') * y = A * (dpush u * u) + C * (dgate u * u) := by
    rw [hy]
    field_simp
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left (dpush_mul_le u) hA0
  have h2 := mul_le_mul_of_nonneg_left (dgate_mul_le u) hC0
  linarith

lemma alphaSeq_le_wt (s : ℝ) (k : ℕ) : alphaSeq (n + 1) s k ≤ wt (n + 1) k := by
  unfold alphaSeq
  exact mul_le_of_le_one_right (wt_pos k).le (amp_le_one k s)

lemma chat_le_wt (s t : ℝ) {k : ℕ} (hk : k ≤ n) :
    NcPlBlockPL.chat n (alphaSeq (n + 1) s) (ampT (n + 1) s * afun t) k ≤
      4 * wt (n + 1) (k + 1) := by
  unfold NcPlBlockPL.chat
  have hw := wt_pos (N := n + 1) (k + 1)
  by_cases hkn : k < n
  · rw [ite_eq_left hkn]
    have := alphaSeq_le_wt (n := n) s (k + 1)
    linarith
  · rw [ite_eq_right hkn]
    have hk' : k = n := by omega
    rw [hk', wt_top (n + 1) (Nat.succ_pos n)]
    have h1 := ampT_le_one (N := n + 1) s
    have h2 := ampT_nonneg (N := n + 1) s
    have h3 := afun_le t
    have h4 := afun_nonneg t
    nlinarith

theorem farfield (S : Scales n r ρ) (s t : ℝ) (y : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), rwGrad n r s t y k * y k ≤ 40 := by
  have hterm : ∀ k ∈ Finset.range (n + 1), rwGrad n r s t y k * y k ≤
      wt (n + 1) k + 16 * wt (n + 1) (k + 1) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hr := S.pos hkn
    have hα0 : ∀ j, j ≤ n → 0 ≤ alphaSeq (n + 1) s j := fun j _ => alphaSeq_nonneg s j
    have hβ0 : 0 ≤ ampT (n + 1) s * afun t := mul_nonneg (ampT_nonneg s) (afun_nonneg t)
    have hA0 : 0 ≤ alphaSeq (n + 1) s k * gprev r y k :=
      mul_nonneg (alphaSeq_nonneg s k) (gprev_nonneg r y k)
    have hC0 := cval_nonneg hα0 hβ0 r y k
    have hb := term_bound (A := alphaSeq (n + 1) s k * gprev r y k)
      (C := cval n (alphaSeq (n + 1) s) (ampT (n + 1) s * afun t) r y k)
      (u := y k / r k) (y := y k) hr (div_mul_cancel₀ _ hr.ne').symm hA0 hC0
    have hA1 : alphaSeq (n + 1) s k * gprev r y k ≤ wt (n + 1) k :=
      (mul_le_of_le_one_right (alphaSeq_nonneg s k) (gprev_le_one r y k)).trans
        (alphaSeq_le_wt s k)
    have hC1 := (cval_le_chat hα0 r y k).trans (chat_le_wt (n := n) s t hkn)
    unfold rwGrad rewardGrad
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ k ∈ Finset.range (n + 1), wt (n + 1) k = cum (n + 1) (n + 1) := rfl
  have h2 : ∑ k ∈ Finset.range (n + 1), wt (n + 1) (k + 1) ≤ cum (n + 1) (n + 1) + 1 := by
    have h3 := Finset.sum_range_succ' (fun k => wt (n + 1) k) (n + 1)
    have h4 : ∑ k ∈ Finset.range (n + 1 + 1), wt (n + 1) k = cum (n + 1) (n + 1 + 1) := rfl
    rw [h4, cum_succ, wt_top (n + 1) (Nat.succ_pos n)] at h3
    have := wt_pos (N := n + 1) 0
    linarith
  have h5 := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  rw [h1]
  linarith

lemma mono_front {c : ℝ} (hc1 : c ≤ 1) (t : ℝ) (y : ℕ → ℝ) {s s' : ℝ}
    (h : s ≤ s') : c * rwd n r s' t y - comp n s' ≤ c * rwd n r s t y - comp n s := by
  have hd : ∀ x, HasDerivAt (fun x => c * rwd n r x t y - comp n x)
      (c * rwDs n r x t y - dcomp n x) x := fun x =>
    ((rw_hasDerivAt_s x t y).const_mul c).sub (comp_hasDerivAt x)
  have hn : ∀ x, c * rwDs n r x t y - dcomp n x ≤ 0 := by
    intro x
    have h1 := rwDs_nonneg (n := n) (r := r) x t y
    have h2 := rwDs_le_dcomp (n := n) (r := r) x t y
    nlinarith
  exact antitone_of_hasDerivAt_nonpos hd hn h

lemma rw_sub_t (s t t' : ℝ) (y : ℕ → ℝ) :
    rwd n r s t' y - rwd n r s t y = ampT (n + 1) s * gate (y n / r n) * (afun t' - afun t) := by
  unfold rwd rewardVal
  ring

lemma sig_mono {v v' : ℝ} (h : v ≤ v') : sig n v ≤ sig n v' :=
  monotone_of_hasDerivAt_nonneg (fun x => sig_hasDerivAt (n := n) x) (fun x => dsig_nonneg x) h

lemma phi_of_mem {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) : phi t = t + 3 / 2 := by
  unfold phi rr
  rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), pos_of_nonpos (by linarith),
    pos_of_nonpos (by linarith)]
  ring

lemma phi_mono {a b : ℝ} (h : a ≤ b) : phi a ≤ phi b :=
  monotone_of_hasDerivAt_nonneg phi_hasDerivAt dphi_nonneg h

lemma alphaSeq_of_nonpos {s : ℝ} (hs : s ≤ 0) (j : ℕ) : alphaSeq (n + 1) s j = 0 := by
  unfold alphaSeq
  rw [amp_of_le (le_trans hs (cum_nonneg _ _)), mul_zero]

lemma rw_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) (y : ℕ → ℝ) : rwd n r s t y = 0 := by
  have hα := alphaSeq_of_nonpos (n := n) hs
  have hT : ampT (n + 1) s = 0 := ampT_of_le (le_trans hs (cum_nonneg _ _))
  unfold rwd rewardVal
  simp only [hα, hT, zero_mul, Finset.sum_const_zero, add_zero]

lemma rwGrad_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) (y : ℕ → ℝ) (k : ℕ) :
    rwGrad n r s t y k = 0 := by
  have hα := alphaSeq_of_nonpos (n := n) hs
  have hT : ampT (n + 1) s = 0 := ampT_of_le (le_trans hs (cum_nonneg _ _))
  unfold rwGrad rewardGrad cval
  simp only [hα, hT, zero_mul, zero_div, ite_self, add_zero]

lemma rwDs_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) (y : ℕ → ℝ) : rwDs n r s t y = 0 := by
  have hd : ∀ j, damp (n + 1) j s = 0 := fun j => damp_of_le (le_trans hs (cum_nonneg _ _))
  have hT : dampT (n + 1) s = 0 := dampT_of_le (le_trans hs (cum_nonneg _ _))
  unfold rwDs
  simp only [hd, hT, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

lemma rwDt_of_nonpos {s : ℝ} (hs : s ≤ 0) (t : ℝ) (y : ℕ → ℝ) : rwDt n r s t y = 0 := by
  have hT : ampT (n + 1) s = 0 := ampT_of_le (le_trans hs (cum_nonneg _ _))
  unfold rwDt
  rw [hT, zero_mul, zero_mul]

lemma rwGrad_sq_le (S : Scales n r ρ) (s t : ℝ) (y : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), rwGrad n r s t y k ^ 2 ≤ 2 ^ 16 * s ^ 2 := by
  have h := rwGrad_lip S 0 s t t y y
  have hz : ∀ k, rwGrad n r 0 t y k = 0 := fun k => rwGrad_of_nonpos le_rfl t y k
  simp only [hz, sub_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero] at h
  exact h

end Block

section Congr

variable {n : ℕ} {r : ℕ → ℝ}

lemma gate_small {a ρ' : ℝ} (hr : 0 < ρ') (h : a ≤ ρ') : gate (a / ρ') = 0 :=
  gate_of_le ((div_le_one hr).mpr h)

lemma dgate_small {a ρ' : ℝ} (hr : 0 < ρ') (h : a ≤ ρ') : dgate (a / ρ') = 0 :=
  dgate_of_le ((div_le_one hr).mpr h)

lemma gprev_congr {y y' : ℕ → ℝ} {J k : ℕ} (hag : ∀ j, j ≤ J → y j = y' j) (hk : k ≤ J) :
    gprev r y k = gprev r y' k := by
  unfold gprev
  by_cases h0 : k = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0, hag (k - 1) (by omega)]

lemma gprev_dead {y : ℕ → ℝ} {J k : ℕ} (hr : ∀ j, j ≤ n → 0 < r j)
    (hy : ∀ j, J ≤ j → j ≤ n → y j ≤ r j) (hJk : J < k) (hk : k ≤ n) : gprev r y k = 0 := by
  unfold gprev
  rw [ite_eq_right (by omega)]
  exact gate_small (hr (k - 1) (by omega)) (hy (k - 1) (by omega) (by omega))

theorem rw_congr {y y' : ℕ → ℝ} {J : ℕ} (hJ : J ≤ n) (hr : ∀ j, j ≤ n → 0 < r j)
    (hag : ∀ j, j ≤ J → y j = y' j) (hy : ∀ j, J ≤ j → j ≤ n → y j ≤ r j)
    (hy' : ∀ j, J ≤ j → j ≤ n → y' j ≤ r j) (s t t' : ℝ) :
    rwd n r s t y = rwd n r s t' y' ∧ rwDs n r s t y = rwDs n r s t' y' ∧
      rwDt n r s t y = 0 ∧ rwDt n r s t' y' = 0 ∧
      (∀ k, k ≤ n → rwGrad n r s t y k = rwGrad n r s t' y' k) ∧
      (∀ k, J < k → k ≤ n → rwGrad n r s t y k = 0) := by
  have hgn : gate (y n / r n) = 0 := gate_small (hr n le_rfl) (hy n hJ le_rfl)
  have hgn' : gate (y' n / r n) = 0 := gate_small (hr n le_rfl) (hy' n hJ le_rfl)
  have hterm : ∀ (c : ℕ → ℝ), ∀ j ∈ Finset.range (n + 1),
      c j * gprev r y j * push (y j / r j) = c j * gprev r y' j * push (y' j / r j) := by
    intro c j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjJ : j ≤ J
    · rw [gprev_congr hag hjJ, hag j hjJ]
    · rw [gprev_dead hr hy (by omega) hjn, gprev_dead hr hy' (by omega) hjn]
      simp only [mul_zero, zero_mul]
  have hzero : ∀ (t0 : ℝ) (z : ℕ → ℝ), (∀ j, J ≤ j → j ≤ n → z j ≤ r j) → ∀ k, J < k → k ≤ n →
      rwGrad n r s t0 z k = 0 := by
    intro t0 z hz k hJk hk
    unfold rwGrad rewardGrad
    rw [gprev_dead hr hz hJk hk, dgate_small (hr k hk) (hz k hJk.le hk)]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hzero t y hy⟩
  · unfold rwd rewardVal
    rw [hgn, hgn', mul_zero, mul_zero, add_zero, add_zero]
    exact Finset.sum_congr rfl (hterm _)
  · unfold rwDs
    rw [hgn, hgn', mul_zero, mul_zero, add_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have h := hterm (fun j => wt (n + 1) j * damp (n + 1) j s) j hj
    exact h
  · unfold rwDt
    rw [hgn, mul_zero]
  · unfold rwDt
    rw [hgn', mul_zero]
  · intro k hk
    rcases lt_trichotomy k J with hkJ | hkJ | hkJ
    · unfold rwGrad rewardGrad cval
      have hkn : k < n := by omega
      rw [ite_eq_left hkn, ite_eq_left hkn, gprev_congr hag hkJ.le, hag k hkJ.le,
        hag (k + 1) (by omega)]
    · unfold rwGrad rewardGrad
      rw [gprev_congr hag hkJ.le, hag k hkJ.le,
        dgate_small (hr k hk) (hy' k hkJ.ge hk)]
      ring
    · rw [hzero t y hy k hkJ hk, hzero t' y' hy' k hkJ hk]

lemma rwGrad_small {y : ℕ → ℝ} {k : ℕ} (hr : 0 < r k) (hyk : y k ≤ r k)
    (s t : ℝ) : |rwGrad n r s t y k| ≤ wt (n + 1) k / (3 * r k) := by
  unfold rwGrad rewardGrad
  rw [dgate_small hr hyk, mul_zero, zero_div, add_zero]
  have h1 := alphaSeq_nonneg (N := n + 1) s k
  have h2 := alphaSeq_le_wt (n := n) s k
  have h3 := gprev_nonneg r y k
  have h4 := gprev_le_one r y k
  have h5 := dpush_nonneg (y k / r k)
  have h6 := dpush_le (y k / r k)
  have hnn : 0 ≤ alphaSeq (n + 1) s k * gprev r y k * dpush (y k / r k) / r k :=
    div_nonneg (mul_nonneg (mul_nonneg h1 h3) h5) hr.le
  rw [abs_of_nonneg hnn, div_le_div_iff₀ hr (by positivity)]
  have h7 : alphaSeq (n + 1) s k * gprev r y k ≤ wt (n + 1) k :=
    (mul_le_of_le_one_right h1 h4).trans h2
  have h8 : alphaSeq (n + 1) s k * gprev r y k * dpush (y k / r k) ≤ wt (n + 1) k * (1 / 3) :=
    mul_le_mul h7 h6 h5 (wt_pos k).le
  nlinarith

end Congr

end LongTails.Proofs.NcPlChainPL
