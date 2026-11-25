import LongTails.Proofs.NcPlBlockSmooth

open scoped BigOperators

namespace LongTails.Proofs.NcPlChain

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.NcPlBlockPL LongTails.Proofs.NcPlSchedule LongTails.Proofs.NcPlCalc
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth

section Driver

variable (n : ℕ)

noncomputable def sig (v : ℝ) : ℝ := smax (n + 1) * psi v

noncomputable def dsig (v : ℝ) : ℝ := smax (n + 1) * dpsi v

variable {n}

lemma smax_pos : 0 < smax (n + 1) := by
  unfold smax
  have := cum_nonneg (n + 1) (n + 1)
  linarith

lemma smax_le : smax (n + 1) ≤ 4 := by
  unfold smax
  have := cum_le (Nat.succ_pos n) (le_refl (n + 1))
  linarith

lemma sig_hasDerivAt (v : ℝ) : HasDerivAt (sig n) (dsig n v) v :=
  (psi_hasDerivAt v).const_mul (smax (n + 1))

lemma sig_nonneg (v : ℝ) : 0 ≤ sig n v := mul_nonneg smax_pos.le (psi_nonneg v)

lemma sig_of_le {v : ℝ} (h : v ≤ 1 / 2) : sig n v = 0 := by
  rw [sig, psi_of_le h, mul_zero]

lemma dsig_of_le {v : ℝ} (h : v ≤ 1 / 2) : dsig n v = 0 := by
  rw [dsig, dpsi_of_le h, mul_zero]

lemma sig_of_ge {v : ℝ} (h : 1 ≤ v) : sig n v = smax (n + 1) := by
  rw [sig, psi_of_ge h, mul_one]

lemma dsig_of_ge {v : ℝ} (h : 1 ≤ v) : dsig n v = 0 := by
  rw [dsig, dpsi_of_ge h, mul_zero]

lemma dsig_nonneg (v : ℝ) : 0 ≤ dsig n v := mul_nonneg smax_pos.le (dpsi_nonneg v)

lemma dsig_le (v : ℝ) : dsig n v ≤ 16 := by
  have h1 := dpsi_le v
  have h2 := dpsi_nonneg v
  have h3 := smax_le (n := n)
  have h4 := smax_pos (n := n)
  unfold dsig
  nlinarith

lemma sig_lip (a b : ℝ) : |sig n a - sig n b| ≤ 16 * |a - b| := by
  have h := psi_lipschitz a b
  have e : sig n a - sig n b = smax (n + 1) * (psi a - psi b) := by unfold sig; ring
  rw [e, abs_mul, abs_of_pos smax_pos]
  have h3 := smax_le (n := n)
  have h4 := smax_pos (n := n)
  nlinarith [abs_nonneg (psi a - psi b), abs_nonneg (a - b)]

lemma dsig_lip (a b : ℝ) : |dsig n a - dsig n b| ≤ 256 * |a - b| := by
  have h := dpsi_lipschitz a b
  have e : dsig n a - dsig n b = smax (n + 1) * (dpsi a - dpsi b) := by unfold dsig; ring
  rw [e, abs_mul, abs_of_pos smax_pos]
  have h3 := smax_le (n := n)
  have h4 := smax_pos (n := n)
  nlinarith [abs_nonneg (dpsi a - dpsi b), abs_nonneg (a - b)]

end Driver

section BlockU

variable {n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

noncomputable def blockU (n : ℕ) (r : ℕ → ℝ) (v t : ℝ) (y : ℕ → ℝ) : ℝ := rwd n r (sig n v) t y

noncomputable def blockDv (n : ℕ) (r : ℕ → ℝ) (v t : ℝ) (y : ℕ → ℝ) : ℝ :=
  rwDs n r (sig n v) t y * dsig n v

noncomputable def blockDt (n : ℕ) (r : ℕ → ℝ) (v t : ℝ) (y : ℕ → ℝ) : ℝ := rwDt n r (sig n v) t y

noncomputable def compU (n : ℕ) (v : ℝ) : ℝ := comp n (sig n v)

noncomputable def compDv (n : ℕ) (v : ℝ) : ℝ := dcomp n (sig n v) * dsig n v

lemma blockU_hasDerivAt_v (v t : ℝ) (y : ℕ → ℝ) :
    HasDerivAt (fun x => blockU n r x t y) (blockDv n r v t y) v := by
  have h : HasDerivAt ((fun s => rwd n r s t y) ∘ sig n) (rwDs n r (sig n v) t y * dsig n v) v :=
    HasDerivAt.comp v (rw_hasDerivAt_s (sig n v) t y) (sig_hasDerivAt v)
  exact h

lemma compU_hasDerivAt (v : ℝ) : HasDerivAt (compU n) (compDv n v) v := by
  have h : HasDerivAt (comp n ∘ sig n) (dcomp n (sig n v) * dsig n v) v :=
    HasDerivAt.comp v (comp_hasDerivAt (sig n v)) (sig_hasDerivAt v)
  exact h

lemma rwDs_abs (s t : ℝ) (y : ℕ → ℝ) : |rwDs n r s t y| ≤ 6 := by
  rw [abs_of_nonneg (rwDs_nonneg s t y)]
  exact (rwDs_le_dcomp s t y).trans (dcomp_le s)

lemma rwDs_lip_s (S : Scales n r ρ) (s s' t : ℝ) (y : ℕ → ℝ) :
    |rwDs n r s' t y - rwDs n r s t y| ≤ 32 * |s' - s| := by
  have h := rwDs_lip S s s' t t y y
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Finset.sum_const_zero] at h
  have h2 : (rwDs n r s' t y - rwDs n r s t y) ^ 2 ≤ (32 * |s' - s|) ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num at h ⊢
    linarith
  exact abs_le_of_sq_le_sq h2 (by positivity)

lemma blockDv_lip_v (S : Scales n r ρ) (v v' t : ℝ) (y : ℕ → ℝ) :
    |blockDv n r v' t y - blockDv n r v t y| ≤ 2 ^ 14 * |v' - v| := by
  have h1 := rwDs_lip_s S (sig n v) (sig n v') t y
  have h2 := sig_lip (n := n) v' v
  have h3 := dsig_lip (n := n) v' v
  have h4 := rwDs_abs (n := n) (r := r) (sig n v) t y
  have h5 : |dsig n v'| ≤ 16 := by
    rw [abs_of_nonneg (dsig_nonneg v')]; exact dsig_le v'
  have e : blockDv n r v' t y - blockDv n r v t y =
      (rwDs n r (sig n v') t y - rwDs n r (sig n v) t y) * dsig n v' +
        rwDs n r (sig n v) t y * (dsig n v' - dsig n v) := by
    unfold blockDv; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have a1 : |rwDs n r (sig n v') t y - rwDs n r (sig n v) t y| * |dsig n v'| ≤
      32 * (16 * |v' - v|) * 16 :=
    mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) h5 (abs_nonneg _)
      (by positivity)
  have a2 : |rwDs n r (sig n v) t y| * |dsig n v' - dsig n v| ≤ 6 * (256 * |v' - v|) :=
    mul_le_mul h4 h3 (abs_nonneg _) (by norm_num)
  have := abs_nonneg (v' - v)
  nlinarith

lemma compDv_lip (v v' : ℝ) : |compDv n v' - compDv n v| ≤ 2 ^ 13 * |v' - v| := by
  have h1 := dcomp_lip (n := n) (sig n v) (sig n v')
  have h2 := sig_lip (n := n) v' v
  have h3 := dsig_lip (n := n) v' v
  have h4 : |dcomp n (sig n v)| ≤ 6 := by
    rw [abs_of_nonneg (dcomp_nonneg _)]; exact dcomp_le _
  have h5 : |dsig n v'| ≤ 16 := by
    rw [abs_of_nonneg (dsig_nonneg v')]; exact dsig_le v'
  have e : compDv n v' - compDv n v =
      (dcomp n (sig n v') - dcomp n (sig n v)) * dsig n v' +
        dcomp n (sig n v) * (dsig n v' - dsig n v) := by
    unfold compDv; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have a1 : |dcomp n (sig n v') - dcomp n (sig n v)| * |dsig n v'| ≤
      15 * (16 * |v' - v|) * 16 :=
    mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) h5 (abs_nonneg _)
      (by positivity)
  have a2 : |dcomp n (sig n v)| * |dsig n v' - dsig n v| ≤ 6 * (256 * |v' - v|) :=
    mul_le_mul h4 h3 (abs_nonneg _) (by norm_num)
  have := abs_nonneg (v' - v)
  nlinarith

lemma compU_model (v v' : ℝ) :
    |compU n v' - compU n v - compDv n v * (v' - v)| ≤ 2 ^ 13 * (v' - v) ^ 2 :=
  model_of_lipschitz (by norm_num) compU_hasDerivAt (fun a b => compDv_lip b a) v v'

theorem blockU_model (S : Scales n r ρ) (v v' t t' : ℝ) (y : ℕ → ℝ) :
    |blockU n r v' t' y - blockU n r v t y - blockDv n r v t y * (v' - v) -
      blockDt n r v t y * (t' - t)| ≤ 2 ^ 15 * ((v' - v) ^ 2 + (t' - t) ^ 2) := by
  have h1 := model_of_lipschitz (g := fun x => blockU n r x t y) (g' := fun x => blockDv n r x t y)
    (K := 2 ^ 14) (by norm_num) (fun x => blockU_hasDerivAt_v x t y)
    (fun a b => blockDv_lip_v S b a t y) v v'
  have h2 := model_of_lipschitz (g := fun x => rwd n r (sig n v') x y)
    (g' := fun x => rwDt n r (sig n v') x y) (K := 4) (by norm_num)
    (fun x => rw_hasDerivAt_t (sig n v') x y)
    (fun a b => by
      have := rwDt_lip S (sig n v') (sig n v') b a y y
      simpa using this) t t'
  have h3 := rwDt_lip S (sig n v) (sig n v') t t y y
  simp only [sub_self, abs_zero, mul_zero, add_zero] at h3
  have h4 := sig_lip (n := n) v' v
  have hcross : |(rwDt n r (sig n v') t y - rwDt n r (sig n v) t y) * (t' - t)| ≤
      8 * ((v' - v) ^ 2 + (t' - t) ^ 2) := by
    rw [abs_mul]
    have a := abs_nonneg (v' - v)
    have b := abs_nonneg (t' - t)
    have hx : |rwDt n r (sig n v') t y - rwDt n r (sig n v) t y| ≤ 16 * |v' - v| := h3.trans h4
    have := mul_le_mul_of_nonneg_right hx b
    nlinarith [sq_nonneg (|v' - v| - |t' - t|), sq_abs (v' - v), sq_abs (t' - t)]
  have e : blockU n r v' t' y - blockU n r v t y - blockDv n r v t y * (v' - v) -
      blockDt n r v t y * (t' - t) =
      (blockU n r v' t y - blockU n r v t y - blockDv n r v t y * (v' - v)) +
      (rwd n r (sig n v') t' y - rwd n r (sig n v') t y - rwDt n r (sig n v') t y * (t' - t)) +
      (rwDt n r (sig n v') t y - rwDt n r (sig n v) t y) * (t' - t) := by
    unfold blockU blockDt
    ring
  rw [e]
  have tri := abs_add_three
    (blockU n r v' t y - blockU n r v t y - blockDv n r v t y * (v' - v))
    (rwd n r (sig n v') t' y - rwd n r (sig n v') t y - rwDt n r (sig n v') t y * (t' - t))
    ((rwDt n r (sig n v') t y - rwDt n r (sig n v) t y) * (t' - t))
  have hv2 := sq_nonneg (v' - v)
  have ht2 := sq_nonneg (t' - t)
  nlinarith

end BlockU

section ChainFn

variable {m n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

noncomputable def prevRead (u : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then 2 else u (i - 1)

noncomputable def rhat (m n : ℕ) (r : ℕ → ℝ) (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), blockU n r (prevRead u i) (u i) (w i)

noncomputable def csum (m n : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), compU n (prevRead u i)

noncomputable def gW (n : ℕ) (r : ℕ → ℝ) (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  rwGrad n r (sig n (prevRead u i)) (u i) (w i) j

noncomputable def gUR (m n : ℕ) (r : ℕ → ℝ) (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  blockDt n r (prevRead u k) (u k) (w k) +
    (if k < m then blockDv n r (u k) (u (k + 1)) (w (k + 1)) else 0)

noncomputable def gUC (m n : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ := if k < m then compDv n (u k) else 0

lemma prevRead_zero (u : ℕ → ℝ) : prevRead u 0 = 2 := by simp [prevRead]

lemma prevRead_succ (u : ℕ → ℝ) (i : ℕ) : prevRead u (i + 1) = u i := by simp [prevRead]

lemma sum_prev_sq (u u' : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), (prevRead u' i - prevRead u i) ^ 2 ≤
      ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (fun k => (u' k - u k) ^ 2)]
  simp only [prevRead_zero, prevRead_succ, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero]
  nlinarith [sq_nonneg (u' m - u m)]

lemma shift_sum (A : ℕ → ℝ) (u u' : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), A i * (prevRead u' i - prevRead u i) =
      ∑ k ∈ Finset.range (m + 1), (if k < m then A (k + 1) * (u' k - u k) else 0) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [prevRead_zero, prevRead_succ, sub_self, mul_zero, add_zero, lt_irrefl, ite_false]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ite_eq_left (Finset.mem_range.mp hk)]

theorem rhat_model_u (S : Scales n r ρ) (u u' : ℕ → ℝ) (w : ℕ → ℕ → ℝ) :
    |rhat m n r u' w - rhat m n r u w -
        ∑ k ∈ Finset.range (m + 1), gUR m n r u w k * (u' k - u k)| ≤
      2 ^ 16 * ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |blockU n r (prevRead u' i) (u' i) (w i) - blockU n r (prevRead u i) (u i) (w i) -
        blockDv n r (prevRead u i) (u i) (w i) * (prevRead u' i - prevRead u i) -
        blockDt n r (prevRead u i) (u i) (w i) * (u' i - u i)| ≤
        2 ^ 15 * ((prevRead u' i - prevRead u i) ^ 2 + (u' i - u i) ^ 2) :=
    fun i _ => blockU_model S _ _ _ _ _
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hprev := sum_prev_sq (m := m) u u'
  have hshift := shift_sum (m := m) (fun i => blockDv n r (prevRead u i) (u i) (w i)) u u'
  have hg : ∑ k ∈ Finset.range (m + 1), gUR m n r u w k * (u' k - u k) =
      ∑ i ∈ Finset.range (m + 1),
        blockDv n r (prevRead u i) (u i) (w i) * (prevRead u' i - prevRead u i) +
      ∑ i ∈ Finset.range (m + 1), blockDt n r (prevRead u i) (u i) (w i) * (u' i - u i) := by
    rw [hshift, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold gUR
    by_cases hk : k < m
    · rw [ite_eq_left hk, ite_eq_left hk, prevRead_succ]
      ring
    · rw [ite_eq_right hk, ite_eq_right hk]
      ring
  have e : rhat m n r u' w - rhat m n r u w -
      ∑ k ∈ Finset.range (m + 1), gUR m n r u w k * (u' k - u k) =
      ∑ i ∈ Finset.range (m + 1),
        (blockU n r (prevRead u' i) (u' i) (w i) - blockU n r (prevRead u i) (u i) (w i) -
          blockDv n r (prevRead u i) (u i) (w i) * (prevRead u' i - prevRead u i) -
          blockDt n r (prevRead u i) (u i) (w i) * (u' i - u i)) := by
    rw [hg]
    unfold rhat
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hS0 : 0 ≤ ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith

theorem csum_model (u u' : ℕ → ℝ) :
    |csum m n u' - csum m n u - ∑ k ∈ Finset.range (m + 1), gUC m n u k * (u' k - u k)| ≤
      2 ^ 13 * ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |compU n (prevRead u' i) - compU n (prevRead u i) -
        compDv n (prevRead u i) * (prevRead u' i - prevRead u i)| ≤
        2 ^ 13 * (prevRead u' i - prevRead u i) ^ 2 := fun i _ => compU_model _ _
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum
  have hprev := sum_prev_sq (m := m) u u'
  have hshift := shift_sum (m := m) (fun i => compDv n (prevRead u i)) u u'
  have hg : ∑ k ∈ Finset.range (m + 1), gUC m n u k * (u' k - u k) =
      ∑ i ∈ Finset.range (m + 1), compDv n (prevRead u i) * (prevRead u' i - prevRead u i) := by
    rw [hshift]
    apply Finset.sum_congr rfl
    intro k _
    unfold gUC
    by_cases hk : k < m
    · rw [ite_eq_left hk, ite_eq_left hk, prevRead_succ]
    · rw [ite_eq_right hk, ite_eq_right hk, zero_mul]
  have e : csum m n u' - csum m n u - ∑ k ∈ Finset.range (m + 1), gUC m n u k * (u' k - u k) =
      ∑ i ∈ Finset.range (m + 1), (compU n (prevRead u' i) - compU n (prevRead u i) -
        compDv n (prevRead u i) * (prevRead u' i - prevRead u i)) := by
    rw [hg]
    unfold csum
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [e]
  nlinarith

theorem rhat_model_w (S : Scales n r ρ) (u : ℕ → ℝ) (w w' : ℕ → ℕ → ℝ) :
    |rhat m n r u w' - rhat m n r u w -
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), gW n r u w i j * (w' i j - w i j)| ≤
      104 / ρ ^ 2 * ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (w' i j - w i j) ^ 2 := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      |blockU n r (prevRead u i) (u i) (w' i) - blockU n r (prevRead u i) (u i) (w i) -
        ∑ j ∈ Finset.range (n + 1), gW n r u w i j * (w' i j - w i j)| ≤
        104 / ρ ^ 2 * ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2 := by
    intro i _
    have h := reward_model S (α := alphaSeq (n + 1) (sig n (prevRead u i)))
      (β := ampT (n + 1) (sig n (prevRead u i)) * afun (u i)) (B := 4)
      (fun j _ => alphaSeq_nonneg _ j)
      (fun j _ => (mul_le_of_le_one_right (wt_pos j).le (amp_le_one j _)).trans
        (wt_le_one (Nat.succ_pos n) j))
      (mul_nonneg (ampT_nonneg _) (afun_nonneg _))
      (by
        have h1 := ampT_le_one (N := n + 1) (sig n (prevRead u i))
        have h2 := afun_le (u i)
        have h3 := ampT_nonneg (N := n + 1) (sig n (prevRead u i))
        have h4 := afun_nonneg (u i)
        nlinarith) (w i) (w' i)
    have e : (40 + 16 * (4 : ℝ)) / ρ ^ 2 = 104 / ρ ^ 2 := by norm_num
    rw [e] at h
    exact h
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum
  have e : rhat m n r u w' - rhat m n r u w -
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), gW n r u w i j * (w' i j - w i j) =
      ∑ i ∈ Finset.range (m + 1),
        (blockU n r (prevRead u i) (u i) (w' i) - blockU n r (prevRead u i) (u i) (w i) -
          ∑ j ∈ Finset.range (n + 1), gW n r u w i j * (w' i j - w i j)) := by
    unfold rhat
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [e]
  exact hsum

end ChainFn

section ChainLip

variable {m n : ℕ} {r : ℕ → ℝ} {ρ : ℝ}

lemma shift_le (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    ∑ k ∈ Finset.range (m + 1), (if k < m then a (k + 1) else 0) ≤
      ∑ k ∈ Finset.range (m + 1), a k := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' a]
  simp only [lt_irrefl, ite_false, add_zero]
  have e : ∑ k ∈ Finset.range m, (if k < m then a (k + 1) else 0) =
      ∑ k ∈ Finset.range m, a (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ite_eq_left (Finset.mem_range.mp hk)]
  rw [e]
  linarith [ha 0]

lemma sig_sq_lip (a b : ℝ) : (sig n a - sig n b) ^ 2 ≤ 256 * (a - b) ^ 2 := by
  have h := sig_lip (n := n) a b
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, sq_abs] at h2
  linarith

theorem gW_lip (S : Scales n r ρ) (u u' : ℕ → ℝ) (w w' : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (gW n r u' w' i j - gW n r u w i j) ^ 2 ≤
      2 ^ 25 * (∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 +
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      ∑ j ∈ Finset.range (n + 1), (gW n r u' w' i j - gW n r u w i j) ^ 2 ≤
        2 ^ 16 * (256 * (prevRead u' i - prevRead u i) ^ 2 + (u' i - u i) ^ 2 +
          ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2) := by
    intro i _
    have h := rwGrad_lip S (sig n (prevRead u i)) (sig n (prevRead u' i)) (u i) (u' i) (w i) (w' i)
    have h2 := sig_sq_lip (n := n) (prevRead u' i) (prevRead u i)
    unfold gW
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hprev := sum_prev_sq (m := m) u u'
  have hU0 : 0 ≤ ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hW0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith

lemma blockDt_lip (S : Scales n r ρ) (v v' t t' : ℝ) (y y' : ℕ → ℝ) :
    (blockDt n r v' t' y' - blockDt n r v t y) ^ 2 ≤
      3 * (256 * (v' - v) ^ 2 + 16 * (t' - t) ^ 2 + 4 * (y' n - y n) ^ 2) := by
  have h := rwDt_lip S (sig n v) (sig n v') t t' y y'
  have h2 := sig_lip (n := n) v' v
  have h3 : |blockDt n r v' t' y' - blockDt n r v t y| ≤
      16 * |v' - v| + 4 * |t' - t| + 2 * |y' n - y n| := by
    unfold blockDt
    linarith
  have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [sq_abs] at h4
  have h5 := sq_add3 (16 * |v' - v|) (4 * |t' - t|) (2 * |y' n - y n|)
  have e1 : (16 * |v' - v|) ^ 2 = 256 * (v' - v) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have e2 : (4 * |t' - t|) ^ 2 = 16 * (t' - t) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have e3 : (2 * |y' n - y n|) ^ 2 = 4 * (y' n - y n) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  rw [e1, e2, e3] at h5
  linarith

lemma blockDv_lip (S : Scales n r ρ) (v v' t t' : ℝ) (y y' : ℕ → ℝ) :
    (blockDv n r v' t' y' - blockDv n r v t y) ^ 2 ≤
      2 ^ 19 * (2 ^ 9 * (v' - v) ^ 2 + (t' - t) ^ 2 +
        ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2) := by
  have h1 := rwDs_lip S (sig n v) (sig n v') t t' y y'
  have h2 := sig_sq_lip (n := n) v' v
  have h3 := dsig_lip (n := n) v' v
  have h4 := rwDs_abs (n := n) (r := r) (sig n v) t y
  have h5 : |dsig n v'| ≤ 16 := by
    rw [abs_of_nonneg (dsig_nonneg v')]; exact dsig_le v'
  have hD0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have e : blockDv n r v' t' y' - blockDv n r v t y =
      (rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) * dsig n v' +
        rwDs n r (sig n v) t y * (dsig n v' - dsig n v) := by
    unfold blockDv; ring
  rw [e]
  have a1 : ((rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) * dsig n v') ^ 2 ≤
      2 ^ 10 * (256 * (v' - v) ^ 2 + (t' - t) ^ 2 +
        ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2) * 256 := by
    rw [mul_pow]
    have hd2 : dsig n v' ^ 2 ≤ 256 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h5 2
      rw [sq_abs] at this
      linarith
    have hx : (rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) ^ 2 ≤
        2 ^ 10 * (256 * (v' - v) ^ 2 + (t' - t) ^ 2 +
          ∑ k ∈ Finset.range (n + 1), (y' k - y k) ^ 2) := by
      nlinarith [sq_nonneg (t' - t)]
    exact mul_le_mul hx hd2 (sq_nonneg _) (by positivity)
  have a2 : (rwDs n r (sig n v) t y * (dsig n v' - dsig n v)) ^ 2 ≤ 36 * (65536 * (v' - v) ^ 2) := by
    rw [mul_pow]
    have hr2 : rwDs n r (sig n v) t y ^ 2 ≤ 36 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h4 2
      rw [sq_abs] at this
      linarith
    have hd2 : (dsig n v' - dsig n v) ^ 2 ≤ 65536 * (v' - v) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs, mul_pow, sq_abs] at this
      linarith
    exact mul_le_mul hr2 hd2 (sq_nonneg _) (by norm_num)
  have h6 : ((rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) * dsig n v' +
      rwDs n r (sig n v) t y * (dsig n v' - dsig n v)) ^ 2 ≤
      2 * ((rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) * dsig n v') ^ 2 +
        2 * (rwDs n r (sig n v) t y * (dsig n v' - dsig n v)) ^ 2 := by
    nlinarith [sq_nonneg ((rwDs n r (sig n v') t' y' - rwDs n r (sig n v) t y) * dsig n v' -
      rwDs n r (sig n v) t y * (dsig n v' - dsig n v))]
  have hv2 := sq_nonneg (v' - v)
  have ht2 := sq_nonneg (t' - t)
  nlinarith

theorem gUR_lip (S : Scales n r ρ) (u u' : ℕ → ℝ) (w w' : ℕ → ℕ → ℝ) :
    ∑ k ∈ Finset.range (m + 1), (gUR m n r u' w' k - gUR m n r u w k) ^ 2 ≤
      2 ^ 31 * (∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 +
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2) := by
  set U := ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 with hU
  set W := ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), (w' i j - w i j) ^ 2 with hW
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hterm : ∀ k ∈ Finset.range (m + 1), (gUR m n r u' w' k - gUR m n r u w k) ^ 2 ≤
      6 * (256 * (prevRead u' k - prevRead u k) ^ 2 + 16 * (u' k - u k) ^ 2 +
        4 * ∑ j ∈ Finset.range (n + 1), (w' k j - w k j) ^ 2) +
      2 ^ 20 * (2 ^ 9 * (u' k - u k) ^ 2 +
        (if k < m then (u' (k + 1) - u (k + 1)) ^ 2 +
          ∑ j ∈ Finset.range (n + 1), (w' (k + 1) j - w (k + 1) j) ^ 2 else 0)) := by
    intro k _
    have hdt := blockDt_lip S (prevRead u k) (prevRead u' k) (u k) (u' k) (w k) (w' k)
    have hn : (w' k n - w k n) ^ 2 ≤ ∑ j ∈ Finset.range (n + 1), (w' k j - w k j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (w' k j - w k j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hu2 := sq_nonneg (u' k - u k)
    unfold gUR
    by_cases hk : k < m
    · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
      have hdv := blockDv_lip S (u k) (u' k) (u (k + 1)) (u' (k + 1)) (w (k + 1)) (w' (k + 1))
      have e : blockDt n r (prevRead u' k) (u' k) (w' k) +
          blockDv n r (u' k) (u' (k + 1)) (w' (k + 1)) -
          (blockDt n r (prevRead u k) (u k) (w k) + blockDv n r (u k) (u (k + 1)) (w (k + 1))) =
          (blockDt n r (prevRead u' k) (u' k) (w' k) - blockDt n r (prevRead u k) (u k) (w k)) +
          (blockDv n r (u' k) (u' (k + 1)) (w' (k + 1)) -
            blockDv n r (u k) (u (k + 1)) (w (k + 1))) := by ring
      rw [e]
      have h2 : ((blockDt n r (prevRead u' k) (u' k) (w' k) -
          blockDt n r (prevRead u k) (u k) (w k)) +
          (blockDv n r (u' k) (u' (k + 1)) (w' (k + 1)) -
            blockDv n r (u k) (u (k + 1)) (w (k + 1)))) ^ 2 ≤
          2 * (blockDt n r (prevRead u' k) (u' k) (w' k) -
            blockDt n r (prevRead u k) (u k) (w k)) ^ 2 +
          2 * (blockDv n r (u' k) (u' (k + 1)) (w' (k + 1)) -
            blockDv n r (u k) (u (k + 1)) (w (k + 1))) ^ 2 := by
        nlinarith [sq_nonneg ((blockDt n r (prevRead u' k) (u' k) (w' k) -
          blockDt n r (prevRead u k) (u k) (w k)) -
          (blockDv n r (u' k) (u' (k + 1)) (w' (k + 1)) -
            blockDv n r (u k) (u (k + 1)) (w (k + 1))))]
      have hS0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), (w' k j - w k j) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      nlinarith
    · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, add_zero, add_zero, add_zero]
      have hS0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), (w' k j - w k j) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hprev := sum_prev_sq (m := m) u u'
  have hshift := shift_le (m := m)
    (fun k => (u' k - u k) ^ 2 + ∑ j ∈ Finset.range (n + 1), (w' k j - w k j) ^ 2)
    (fun k => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  rw [Finset.sum_add_distrib] at hshift
  nlinarith

theorem gUC_lip (u u' : ℕ → ℝ) :
    ∑ k ∈ Finset.range (m + 1), (gUC m n u' k - gUC m n u k) ^ 2 ≤
      2 ^ 26 * ∑ k ∈ Finset.range (m + 1), (u' k - u k) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  unfold gUC
  by_cases hk : k < m
  · rw [ite_eq_left hk, ite_eq_left hk]
    have h := compDv_lip (n := n) (u k) (u' k)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    norm_num at h2 ⊢
    linarith
  · rw [ite_eq_right hk, ite_eq_right hk, sub_self]
    nlinarith [sq_nonneg (u' k - u k)]

lemma blockU_nonneg (v t : ℝ) (y : ℕ → ℝ) : 0 ≤ blockU n r v t y := rw_nonneg _ _ _

lemma blockU_le_comp (v t : ℝ) (y : ℕ → ℝ) : blockU n r v t y ≤ compU n v := rw_le_comp _ _ _

lemma compU_nonneg (v : ℝ) : 0 ≤ compU n v := comp_nonneg _

lemma compU_le (v : ℝ) : compU n v ≤ 6 := comp_le _

lemma rhat_nonneg (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) : 0 ≤ rhat m n r u w :=
  Finset.sum_nonneg fun _ _ => blockU_nonneg _ _ _

lemma rhat_le_csum (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) : rhat m n r u w ≤ csum m n u :=
  Finset.sum_le_sum fun _ _ => blockU_le_comp _ _ _

lemma csum_nonneg (u : ℕ → ℝ) : 0 ≤ csum m n u := Finset.sum_nonneg fun _ _ => compU_nonneg _

lemma csum_le (u : ℕ → ℝ) : csum m n u ≤ 6 * ((m : ℝ) + 1) := by
  unfold csum
  have h := Finset.sum_le_sum (s := Finset.range (m + 1)) (fun i _ => compU_le (n := n) (prevRead u i))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h
  linarith

lemma blockDt_abs (v t : ℝ) (y : ℕ → ℝ) : |blockDt n r v t y| ≤ 1 := rwDt_abs _ _ _

lemma blockDv_abs (v t : ℝ) (y : ℕ → ℝ) : |blockDv n r v t y| ≤ 96 := by
  unfold blockDv
  rw [abs_mul]
  have h1 := rwDs_abs (n := n) (r := r) (sig n v) t y
  have h2 : |dsig n v| ≤ 16 := by
    rw [abs_of_nonneg (dsig_nonneg v)]; exact dsig_le v
  nlinarith [abs_nonneg (rwDs n r (sig n v) t y), abs_nonneg (dsig n v)]

lemma gUR_abs (u : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (k : ℕ) : |gUR m n r u w k| ≤ 97 := by
  unfold gUR
  have h1 := blockDt_abs (n := n) (r := r) (prevRead u k) (u k) (w k)
  split_ifs
  · have h2 := blockDv_abs (n := n) (r := r) (u k) (u (k + 1)) (w (k + 1))
    have := abs_add_le (blockDt n r (prevRead u k) (u k) (w k))
      (blockDv n r (u k) (u (k + 1)) (w (k + 1)))
    linarith
  · rw [add_zero]
    linarith

lemma compDv_abs (v : ℝ) : |compDv n v| ≤ 96 := by
  unfold compDv
  rw [abs_mul]
  have h1 : |dcomp n (sig n v)| ≤ 6 := by
    rw [abs_of_nonneg (dcomp_nonneg _)]; exact dcomp_le _
  have h2 : |dsig n v| ≤ 16 := by
    rw [abs_of_nonneg (dsig_nonneg v)]; exact dsig_le v
  nlinarith [abs_nonneg (dcomp n (sig n v)), abs_nonneg (dsig n v)]

lemma gUC_abs (u : ℕ → ℝ) (k : ℕ) : |gUC m n u k| ≤ 96 := by
  unfold gUC
  split_ifs
  · exact compDv_abs _
  · rw [abs_zero]
    norm_num

end ChainLip

end LongTails.Proofs.NcPlChain
