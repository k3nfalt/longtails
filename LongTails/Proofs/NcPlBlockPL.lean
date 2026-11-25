import LongTails.Proofs.NcPlProfiles
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace LongTails.Proofs.NcPlBlockPL

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlProfiles

noncomputable def gprev (r y : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else gate (y (j - 1) / r (j - 1))

noncomputable def chat (n : ℕ) (α : ℕ → ℝ) (β : ℝ) (j : ℕ) : ℝ :=
  if j < n then α (j + 1) else β

noncomputable def cval (n : ℕ) (α : ℕ → ℝ) (β : ℝ) (r y : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < n then α (j + 1) * push (y (j + 1) / r (j + 1)) else β

noncomputable def blockVal (n : ℕ) (lam Lam r0 : ℝ) (α : ℕ → ℝ) (β : ℝ) (r y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (α j * gprev r y j * push (y j / r j) - lam * y j ^ 2 / 2 -
    Lam / 2 * pos (-y j - r0 / 2) ^ 2) + β * gate (y n / r n)

noncomputable def blockGrad (n : ℕ) (lam Lam r0 : ℝ) (α : ℕ → ℝ) (β : ℝ) (r y : ℕ → ℝ)
    (k : ℕ) : ℝ :=
  α k * gprev r y k * dpush (y k / r k) / r k - lam * y k + Lam * pos (-y k - r0 / 2) +
    cval n α β r y k * dgate (y k / r k) / r k

lemma gprev_nonneg (r y : ℕ → ℝ) (j : ℕ) : 0 ≤ gprev r y j := by
  unfold gprev
  split_ifs
  · exact zero_le_one
  · exact gate_nonneg _

lemma gprev_le_one (r y : ℕ → ℝ) (j : ℕ) : gprev r y j ≤ 1 := by
  unfold gprev
  split_ifs
  · exact le_rfl
  · exact gate_le_one _

lemma gprev_succ (r y : ℕ → ℝ) (j : ℕ) : gprev r y (j + 1) = gate (y j / r j) := by
  simp [gprev]

lemma cval_nonneg {n : ℕ} {α : ℕ → ℝ} {β : ℝ} (hα : ∀ j, j ≤ n → 0 ≤ α j) (hβ : 0 ≤ β)
    (r y : ℕ → ℝ) (j : ℕ) : 0 ≤ cval n α β r y j := by
  unfold cval
  split_ifs with h
  · exact mul_nonneg (hα _ h) (push_nonneg _)
  · exact hβ

lemma cval_le_chat {n : ℕ} {α : ℕ → ℝ} {β : ℝ} (hα : ∀ j, j ≤ n → 0 ≤ α j)
    (r y : ℕ → ℝ) (j : ℕ) : cval n α β r y j ≤ chat n α β j := by
  unfold cval chat
  split_ifs with h
  · exact mul_le_of_le_one_right (hα _ h) (push_le_one _)
  · exact le_rfl

lemma chat_nonneg {n : ℕ} {α : ℕ → ℝ} {β : ℝ} (hα : ∀ j, j ≤ n → 0 ≤ α j) (hβ : 0 ≤ β)
    (j : ℕ) : 0 ≤ chat n α β j := by
  unfold chat
  split_ifs with h
  · exact hα _ h
  · exact hβ

lemma blockVal_eq (n : ℕ) (lam Lam r0 : ℝ) (α : ℕ → ℝ) (β : ℝ) (r y : ℕ → ℝ) :
    blockVal n lam Lam r0 α β r y =
      ∑ j ∈ Finset.range (n + 1), hpot lam Lam r0 (α j) (r j) (y j) -
        ∑ j ∈ Finset.range (n + 1), (1 - gate (y j / r j)) * cval n α β r y j + β := by
  have h1 : ∑ j ∈ Finset.range (n + 1), (1 - gate (y j / r j)) * cval n α β r y j =
      ∑ j ∈ Finset.range n, (1 - gate (y j / r j)) * (α (j + 1) * push (y (j + 1) / r (j + 1))) +
        (1 - gate (y n / r n)) * β := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [cval, ite_eq_left (Finset.mem_range.mp hj)]
    · rw [cval, ite_eq_right (lt_irrefl n)]
  have h2 : ∑ j ∈ Finset.range (n + 1), α j * (1 - gprev r y j) * push (y j / r j) =
      ∑ j ∈ Finset.range n, (1 - gate (y j / r j)) * (α (j + 1) * push (y (j + 1) / r (j + 1))) := by
    rw [Finset.sum_range_succ']
    have e0 : α 0 * (1 - gprev r y 0) * push (y 0 / r 0) = 0 := by simp [gprev]
    rw [e0, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [gprev_succ]
    ring
  have h3 : ∑ j ∈ Finset.range (n + 1), (α j * gprev r y j * push (y j / r j) -
      lam * y j ^ 2 / 2 - Lam / 2 * pos (-y j - r0 / 2) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), hpot lam Lam r0 (α j) (r j) (y j) -
        ∑ j ∈ Finset.range (n + 1), α j * (1 - gprev r y j) * push (y j / r j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold hpot
    ring
  unfold blockVal
  rw [h3, h1, h2]
  ring

lemma tail_bound {lam Lam r0 α r g c v : ℝ} (hlam : 0 < lam) (hlL : lam ≤ Lam) (hr0 : 0 ≤ r0)
    (hα : 0 ≤ α) (hr : 0 < r) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hc : 0 ≤ c)
    (hstrong : 0 < c → 24 * lam * r ^ 2 ≤ α) (w : ℝ) :
    hpot lam Lam r0 α r w - hpot lam Lam r0 α r v ≤
      3 * α + (α * g * dpush (v / r) / r - lam * v + Lam * pos (-v - r0 / 2) +
        c * dgate (v / r) / r) ^ 2 / lam := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlL
  have hw := hpot_le_amp (r0 := r0) (r := r) hlam.le hLam.le hα w
  set d := α * g * dpush (v / r) / r - lam * v + Lam * pos (-v - r0 / 2) +
    c * dgate (v / r) / r with hd
  have hd2 : 0 ≤ d ^ 2 / lam := by positivity
  rcases le_or_gt (3 * r) v with h3 | h3
  · have hu : 3 ≤ v / r := by rw [le_div_iff₀ hr]; linarith
    have hp : pos (-v - r0 / 2) = 0 := pos_of_nonpos (by nlinarith)
    have hdv : d = -(lam * v) := by
      rw [hd, dpush_of_ge hu, dgate_of_ge (by linarith), hp]
      ring
    have hv : hpot lam Lam r0 α r v = α - lam * v ^ 2 / 2 := by
      rw [hpot, push_of_ge hu, hp]
      ring
    have e : d ^ 2 / lam = lam * v ^ 2 := by
      rw [hdv]
      field_simp
    rw [hv, e]
    nlinarith [mul_nonneg hlam.le (sq_nonneg v)]
  · rcases le_or_gt v 0 with h0 | h0
    · have hu : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hr.le
      set p := pos (-v - r0 / 2) with hp
      have hp0 : 0 ≤ p := pos_nonneg _
      have hA : 0 ≤ α * g * dpush (v / r) / r :=
        div_nonneg (mul_nonneg (mul_nonneg hα hg0) (dpush_nonneg _)) hr.le
      have hdv : d = α * g * dpush (v / r) / r + lam * (-v) + Lam * p := by
        rw [hd, dgate_of_le (by linarith)]
        ring
      have hB : 0 ≤ lam * (-v) := by nlinarith
      have hC : 0 ≤ Lam * p := mul_nonneg hLam.le hp0
      have e1 : d ^ 2 = (lam * (-v)) ^ 2 + (Lam * p) ^ 2 +
          ((α * g * dpush (v / r) / r) ^ 2 + 2 * (α * g * dpush (v / r) / r * (lam * (-v))) +
            2 * (α * g * dpush (v / r) / r * (Lam * p)) + 2 * (lam * (-v) * (Lam * p))) := by
        rw [hdv]; ring
      have hsq : (lam * (-v)) ^ 2 + (Lam * p) ^ 2 ≤ d ^ 2 := by
        have := sq_nonneg (α * g * dpush (v / r) / r)
        have := mul_nonneg hA hB
        have := mul_nonneg hA hC
        have := mul_nonneg hB hC
        linarith
      have hv : α * push (v / r) - lam * v ^ 2 / 2 - Lam / 2 * p ^ 2 = hpot lam Lam r0 α r v := rfl
      have hpn := mul_nonneg hα (push_nonneg (v / r))
      have hq : lam * v ^ 2 / 2 + Lam / 2 * p ^ 2 ≤ d ^ 2 / lam := by
        rw [le_div_iff₀ hlam]
        have h1 : lam * (Lam * p ^ 2) ≤ Lam * (Lam * p ^ 2) :=
          mul_le_mul_of_nonneg_right hlL (mul_nonneg hLam.le (sq_nonneg p))
        have e2 : (lam * v ^ 2 / 2 + Lam / 2 * p ^ 2) * lam =
            (lam * (-v)) ^ 2 / 2 + lam * (Lam * p ^ 2) / 2 := by ring
        have e3 : (Lam * p) ^ 2 = Lam * (Lam * p ^ 2) := by ring
        have h5 := sq_nonneg (lam * (-v))
        have h6 : 0 ≤ Lam * (Lam * p ^ 2) := mul_nonneg hLam.le (mul_nonneg hLam.le (sq_nonneg p))
        rw [e2]
        linarith
      linarith
    · have hpz : pos (-v - r0 / 2) = 0 := pos_of_nonpos (by linarith)
      have hv : hpot lam Lam r0 α r v = α * push (v / r) - lam * v ^ 2 / 2 := by
        rw [hpot, hpz]
        ring
      have hpn := mul_nonneg hα (push_nonneg (v / r))
      by_cases hs : 24 * lam * r ^ 2 ≤ α
      · have hq : lam * v ^ 2 / 2 ≤ 9 / 2 * (lam * r ^ 2) := by
          nlinarith [mul_self_le_mul_self h0.le h3.le]
        rw [hv]
        linarith
      · have hc0 : c = 0 := by
          by_contra hne
          exact hs (hstrong (lt_of_le_of_ne hc (Ne.symm hne)))
        have hdv : d = α * g * dpush (v / r) / r - lam * v := by
          rw [hd, hc0, hpz]
          ring
        have h1 := hpot_sub_of_nonneg hlam hLam.le hr0 hα hr h0.le w
        set dh := dhpot lam Lam r0 α r v with hdh
        have hdhv : dh = d + α * (1 - g) * dpush (v / r) / r := by
          rw [hdh, dhpot, hpz, hdv]
          ring
        have hx0 : 0 ≤ α * (1 - g) * dpush (v / r) / r :=
          div_nonneg (mul_nonneg (mul_nonneg hα (by linarith)) (dpush_nonneg _)) hr.le
        have hx1 : α * (1 - g) * dpush (v / r) / r ≤ α / (3 * r) := by
          rw [div_le_div_iff₀ hr (by positivity)]
          have := dpush_le (v / r)
          have h2 : α * (1 - g) * dpush (v / r) ≤ α * (1 / 3) := by
            have hα1 : α * (1 - g) ≤ α := by nlinarith
            calc α * (1 - g) * dpush (v / r) ≤ α * (1 - g) * (1 / 3) :=
                  mul_le_mul_of_nonneg_left this (mul_nonneg hα (by linarith))
              _ ≤ α * (1 / 3) := by nlinarith
          nlinarith
        have hx2 : (α / (3 * r)) ^ 2 ≤ 8 / 3 * α * lam := by
          rw [div_pow, div_le_iff₀ (by positivity)]
          have hlt : α < 24 * lam * r ^ 2 := not_le.mp hs
          nlinarith [mul_nonneg hα hlam.le, sq_nonneg r, mul_le_mul_of_nonneg_left hlt.le hα,
            sq_nonneg α]
        obtain ⟨x, hx⟩ : ∃ x, x = α * (1 - g) * dpush (v / r) / r := ⟨_, rfl⟩
        rw [← hx] at hdhv hx0 hx1
        have hxx : x ^ 2 ≤ (α / (3 * r)) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
        have e5 : (d + x) ^ 2 = 2 * d ^ 2 + 2 * x ^ 2 - (d - x) ^ 2 := by ring
        have hsq : dh ^ 2 ≤ 2 * d ^ 2 + 2 * (α / (3 * r)) ^ 2 := by
          rw [hdhv, e5]
          linarith [sq_nonneg (d - x)]
        have hαl := mul_nonneg hα hlam.le
        have hfin : dh ^ 2 / (2 * lam) ≤ 3 * α + d ^ 2 / lam := by
          rw [div_le_iff₀ (by positivity)]
          have hc : d ^ 2 / lam * lam = d ^ 2 := div_mul_cancel₀ _ hlam.ne'
          have e : (3 * α + d ^ 2 / lam) * (2 * lam) = 6 * α * lam + 2 * d ^ 2 := by
            linear_combination 2 * hc
          rw [e]
          linarith
        linarith

theorem block_pl {n : ℕ} {lam Lam r0 : ℝ} {α : ℕ → ℝ} {β : ℝ} {r : ℕ → ℝ}
    (hlam : 0 < lam) (hlL : lam ≤ Lam) (hr0 : 0 < r0) (hr : ∀ j, j ≤ n → r0 ≤ r j)
    (hα : ∀ j, j ≤ n → 0 ≤ α j) (hαL : ∀ j, j ≤ n → α j ≤ 3 * Lam * r j ^ 2) (hβ : 0 ≤ β)
    (H1 : ∀ j, j ≤ n → 0 < chat n α β j → 24 * lam * r j ^ 2 ≤ α j)
    (H2 : ∀ J, J ≤ n → 0 < chat n α β J →
      ∑ k ∈ Finset.range (n + 1), (if J ≤ k then chat n α β k else 0) ≤
        α J ^ 2 / (lam * r J ^ 2))
    (y y' : ℕ → ℝ) :
    blockVal n lam Lam r0 α β r y' - blockVal n lam Lam r0 α β r y ≤
      147 / lam * ∑ k ∈ Finset.range (n + 1), blockGrad n lam Lam r0 α β r y k ^ 2 := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlL
  have hrpos : ∀ j, j ≤ n → 0 < r j := fun j hj => lt_of_lt_of_le hr0 (hr j hj)
  set G : ℕ → ℝ := fun k => gate (y k / r k) with hG
  set c : ℕ → ℝ := fun k => cval n α β r y k with hcdef
  set ch : ℕ → ℝ := fun k => chat n α β k with hchdef
  set d : ℕ → ℝ := fun k => blockGrad n lam Lam r0 α β r y k with hddef
  set e : ℕ → ℝ := fun k => hpot lam Lam r0 (α k) (r k) (y' k) - hpot lam Lam r0 (α k) (r k) (y k)
    with hedef
  suffices hmain : blockVal n lam Lam r0 α β r y' - blockVal n lam Lam r0 α β r y ≤
      147 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 from hmain
  have hc0 : ∀ k, 0 ≤ c k := fun k => cval_nonneg hα hβ r y k
  have hcle : ∀ k, c k ≤ ch k := fun k => cval_le_chat hα r y k
  have hch0 : ∀ k, 0 ≤ ch k := fun k => chat_nonneg hα hβ k
  have hG0 : ∀ k, 0 ≤ G k := fun k => gate_nonneg _
  have hG1 : ∀ k, G k ≤ 1 := fun k => gate_le_one _
  have hdiff : blockVal n lam Lam r0 α β r y' - blockVal n lam Lam r0 α β r y ≤
      ∑ k ∈ Finset.range (n + 1), (e k + (1 - G k) * c k) := by
    rw [blockVal_eq, blockVal_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hnn : 0 ≤ ∑ j ∈ Finset.range (n + 1), (1 - gate (y' j / r j)) * cval n α β r y' j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by linarith [gate_le_one (y' j / r j)])
        (cval_nonneg hα hβ r y' j))
    linarith
  have hprev : ∀ k, k ≤ n → α k * (1 - gprev r y k) = 0 ∨
      (∃ j, j + 1 = k ∧ α k * (1 - gprev r y k) = ch j * (1 - G j)) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · left
      rw [h0]
      simp [gprev]
    · right
      refine ⟨k - 1, Nat.sub_add_cancel h0, ?_⟩
      have hlt : k - 1 < n := by omega
      simp only [hchdef, hG, chat, ite_eq_left hlt, gprev, ite_eq_right (Nat.pos_iff_ne_zero.mp h0),
        Nat.sub_add_cancel h0]
  have exact_coord : ∀ k, k ≤ n → (∀ j, j ≤ k → ch j * (1 - G j) = 0) →
      d k = dhpot lam Lam r0 (α k) (r k) (y k) ∧ (1 - G k) * c k = 0 := by
    intro k hk hz
    have hzk := hz k le_rfl
    have hck : c k * dgate (y k / r k) = 0 ∧ (1 - G k) * c k = 0 := by
      rcases mul_eq_zero.mp hzk with h | h
      · have : c k = 0 := le_antisymm (h ▸ hcle k) (hc0 k)
        rw [this]
        simp
      · have hG1' : gate (y k / r k) = 1 := by
          have : G k = 1 := by linarith
          exact this
        rw [dgate_eq_zero_of_gate_eq_one hG1', h]
        simp
    have hpk : α k * (1 - gprev r y k) = 0 := by
      rcases hprev k hk with h | ⟨j, hj, h⟩
      · exact h
      · rw [h]
        exact hz j (by omega)
    refine ⟨?_, hck.2⟩
    have e1 : α k * gprev r y k = α k := by linarith
    simp only [hddef, blockGrad, dhpot]
    rw [e1]
    have e2 : cval n α β r y k * dgate (y k / r k) / r k = 0 := by
      have := hck.1
      simp only [hcdef] at this
      rw [this, zero_div]
    rw [e2]
    ring
  have own_bound : ∀ k, k ≤ n → e k ≤ 5 / (2 * lam) * dhpot lam Lam r0 (α k) (r k) (y k) ^ 2 :=
    fun k hk => hpot_sub_le hlam hlL hr0.le (hα k hk) (hrpos k hk) (hr k hk) (hαL k hk) (y k) (y' k)
  have hcoef : (5 : ℝ) / (2 * lam) ≤ 147 / lam := by
    rw [div_le_div_iff₀ (by positivity) hlam]
    nlinarith
  by_cases hA : ∀ k, k ≤ n → ch k * (1 - G k) = 0
  · refine hdiff.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    obtain ⟨h1, h2⟩ := exact_coord k hkn (fun j hj => hA j (le_trans hj hkn))
    have h3 := own_bound k hkn
    rw [h2, add_zero, h1]
    exact h3.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  · have hex : ∃ k, k ≤ n ∧ ch k * (1 - G k) ≠ 0 := by
      by_contra hne
      apply hA
      intro k hk
      by_contra hc
      exact hne ⟨k, hk, hc⟩
    classical
    let J := Nat.find hex
    have hJ : J ≤ n ∧ ch J * (1 - G J) ≠ 0 := Nat.find_spec hex
    have hJmin : ∀ j, j < J → ch j * (1 - G j) = 0 := by
      intro j hj
      by_contra hne
      exact Nat.find_min hex hj ⟨by omega, hne⟩
    have hchJ : 0 < ch J := by
      rcases (hch0 J).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hJ.2
        rw [← h, zero_mul]
    have hGJ : G J < 1 := by
      rcases (hG1 J).lt_or_eq with h | h
      · exact h
      · exfalso
        apply hJ.2
        rw [h, sub_self, mul_zero]
    have hrJ := hrpos J hJ.1
    have hyJ : y J < 2 * r J := by
      have := lt_two_of_gate_lt_one hGJ
      rwa [div_lt_iff₀ hrJ] at this
    have hstrongJ := H1 J hJ.1 hchJ
    have hdhJ := dhpot_strong_lower hlam.le (hα J hJ.1) hrJ (hr J hJ.1) (hαL J hJ.1) hstrongJ hyJ
    have hpJ : α J * (1 - gprev r y J) = 0 := by
      rcases hprev J hJ.1 with h | ⟨j, hj, h⟩
      · exact h
      · rw [h]
        exact hJmin j (by omega)
    have hdJ : d J = dhpot lam Lam r0 (α J) (r J) (y J) + c J * dgate (y J / r J) / r J := by
      have e1 : α J * gprev r y J = α J := by linarith
      simp only [hddef, blockGrad, dhpot]
      rw [e1]
    have hextra : 0 ≤ c J * dgate (y J / r J) / r J :=
      div_nonneg (mul_nonneg (hc0 J) (dgate_nonneg _)) hrJ.le
    have hαJ0 : 0 ≤ α J / (6 * r J) := div_nonneg (hα J hJ.1) (by positivity)
    have hdJlow : α J / (6 * r J) ≤ d J := by rw [hdJ]; linarith
    have hdhJ0 : 0 ≤ dhpot lam Lam r0 (α J) (r J) (y J) := le_trans hαJ0 hdhJ
    have hdhle : dhpot lam Lam r0 (α J) (r J) (y J) ≤ d J := by rw [hdJ]; linarith
    have hDJ : α J ^ 2 / (lam * r J ^ 2) ≤ 36 / lam * d J ^ 2 := by
      have hα6 : α J ≤ 6 * r J * d J := by
        have := hdJlow
        rw [div_le_iff₀ (by positivity)] at this
        linarith
      have hsq36 : α J ^ 2 ≤ 36 * r J ^ 2 * d J ^ 2 := by
        have := mul_self_le_mul_self (hα J hJ.1) hα6
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      have e3 : 36 / lam * d J ^ 2 * (lam * r J ^ 2) = 36 * r J ^ 2 * d J ^ 2 := by
        field_simp
      rw [e3]
      exact hsq36
    set t : ℕ → ℝ := fun k => if J ≤ k then ch k + (if J < k then 3 * α k else 0) else 0 with ht
    have pointwise : ∀ k, k ≤ n → e k + (1 - G k) * c k ≤ 5 / (2 * lam) * d k ^ 2 + t k := by
      intro k hk
      rcases lt_trichotomy k J with hlt | heq | hgt
      · obtain ⟨h1, h2⟩ := exact_coord k hk (fun j hj => hJmin j (by omega))
        have h3 := own_bound k hk
        rw [h2, h1, add_zero]
        simp only [ht, ite_eq_right (not_le.mpr hlt), add_zero]
        exact h3
      · subst heq
        have h3 := own_bound J hk
        have h4 : dhpot lam Lam r0 (α J) (r J) (y J) ^ 2 ≤ d J ^ 2 := by
          nlinarith [mul_self_le_mul_self hdhJ0 hdhle]
        have h5 : (1 - G J) * c J ≤ ch J := by
          have := hcle J
          nlinarith [hc0 J, hG0 J, hG1 J]
        simp only [ht, ite_eq_left (le_refl J), ite_eq_right (lt_irrefl J), add_zero]
        have h6 : 5 / (2 * lam) * dhpot lam Lam r0 (α J) (r J) (y J) ^ 2 ≤
            5 / (2 * lam) * d J ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
        linarith
      · have hstrongk : 0 < c k → 24 * lam * r k ^ 2 ≤ α k :=
          fun hpos => H1 k hk (lt_of_lt_of_le hpos (hcle k))
        have h3 := tail_bound (r0 := r0) hlam hlL hr0.le (hα k hk) (hrpos k hk)
          (gprev_nonneg r y k) (gprev_le_one r y k) (hc0 k) hstrongk (v := y k) (y' k)
        have h5 : (1 - G k) * c k ≤ ch k := by
          have := hcle k
          nlinarith [hc0 k, hG0 k, hG1 k]
        simp only [ht, ite_eq_left hgt.le, ite_eq_left hgt]
        have h6 : d k ^ 2 / lam ≤ 5 / (2 * lam) * d k ^ 2 := by
          rw [div_le_iff₀ hlam]
          have e : 5 / (2 * lam) * d k ^ 2 * lam = 5 / 2 * d k ^ 2 := by field_simp
          rw [e]
          nlinarith [sq_nonneg (d k)]
        have h7 : hpot lam Lam r0 (α k) (r k) (y' k) - hpot lam Lam r0 (α k) (r k) (y k) ≤
            3 * α k + d k ^ 2 / lam := h3
        linarith
    have hsum_t : ∑ k ∈ Finset.range (n + 1), t k ≤
        4 * ∑ k ∈ Finset.range (n + 1), (if J ≤ k then ch k else 0) := by
      have hshift : ∑ k ∈ Finset.range (n + 1), (if J < k then α k else 0) ≤
          ∑ k ∈ Finset.range (n + 1), (if J ≤ k then ch k else 0) := by
        rw [Finset.sum_range_succ' (fun k => if J < k then α k else 0),
          Finset.sum_range_succ (fun k => if J ≤ k then ch k else 0)]
        have e0 : (if J < 0 then α 0 else 0) = 0 := ite_eq_right (Nat.not_lt_zero J)
        rw [e0, add_zero]
        have hlast : 0 ≤ (if J ≤ n then ch n else 0) := by
          split_ifs
          · exact hch0 n
          · exact le_rfl
        have hle : ∑ k ∈ Finset.range n, (if J < k + 1 then α (k + 1) else 0) ≤
            ∑ k ∈ Finset.range n, (if J ≤ k then ch k else 0) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          by_cases hJk : J ≤ k
          · rw [ite_eq_left (Nat.lt_succ_of_le hJk), ite_eq_left hJk]
            simp only [hchdef, chat, ite_eq_left hkn]
            exact le_rfl
          · rw [ite_eq_right (by omega), ite_eq_right hJk]
        linarith
      have hsplit : ∀ k, t k = (if J ≤ k then ch k else 0) + 3 * (if J < k then α k else 0) := by
        intro k
        simp only [ht]
        by_cases h1 : J ≤ k
        · by_cases h2 : J < k
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ J < k := by omega
          simp [h1, h2]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      linarith
    have hH2 := H2 J hJ.1 hchJ
    have hD0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), (if J ≤ k then ch k else 0) :=
      Finset.sum_nonneg (fun k _ => by
        split_ifs
        · exact hch0 k
        · exact le_rfl)
    have hJmem : J ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hJ.1)
    have hdJsum : d J ^ 2 ≤ ∑ k ∈ Finset.range (n + 1), d k ^ 2 :=
      Finset.single_le_sum (f := fun k => d k ^ 2) (fun k _ => sq_nonneg (d k)) hJmem
    have hS0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), d k ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg (d k))
    calc blockVal n lam Lam r0 α β r y' - blockVal n lam Lam r0 α β r y
        ≤ ∑ k ∈ Finset.range (n + 1), (e k + (1 - G k) * c k) := hdiff
      _ ≤ ∑ k ∈ Finset.range (n + 1), (5 / (2 * lam) * d k ^ 2 + t k) :=
          Finset.sum_le_sum (fun k hk => pointwise k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      _ = 5 / (2 * lam) * ∑ k ∈ Finset.range (n + 1), d k ^ 2 + ∑ k ∈ Finset.range (n + 1), t k := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 5 / (2 * lam) * ∑ k ∈ Finset.range (n + 1), d k ^ 2 + 4 * (36 / lam * d J ^ 2) := by
          have := hsum_t.trans (mul_le_mul_of_nonneg_left (hH2.trans hDJ) (by norm_num))
          linarith
      _ ≤ 147 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 := by
          have e1 : 5 / (2 * lam) * ∑ k ∈ Finset.range (n + 1), d k ^ 2 =
              5 / 2 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 := by
            field_simp
          have e2 : 4 * (36 / lam * d J ^ 2) = 144 / lam * d J ^ 2 := by ring
          have e3 : 147 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 =
              5 / 2 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 +
                144.5 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 := by ring
          rw [e1, e2, e3]
          have h1 : 144 / lam * d J ^ 2 ≤ 144 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 :=
            mul_le_mul_of_nonneg_left hdJsum (by positivity)
          have h2 : 144 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 ≤
              144.5 / lam * ∑ k ∈ Finset.range (n + 1), d k ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hS0
            rw [div_le_div_iff_of_pos_right hlam]
            norm_num
          linarith

theorem block_open {n : ℕ} {lam Lam r0 : ℝ} {α : ℕ → ℝ} {β : ℝ} {r : ℕ → ℝ}
    (hlam : 0 < lam) (hr0 : 0 < r0) (hr : ∀ j, j ≤ n → r0 ≤ r j)
    (hα : ∀ j, j ≤ n → 0 ≤ α j) (hαL : ∀ j, j ≤ n → α j ≤ 3 * Lam * r j ^ 2) (hβ : 0 ≤ β)
    (H1 : ∀ j, j ≤ n → 0 < chat n α β j → 24 * lam * r j ^ 2 ≤ α j)
    (y : ℕ → ℝ) (hzero : ∀ k, k ≤ n → blockGrad n lam Lam r0 α β r y k = 0) :
    ∀ k, k ≤ n → chat n α β k * (1 - gate (y k / r k)) = 0 := by
  have hrpos : ∀ j, j ≤ n → 0 < r j := fun j hj => lt_of_lt_of_le hr0 (hr j hj)
  by_contra hA
  have hex : ∃ k, k ≤ n ∧ chat n α β k * (1 - gate (y k / r k)) ≠ 0 := by
    by_contra hne
    apply hA
    intro k hk
    by_contra hc
    exact hne ⟨k, hk, hc⟩
  classical
  let J := Nat.find hex
  have hJ : J ≤ n ∧ chat n α β J * (1 - gate (y J / r J)) ≠ 0 := Nat.find_spec hex
  have hJmin : ∀ j, j < J → chat n α β j * (1 - gate (y j / r j)) = 0 := by
    intro j hj
    by_contra hne
    exact Nat.find_min hex hj ⟨by omega, hne⟩
  have hchJ : 0 < chat n α β J := by
    rcases (chat_nonneg hα hβ J).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hJ.2
      rw [← h, zero_mul]
  have hGJ : gate (y J / r J) < 1 := by
    rcases (gate_le_one (y J / r J)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hJ.2
      rw [h, sub_self, mul_zero]
  have hrJ := hrpos J hJ.1
  have hyJ : y J < 2 * r J := by
    have := lt_two_of_gate_lt_one hGJ
    rwa [div_lt_iff₀ hrJ] at this
  have hstrongJ := H1 J hJ.1 hchJ
  have hdhJ := dhpot_strong_lower hlam.le (hα J hJ.1) hrJ (hr J hJ.1) (hαL J hJ.1) hstrongJ hyJ
  have hpJ : α J * (1 - gprev r y J) = 0 := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0]
      simp [gprev]
    · have hlt : J - 1 < n := by omega
      have h := hJmin (J - 1) (by omega)
      simp only [chat, ite_eq_left hlt, Nat.sub_add_cancel h0] at h
      simp only [gprev, ite_eq_right (Nat.pos_iff_ne_zero.mp h0)]
      exact h
  have hextra : 0 ≤ cval n α β r y J * dgate (y J / r J) / r J :=
    div_nonneg (mul_nonneg (cval_nonneg hα hβ r y J) (dgate_nonneg _)) hrJ.le
  have hd := hzero J hJ.1
  have e1 : α J * gprev r y J = α J := by linarith
  simp only [blockGrad] at hd
  rw [e1] at hd
  have hdh : dhpot lam Lam r0 (α J) (r J) (y J) =
      α J * dpush (y J / r J) / r J - lam * y J + Lam * pos (-y J - r0 / 2) := rfl
  rw [hdh] at hdhJ
  have hαpos : 0 < α J := by
    have : 0 < 24 * lam * r J ^ 2 := by positivity
    linarith
  have : 0 < α J / (6 * r J) := by positivity
  linarith

end LongTails.Proofs.NcPlBlockPL
