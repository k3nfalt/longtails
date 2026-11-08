import LongTails.Proofs.BirchDelayedCoefficients

namespace LongTails.Proofs.BirchCausalCoefficients

open Finset
open LongTails.Proofs.BirchDelayedCoefficients

noncomputable def residual (a α : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  a - α * ∑ j ∈ range n, c j

lemma residual_zero (a α : ℝ) (c : ℕ → ℝ) : residual a α c 0 = a := by
  simp [residual]

lemma residual_succ (a α : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    residual a α c (n + 1) = residual a α c n - α * c n := by
  simp only [residual, sum_range_succ]
  ring

lemma depletion_bounds (history : ℕ → Finset ℕ) (active : ℕ → Prop)
    [DecidablePred active] (a α : ℝ) (r : ℕ) (c : ℕ → ℝ)
    (ha : 0 ≤ a) (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2)
    (hdelay : 4 * α * (r : ℝ) ≤ 1)
    (hpast : ∀ n, history n ⊆ range n)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hrec : ∀ n, c n = if active n then a - α * ∑ j ∈ history n, c j else 0) :
    ∀ n, 0 ≤ residual a α c n ∧ 0 ≤ c n ∧ c n ≤ a ∧
      c n ≤ 2 * residual a α c n ∧
      (1 - 2 * α) * residual a α c n ≤ residual a α c (n + 1) := by
  have hfactor : 0 ≤ 1 - 2 * α := by linarith
  have hfactor1 : 1 - 2 * α ≤ 1 := by linarith
  have hpower := delay_power_lower α r hsmall hdelay
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hu : 0 ≤ residual a α c n := by
        cases n with
        | zero => simpa [residual] using ha
        | succ k =>
            exact (mul_nonneg hfactor (ih k (by omega)).1).trans
              (ih k (by omega)).2.2.2.2
      have hprior : ∀ j ∈ range n, 0 ≤ c j := by
        intro j hj
        exact (ih j (mem_range.mp hj)).2.1
      have hhistory : 0 ≤ ∑ j ∈ history n, c j :=
        sum_nonneg (fun j hj => hprior j (hpast n hj))
      have hprefix : (∑ j ∈ range (n - r), c j) ≤ ∑ j ∈ history n, c j := by
        exact sum_le_sum_of_subset_of_nonneg (hrecent n)
          (fun j hj _ => hprior j (hpast n hj))
      have hfull : (∑ j ∈ history n, c j) ≤ ∑ j ∈ range n, c j := by
        exact sum_le_sum_of_subset_of_nonneg (hpast n) (fun j hj _ => hprior j hj)
      have hsource : 0 ≤ residual a α c (n - r) := by
        by_cases he : n - r = n
        · simpa [he] using hu
        · exact (ih (n - r) (by omega)).1
      have hsegment := segment_lower (residual a α c) (1 - 2 * α) hfactor
        (n - r) (n - (n - r))
        (fun j _ hj => (ih j (by omega)).2.2.2.2)
      rw [Nat.add_sub_of_le (Nat.sub_le n r)] at hsegment
      have hexp : n - (n - r) ≤ r := by omega
      have hp := pow_le_pow_of_le_one hfactor hfactor1 hexp
      have hhalf := (mul_le_mul_of_nonneg_right (hpower.trans hp) hsource).trans hsegment
      have hratio : residual a α c (n - r) ≤ 2 * residual a α c n := by linarith
      have hc : 0 ≤ c n ∧ c n ≤ a ∧ c n ≤ 2 * residual a α c n := by
        rw [hrec n]
        split_ifs
        · have hlo : residual a α c n ≤ a - α * ∑ j ∈ history n, c j := by
            dsimp [residual]
            nlinarith [mul_le_mul_of_nonneg_left hfull hα]
          have hhi : a - α * ∑ j ∈ history n, c j ≤ residual a α c (n - r) := by
            dsimp [residual]
            nlinarith [mul_le_mul_of_nonneg_left hprefix hα]
          exact ⟨hu.trans hlo, sub_le_self _ (mul_nonneg hα hhistory), hhi.trans hratio⟩
        · exact ⟨le_rfl, ha, by linarith⟩
      refine ⟨hu, hc.1, hc.2.1, hc.2.2, ?_⟩
      rw [residual_succ]
      nlinarith [mul_le_mul_of_nonneg_left hc.2.2 hα]

lemma residual_antitone (a α : ℝ) (c : ℕ → ℝ) (hα : 0 ≤ α)
    (hc : ∀ n, 0 ≤ c n) : Antitone (residual a α c) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [residual_succ]
  exact sub_le_self _ (mul_nonneg hα (hc n))

lemma depletion_tail (history : ℕ → Finset ℕ) (a α : ℝ) (c : ℕ → ℝ)
    (cutoff : ℕ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hpast : ∀ n, history n ⊆ range n) (hc : ∀ n, 0 ≤ c n)
    (hrec : ∀ n, cutoff ≤ n → c n = a - α * ∑ j ∈ history n, c j) :
    ∀ n, residual a α c (cutoff + n) ≤
      (1 - α) ^ n * residual a α c cutoff := by
  have hstep (n : ℕ) (hn : cutoff ≤ n) :
      residual a α c (n + 1) ≤ (1 - α) * residual a α c n := by
    have hs : (∑ j ∈ history n, c j) ≤ ∑ j ∈ range n, c j :=
      sum_le_sum_of_subset_of_nonneg (hpast n) (fun j _ _ => hc j)
    have hlo : residual a α c n ≤ c n := by
      rw [hrec n hn]
      dsimp [residual]
      nlinarith [mul_le_mul_of_nonneg_left hs hα]
    rw [residual_succ]
    nlinarith [mul_le_mul_of_nonneg_left hlo hα]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 - α by linarith)
      have hs := hstep (cutoff + n) (by omega)
      simpa [Nat.add_assoc, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hs.trans hm

def shiftedHistory (history : ℕ → Finset ℕ) (birth n : ℕ) : Finset ℕ :=
  (range n).filter (fun j => birth + j ∈ history (birth + n))

lemma shiftedHistory_past (history : ℕ → Finset ℕ) (birth n : ℕ) :
    shiftedHistory history birth n ⊆ range n := filter_subset _ _

lemma shiftedHistory_recent (history : ℕ → Finset ℕ) (birth r : ℕ)
    (hrecent : ∀ n, range (n - r) ⊆ history n) (n : ℕ) :
    range (n - r) ⊆ shiftedHistory history birth n := by
  intro j hj
  have hj' := mem_range.mp hj
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (by omega), ?_⟩
  exact hrecent (birth + n) (mem_range.mpr (by omega))

lemma sum_shiftedHistory (history : ℕ → Finset ℕ) (birth n : ℕ) (c : ℕ → ℝ)
    (hpast : history (birth + n) ⊆ range (birth + n))
    (hzero : ∀ j, j < birth → c j = 0) :
    (∑ j ∈ shiftedHistory history birth n, c (birth + j)) =
      ∑ j ∈ history (birth + n), c j := by
  let s := (history (birth + n)).filter (birth ≤ ·)
  have hs : (∑ j ∈ s, c j) = ∑ j ∈ history (birth + n), c j := by
    apply sum_subset (filter_subset _ _)
    intro j hj hjs
    have hlt : j < birth := by simpa [s, hj] using hjs
    exact hzero j hlt
  rw [← hs]
  apply sum_bij (fun j _ => birth + j)
  · intro j hj
    obtain ⟨_, hj⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj, Nat.le_add_right _ _⟩
  · intro j₁ _ j₂ _ he
    omega
  · intro j hj
    obtain ⟨hj, hbj⟩ := mem_filter.mp hj
    refine ⟨j - birth, ?_, by omega⟩
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, ?_⟩
    · have := mem_range.mp (hpast hj)
      omega
    · simpa [Nat.add_sub_of_le hbj] using hj
  · intro j _
    rfl

lemma source_zero (history : ℕ → Finset ℕ) (q : ℕ) (α : ℝ) (c : ℕ → ℝ)
    (hpast : ∀ n, history n ⊆ range n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (hrec : ∀ n, c n = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, c j) :
    ∀ n, q ∉ history n → c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rw [hrec n, ite_eq_right hn]
      have hs : (∑ j ∈ history n, c j) = 0 := by
        apply sum_eq_zero
        intro j hj
        exact ih j (mem_range.mp (hpast n hj)) (fun hq => hn (hclosed n j hj hq))
      simp [hs]

lemma source_nonnegative_cap (history : ℕ → Finset ℕ) (q r : ℕ) (α : ℝ)
    (c : ℕ → ℝ) (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2)
    (hdelay : 4 * α * (r : ℝ) ≤ 1)
    (hpast : ∀ n, history n ⊆ range n)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n)
    (hrec : ∀ n, c n = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, c j) :
    ∀ n, 0 ≤ c n ∧ c n ≤ α := by
  have hz := source_zero history q α c hpast hclosed hrec
  have hbefore (n : ℕ) (hn : n < q + 1) : c n = 0 := by
    apply hz n
    intro hq
    have := mem_range.mp (hpast n hq)
    omega
  let d := fun n => c (q + 1 + n)
  have hdrec : ∀ n, d n = if q ∈ history (q + 1 + n) then
      α - α * ∑ j ∈ shiftedHistory history (q + 1) n, d j else 0 := by
    intro n
    dsimp only [d]
    rw [sum_shiftedHistory history (q + 1) n c (hpast _) hbefore]
    by_cases hq : q ∈ history (q + 1 + n)
    · rw [ite_eq_left hq, hrec, ite_eq_left hq]
    · rw [ite_eq_right hq, hz _ hq]
  have hb := depletion_bounds (shiftedHistory history (q + 1))
    (fun n => q ∈ history (q + 1 + n)) α α r d hα hα hsmall hdelay
    (shiftedHistory_past history (q + 1))
    (shiftedHistory_recent history (q + 1) r hrecent) hdrec
  intro n
  by_cases hn : n < q + 1
  · rw [hbefore n hn]
    exact ⟨le_rfl, hα⟩
  · have he : q + 1 + (n - (q + 1)) = n := by omega
    exact ⟨by simpa [d, he] using (hb (n - (q + 1))).2.1,
      by simpa [d, he] using (hb (n - (q + 1))).2.2.1⟩

lemma sum_source_births (s : Finset ℕ) (N : ℕ) (α : ℝ) (hs : s ⊆ range N) :
    (∑ q ∈ range N, if q ∈ s then α else 0) = (s.card : ℝ) * α := by
  have he : (∑ q ∈ s, if q ∈ s then α else 0) =
      ∑ q ∈ range N, if q ∈ s then α else 0 := by
    apply sum_subset hs
    intro q _ hq
    simp [hq]
  rw [← he]
  simp

lemma coefficient_mass (history : ℕ → Finset ℕ) (α : ℝ) (initial : ℕ → ℝ)
    (source : ℕ → ℕ → ℝ) (hpast : ∀ n, history n ⊆ range n)
    (hi : ∀ n, initial n = 1 - α * ∑ j ∈ history n, initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, source j q) :
    ∀ n N, n ≤ N → initial n + ∑ q ∈ range N, source n q = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro N hn
      have hsub : history n ⊆ range N := (hpast n).trans (range_mono hn)
      have hbirth := sum_source_births (history n) N α hsub
      have hsource : (∑ q ∈ range N, source n q) =
          (history n).card * α - α * ∑ j ∈ history n, ∑ q ∈ range N, source j q := by
        simp_rw [hs n]
        rw [sum_sub_distrib, hbirth, ← mul_sum, sum_comm]
      have hmass : (∑ j ∈ history n, (initial j + ∑ q ∈ range N, source j q)) =
          ((history n).card : ℝ) := by
        calc
          _ = ∑ j ∈ history n, (1 : ℝ) := by
            apply sum_congr rfl
            intro j hj
            exact ih j (mem_range.mp (hpast n hj)) N (by
              have := mem_range.mp (hsub hj)
              omega)
          _ = _ := by simp
      rw [sum_add_distrib] at hmass
      rw [hi n, hsource]
      rw [← hmass]
      ring

lemma initial_nonnegative_cap (history : ℕ → Finset ℕ) (r : ℕ) (α : ℝ)
    (initial : ℕ → ℝ) (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2)
    (hdelay : 4 * α * (r : ℝ) ≤ 1)
    (hpast : ∀ n, history n ⊆ range n)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hi : ∀ n, initial n = 1 - α * ∑ j ∈ history n, initial j) :
    ∀ n, 0 ≤ initial n ∧ initial n ≤ 1 := by
  have h := depletion_bounds history (fun _ => True) 1 α r initial (by norm_num)
    hα hsmall hdelay hpast hrecent (by simpa using hi)
  exact fun n => ⟨(h n).2.1, (h n).2.2.1⟩

lemma merged_square_mass {ι : Type*} (s : Finset ι) (initial : ℝ)
    (source : ι → ℝ) (B : ℝ) (hB : 0 < B) (hi : 0 ≤ initial)
    (hi1 : initial ≤ 1) (hs : ∀ q ∈ s, 0 ≤ source q)
    (hcap : ∀ q ∈ s, source q ≤ 1 / B)
    (hmass : initial + ∑ q ∈ s, source q = 1) :
    initial ^ 2 / B + ∑ q ∈ s, source q ^ 2 ≤ 1 / B := by
  have hsquare : (∑ q ∈ s, source q ^ 2) ≤ (1 / B) * ∑ q ∈ s, source q := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    nlinarith [mul_le_mul_of_nonneg_right (hcap q hq) (hs q hq)]
  have hisquare : initial ^ 2 / B ≤ initial / B :=
    div_le_div_of_nonneg_right (by nlinarith) hB.le
  calc
    _ ≤ initial / B + (1 / B) * ∑ q ∈ s, source q := add_le_add hisquare hsquare
    _ = (initial + ∑ q ∈ s, source q) / B := by ring
    _ = 1 / B := by rw [hmass]

lemma depletion_local_tail (history : ℕ → Finset ℕ) (r : ℕ) (α : ℝ)
    (c : ℕ → ℝ) (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2)
    (hdelay : 4 * α * (r : ℝ) ≤ 1)
    (hpast : ∀ n, history n ⊆ range n)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hrec : ∀ n, c n = 1 - α * ∑ j ∈ history n, c j) :
    ∀ n, c n ≤ (1 - α) ^ (n - r) := by
  have hb := depletion_bounds history (fun _ => True) 1 α r c (by norm_num)
    hα hsmall hdelay hpast hrecent (by simpa using hrec)
  have hc : ∀ n, 0 ≤ c n := fun n => (hb n).2.1
  have ht := depletion_tail history 1 α c 0 hα (by linarith) hpast hc
    (fun n _ => hrec n)
  intro n
  have hsum : (∑ j ∈ range (n - r), c j) ≤ ∑ j ∈ history n, c j :=
    sum_le_sum_of_subset_of_nonneg (hrecent n) (fun j _ _ => hc j)
  have hlocal : c n ≤ residual 1 α c (n - r) := by
    rw [hrec n]
    dsimp [residual]
    nlinarith [mul_le_mul_of_nonneg_left hsum hα]
  exact hlocal.trans (by simpa [residual_zero] using ht (n - r))

lemma shifted_old_recurrence (history : ℕ → Finset ℕ) (α : ℝ)
    (cutoff : ℕ) (c : ℕ → ℝ) (hpast : ∀ n, history n ⊆ range n)
    (hbefore : ∀ n, n < cutoff → c n = 1)
    (hrec : ∀ n, c n = 1 + (∑ j ∈ history n, if j < cutoff then α else 0) -
      α * ∑ j ∈ history n, c j) :
    ∀ n, c (cutoff + n) = 1 - α *
      ∑ j ∈ shiftedHistory history cutoff n, c (cutoff + j) := by
  intro n
  let d := fun j => if j < cutoff then 0 else c j
  have hd (j : ℕ) : (if j < cutoff then α else 0) - α * c j = -α * d j := by
    dsimp [d]
    split_ifs with hj
    · rw [hbefore j hj]
      ring
    · ring
  have hz : ∀ j, j < cutoff → d j = 0 := by
    intro j hj
    simp [d, hj]
  have hshift := sum_shiftedHistory history cutoff n d (hpast _) hz
  have hdshift : (∑ j ∈ shiftedHistory history cutoff n, d (cutoff + j)) =
      ∑ j ∈ shiftedHistory history cutoff n, c (cutoff + j) := by
    apply sum_congr rfl
    intro j _
    simp [d]
  rw [hdshift] at hshift
  calc
    c (cutoff + n) = 1 + ∑ j ∈ history (cutoff + n),
        ((if j < cutoff then α else 0) - α * c j) := by
      rw [hrec, sum_sub_distrib, ← mul_sum]
      ring
    _ = 1 + ∑ j ∈ history (cutoff + n), -α * d j := by simp_rw [hd]
    _ = 1 - α * ∑ j ∈ shiftedHistory history cutoff n, c (cutoff + j) := by
      rw [← mul_sum, ← hshift]
      ring

lemma sum_births_interchange (s : Finset ℕ) (cutoff : ℕ) (α : ℝ) :
    (∑ q ∈ range cutoff, if q ∈ s then α else 0) =
      ∑ j ∈ s, if j < cutoff then α else 0 := by
  calc
    _ = ∑ q ∈ range cutoff, ∑ j ∈ s, if j = q then α else 0 := by simp
    _ = ∑ j ∈ s, ∑ q ∈ range cutoff, if j = q then α else 0 := sum_comm
    _ = _ := by simp

lemma old_source_recurrence (history : ℕ → Finset ℕ) (α : ℝ)
    (initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ) (cutoff : ℕ)
    (hi : ∀ n, initial n = 1 - α * ∑ j ∈ history n, initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, source j q) (n : ℕ) :
    initial n + ∑ q ∈ range cutoff, source n q =
      1 + (∑ j ∈ history n, if j < cutoff then α else 0) -
        α * ∑ j ∈ history n, (initial j + ∑ q ∈ range cutoff, source j q) := by
  rw [hi n]
  simp_rw [hs n]
  rw [sum_sub_distrib, ← mul_sum, sum_comm, sum_births_interchange, sum_add_distrib]
  ring

lemma old_source_tail (history : ℕ → Finset ℕ) (α : ℝ) (r cutoff : ℕ)
    (initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (hα : 0 ≤ α) (hsmall : α ≤ 1 / 2) (hdelay : 4 * α * (r : ℝ) ≤ 1)
    (hpast : ∀ n, history n ⊆ range n)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hi : ∀ n, initial n = 1 - α * ∑ j ∈ history n, initial j)
    (hs : ∀ n q, source n q = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, source j q) :
    ∀ n, initial n + ∑ q ∈ range cutoff, source n q ≤
      (1 - α) ^ (n - cutoff - r) := by
  let c := fun n => initial n + ∑ q ∈ range cutoff, source n q
  have hm := coefficient_mass history α initial source hpast hi hs
  have hr := shifted_old_recurrence history α cutoff c hpast
    (fun n hn => hm n cutoff hn.le) (old_source_recurrence history α initial source cutoff hi hs)
  have ht := depletion_local_tail (shiftedHistory history cutoff) r α
    (fun n => c (cutoff + n)) hα hsmall hdelay
    (shiftedHistory_past history cutoff) (shiftedHistory_recent history cutoff r hrecent) hr
  intro n
  by_cases hn : n < cutoff
  · rw [hm n cutoff hn.le]
    simp [Nat.sub_eq_zero_of_le hn.le]
  · have he : cutoff + (n - cutoff) = n := by omega
    simpa [c, he] using ht (n - cutoff)

def estimatorInitial (α : ℝ) (initial : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 - α) * initial n

def estimatorSource (α : ℝ) (source : ℕ → ℕ → ℝ) (n q : ℕ) : ℝ :=
  (1 - α) * source n q + if q = n then α else 0

lemma estimator_mass (α : ℝ) (initial : ℕ → ℝ) (source : ℕ → ℕ → ℝ)
    (n N : ℕ) (hn : n < N) (hm : initial n + ∑ q ∈ range N, source n q = 1) :
    estimatorInitial α initial n + ∑ q ∈ range N, estimatorSource α source n q = 1 := by
  simp only [estimatorInitial, estimatorSource, sum_add_distrib, ← mul_sum]
  simp only [sum_ite_eq', mem_range, hn, ite_true]
  rw [← add_assoc, ← mul_add, hm]
  ring

lemma estimator_source_cap (α : ℝ) (source : ℕ → ℕ → ℝ) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (n q : ℕ) (hnonneg : 0 ≤ source n q)
    (hcap : source n q ≤ α) (hself : source n n = 0) :
    0 ≤ estimatorSource α source n q ∧ estimatorSource α source n q ≤ α := by
  dsimp [estimatorSource]
  by_cases hq : q = n
  · subst q
    simp [hself, hα]
  · simp only [hq, ite_false, add_zero]
    constructor
    · exact mul_nonneg (by linarith) hnonneg
    · nlinarith

lemma estimator_initial_bounds (α : ℝ) (initial : ℕ → ℝ) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) (n : ℕ) (hi : 0 ≤ initial n) (hi1 : initial n ≤ 1) :
    0 ≤ estimatorInitial α initial n ∧ estimatorInitial α initial n ≤ 1 := by
  dsimp [estimatorInitial]
  exact ⟨mul_nonneg (by linarith) hi, by nlinarith⟩

lemma estimator_old_tail (α : ℝ) (r : ℕ) (initial : ℕ → ℝ)
    (source : ℕ → ℕ → ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hmass : ∀ n N, n ≤ N → initial n + ∑ q ∈ range N, source n q = 1)
    (htail : ∀ cutoff n, initial n + ∑ q ∈ range cutoff, source n q ≤
      (1 - α) ^ (n - cutoff - r)) (cutoff n : ℕ) :
    estimatorInitial α initial n + ∑ q ∈ range cutoff, estimatorSource α source n q ≤
      (1 - α) ^ (n - cutoff - r) := by
  by_cases hn : n < cutoff
  · rw [estimator_mass α initial source n cutoff hn (hmass n cutoff hn.le)]
    simp [Nat.sub_eq_zero_of_le hn.le]
  · have he : estimatorInitial α initial n +
        ∑ q ∈ range cutoff, estimatorSource α source n q =
        (1 - α) * (initial n + ∑ q ∈ range cutoff, source n q) := by
      simp [estimatorInitial, estimatorSource, sum_add_distrib, ← mul_sum, hn, mul_add]
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left (htail cutoff n) (show 0 ≤ 1 - α by linarith)
    have hp := pow_nonneg (show 0 ≤ 1 - α by linarith) (n - cutoff - r)
    exact hmul.trans (by nlinarith)

noncomputable def initialCoefficient (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (n : ℕ) : ℝ :=
  1 - α * ∑ j : history n, initialCoefficient history hpast α j.val
termination_by n
decreasing_by exact mem_range.mp (hpast n j.property)

noncomputable def sourceCoefficient (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (q n : ℕ) : ℝ :=
  (if q ∈ history n then α else 0) -
    α * ∑ j : history n, sourceCoefficient history hpast α q j.val
termination_by n
decreasing_by exact mem_range.mp (hpast n j.property)

lemma initialCoefficient_rec (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (n : ℕ) :
    initialCoefficient history hpast α n =
      1 - α * ∑ j ∈ history n, initialCoefficient history hpast α j := by
  rw [initialCoefficient]
  simp [sum_attach]

lemma sourceCoefficient_rec (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (α : ℝ) (q n : ℕ) :
    sourceCoefficient history hpast α q n =
      (if q ∈ history n then α else 0) -
        α * ∑ j ∈ history n, sourceCoefficient history hpast α q j := by
  rw [sourceCoefficient]
  simp [sum_attach]

noncomputable def initialWeight (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B : ℕ) (n : ℕ) : ℝ :=
  estimatorInitial (1 / (B : ℝ)) (initialCoefficient history hpast (1 / (B : ℝ))) n

noncomputable def sourceWeight (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B : ℕ) (n q : ℕ) : ℝ :=
  estimatorSource (1 / (B : ℝ)) (fun j q => sourceCoefficient history hpast (1 / (B : ℝ)) q j) n q

lemma weight_bounds (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B r : ℕ) (hB : 2 ≤ B) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) :
    (∀ n, 0 ≤ initialWeight history hpast B n ∧ initialWeight history hpast B n ≤ 1) ∧
    (∀ n q, 0 ≤ sourceWeight history hpast B n q ∧ sourceWeight history hpast B n q ≤ 1 / (B : ℝ)) ∧
    (∀ n N, n < N → initialWeight history hpast B n +
      ∑ q ∈ range N, sourceWeight history hpast B n q = 1) ∧
    (∀ n cutoff, initialWeight history hpast B n +
      ∑ q ∈ range cutoff, sourceWeight history hpast B n q ≤
        (1 - 1 / (B : ℝ)) ^ (n - cutoff - r)) := by
  let α := 1 / (B : ℝ)
  let initial := initialCoefficient history hpast α
  let source := fun n q => sourceCoefficient history hpast α q n
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hα : 0 ≤ α := by positivity
  have hsmall : α ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hB0 (by norm_num)).2
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hdelay : 4 * α * (r : ℝ) ≤ 1 := by
    have hrr : (4 : ℝ) * r ≤ B := by exact_mod_cast hr
    dsimp [α]
    calc
      4 * (1 / (B : ℝ)) * r = (4 * r) / B := by ring
      _ ≤ 1 := (div_le_iff₀ hB0).2 (by simpa using hrr)
  have hi : ∀ n, initial n = 1 - α * ∑ j ∈ history n, initial j :=
    initialCoefficient_rec history hpast α
  have hs : ∀ n q, source n q = (if q ∈ history n then α else 0) -
      α * ∑ j ∈ history n, source j q := fun n q => sourceCoefficient_rec history hpast α q n
  have hib := initial_nonnegative_cap history r α initial hα hsmall hdelay hpast hrecent hi
  have hsb (n q : ℕ) := source_nonnegative_cap history q r α (fun j => source j q)
    hα hsmall hdelay hpast hrecent hclosed (fun j => hs j q) n
  have hmass := coefficient_mass history α initial source hpast hi hs
  have htail (cutoff : ℕ) := old_source_tail history α r cutoff initial source
    hα hsmall hdelay hpast hrecent hi hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact estimator_initial_bounds α initial hα (by linarith) n (hib n).1 (hib n).2
  · intro n q
    have hself : source n n = 0 :=
      source_zero history n α (fun j => source j n) hpast hclosed (fun j => hs j n) n
        (fun hn => (Nat.lt_irrefl _) (mem_range.mp (hpast n hn)))
    exact estimator_source_cap α source hα (by linarith) n q (hsb n q).1 (hsb n q).2 hself
  · intro n N hn
    exact estimator_mass α initial source n N hn (hmass n N hn.le)
  · intro n cutoff
    exact estimator_old_tail α r initial source hα (by linarith) hmass htail cutoff n

lemma weight_square_mass (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (B r : ℕ) (hB : 2 ≤ B) (hr : 4 * r ≤ B)
    (hrecent : ∀ n, range (n - r) ⊆ history n)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) (n N : ℕ) (hn : n < N) :
    initialWeight history hpast B n ^ 2 / B +
      ∑ q ∈ range N, sourceWeight history hpast B n q ^ 2 ≤ 1 / (B : ℝ) := by
  have hb := weight_bounds history hpast B r hB hr hrecent hclosed
  exact merged_square_mass (range N) (initialWeight history hpast B n)
    (sourceWeight history hpast B n) B (by exact_mod_cast (show 0 < B by omega))
    (hb.1 n).1 (hb.1 n).2 (fun q _ => (hb.2.1 n q).1) (fun q _ => (hb.2.1 n q).2)
    (hb.2.2.1 n N hn)

end LongTails.Proofs.BirchCausalCoefficients
