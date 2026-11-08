import LongTails.Proofs.BirchRetainedCoefficients

namespace LongTails.Proofs.BirchRetainedRenewal

open Finset
open LongTails.Proofs.BirchRetainedWork
open LongTails.Proofs.BirchRetainedCoefficients

lemma sourceCoefficient_prefix (history other : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (hother : ∀ n, other n ⊆ range n)
    (β γ : ℕ → ℝ) (N : ℕ)
    (hh : ∀ n, n < N → history n = other n) (hb : ∀ n, n < N → β n = γ n) :
    ∀ n, n < N → ∀ q, sourceCoefficient history hpast β q n =
      sourceCoefficient other hother γ q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn q
      rw [sourceCoefficient_rec, sourceCoefficient_rec, ← hh n hn]
      congr 1
      · by_cases hq : q ∈ history n
        · rw [ite_eq_left hq, ite_eq_left hq, hb q
            (lt_trans (mem_range.mp (hpast n hq)) hn)]
        · simp [hq]
      · apply sum_congr rfl
        intro j hj
        have hjn := mem_range.mp (hpast n hj)
        rw [hb j (hjn.trans hn), ih j hjn (hjn.trans hn) q]

lemma sourceWeight_prefix (history other : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (hother : ∀ n, other n ⊆ range n)
    (β γ : ℕ → ℝ) (N : ℕ)
    (hh : ∀ n, n < N → history n = other n) (hb : ∀ n, n < N → β n = γ n)
    (n q : ℕ) (hn : n < N) :
    sourceWeight history hpast β n q = sourceWeight other hother γ n q := by
  simp only [sourceWeight, estimatorSource]
  rw [hb n hn, sourceCoefficient_prefix history other hpast hother β γ N hh hb n hn q]

def finishHistory (history : ℕ → Finset ℕ) (N n : ℕ) : Finset ℕ :=
  if n < N then history n else range n

def finishGain (β : ℕ → ℝ) (N n : ℕ) : ℝ := if n < N then β n else 0

def finishScale (scale : ℕ → ℝ) (N n : ℕ) : ℝ := if n < N then scale n else 1

def finishFrontier (frontier : ℕ → ℕ) (N n : ℕ) : ℕ := if n < N then frontier n else n

lemma finishHistory_past (history : ℕ → Finset ℕ) (N : ℕ)
    (hpast : ∀ n, history n ⊆ range n) : ∀ n, finishHistory history N n ⊆ range n := by
  intro n
  unfold finishHistory
  split_ifs
  · exact hpast n
  · exact Subset.rfl

lemma finishHistory_closed (history : ℕ → Finset ℕ) (N : ℕ)
    (hpast : ∀ n, history n ⊆ range n)
    (hclosed : ∀ n, n < N → ∀ j, j ∈ history n → history j ⊆ history n) :
    ∀ n j, j ∈ finishHistory history N n → finishHistory history N j ⊆ finishHistory history N n := by
  intro n j hj
  by_cases hn : n < N
  · have hj' : j ∈ history n := by simpa [finishHistory, hn] using hj
    have hjn := mem_range.mp (hpast n hj')
    simp only [finishHistory, hn, hjn.trans hn, ite_true]
    exact hclosed n hn j hj'
  · have hjn : j < n := by simpa [finishHistory, hn] using hj
    rw [show finishHistory history N n = range n by simp [finishHistory, hn]]
    exact (finishHistory_past history N hpast j).trans (range_mono hjn.le)

lemma finite_weight_bounds (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (β scale : ℕ → ℝ) (N : ℕ) (hN : 0 < N) (hpast : ∀ n, history n ⊆ range n)
    (hβ : ∀ n, n < N → 0 ≤ β n) (hscale : ∀ n, n < N → 1 ≤ scale n)
    (hp : ∀ n, n < N → 0 ≤ 1 - β n * scale n)
    (hclosed : ∀ n, n < N → ∀ j, j ∈ history n → history j ⊆ history n)
    (hfrontier : ∀ n, n < N → frontier n ≤ n)
    (hprefix : ∀ n, n < N → range (frontier n) ⊆ history n)
    (hgate : ∀ n, n < N → 1 ≤ scale n *
      ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)))
    (hreset : β 0 = 1) :
    (∀ n, n < N → ∀ q, q < N →
      0 ≤ sourceWeight history hpast β n q ∧ sourceWeight history hpast β n q ≤ β q) ∧
    (∀ n, n < N → ∑ q ∈ range (n + 1), sourceWeight history hpast β n q = 1) ∧
    (∀ n, n < N → ∀ cutoff, cutoff ≤ n →
      (∑ q ∈ range cutoff, sourceWeight history hpast β n q) ≤
        scale n * survival β cutoff (n + 1)) := by
  let A := finishHistory history N
  let b := finishGain β N
  let l := finishScale scale N
  let f := finishFrontier frontier N
  have hA := finishHistory_past history N hpast
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b, finishGain]
    split_ifs with hn
    · exact hβ n hn
    · norm_num
  have hl : ∀ n, 1 ≤ l n := by
    intro n
    dsimp [l, finishScale]
    split_ifs with hn
    · exact hscale n hn
    · norm_num
  have hprod : ∀ n, 0 ≤ 1 - b n * l n := by
    intro n
    by_cases hn : n < N
    · simpa [b, l, finishGain, finishScale, hn] using hp n hn
    · simp [b, l, finishGain, finishScale, hn]
  have hf : ∀ n, f n ≤ n := by
    intro n
    by_cases hn : n < N
    · simpa [f, finishFrontier, hn] using hfrontier n hn
    · simp [f, finishFrontier, hn]
  have hpre : ∀ n, range (f n) ⊆ A n := by
    intro n
    by_cases hn : n < N
    · simpa [f, A, finishFrontier, finishHistory, hn] using hprefix n hn
    · simp [f, A, finishFrontier, finishHistory, hn]
  have hg : ∀ n, 1 ≤ l n * ∏ j ∈ range (n - f n), (1 - b (f n + j) * l (f n + j)) := by
    intro n
    by_cases hn : n < N
    · have he : (∏ j ∈ range (n - frontier n),
          (1 - b (frontier n + j) * l (frontier n + j))) =
          ∏ j ∈ range (n - frontier n), (1 - β (frontier n + j) * scale (frontier n + j)) := by
        apply prod_congr rfl
        intro j hj
        have hh : frontier n + j < N := by
          have := mem_range.mp hj
          have := hfrontier n hn
          omega
        simp [b, l, finishGain, finishScale, hh]
      simp only [f, finishFrontier, hn, ite_true]
      rw [show l n = scale n by simp [l, finishScale, hn], he]
      exact hgate n hn
    · simp [f, l, finishFrontier, finishScale, hn]
  have hr : b 0 = 1 := by simp [b, finishGain, hN, hreset]
  have hh := weight_bounds A f b l hA hb hl hprod
    (finishHistory_closed history N hpast hclosed) hf hpre hg hr
  have he (n q : ℕ) (hn : n < N) : sourceWeight history hpast β n q = sourceWeight A hA b n q := by
    apply sourceWeight_prefix history A hpast hA β b N _ _ n q hn
    · intro j hj
      simp [A, finishHistory, hj]
    · intro j hj
      simp [b, finishGain, hj]
  refine ⟨?_, ?_, ?_⟩
  · intro n hn q hq
    rw [he n q hn]
    simpa [b, finishGain, hq] using hh.1 n q
  · intro n hn
    simp_rw [he n _ hn]
    exact hh.2.1 n (n + 1) (by omega)
  · intro n hn c hc
    have ht := hh.2.2 n c hc
    have hsurv : survival b c (n + 1) = survival β c (n + 1) := by
      apply prod_congr rfl
      intro j hj
      have hjN : j < N := by have := (mem_Ico.mp hj).2; omega
      simp [b, finishGain, hjN]
    simp_rw [he n _ hn]
    simpa [l, finishScale, hn, hsurv] using ht

lemma reset_cancels_prefix {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v₀ : E) (reply momentum : ℕ → E) (β : ℕ → ℝ) (r : ℕ)
    (hreset : β r = 1)
    (hr : momentum r = v₀ + ∑ j ∈ range r, β j • (reply j - momentum j)) :
    v₀ + ∑ j ∈ range (r + 1), β j • (reply j - momentum j) = reply r := by
  rw [sum_range_succ, hreset, one_smul, hr]
  abel

lemma reset_cancels_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v₀ : E) (reply momentum : ℕ → E) (β : ℕ → ℝ) (r : ℕ) (s : Finset ℕ)
    (hreset : β r = 1) (hprefix : range (r + 1) ⊆ s)
    (hr : momentum r = v₀ + ∑ j ∈ range r, β j • (reply j - momentum j)) :
    v₀ + ∑ j ∈ s, β j • (reply j - momentum j) =
      reply r + ∑ j ∈ s \ range (r + 1), β j • (reply j - momentum j) := by
  have hs := sum_sdiff hprefix (f := fun j => β j • (reply j - momentum j))
  have hh := reset_cancels_prefix v₀ reply momentum β r hreset hr
  rw [← hs]
  rw [← hh]
  abel

def after (r : ℕ) (s : Finset ℕ) : Finset ℕ :=
  (s.filter (fun j => r ≤ j)).image (fun j => j - r)

lemma mem_after (r j : ℕ) (s : Finset ℕ) : j ∈ after r s ↔ r + j ∈ s := by
  constructor
  · intro hj
    obtain ⟨i, hi, he⟩ := mem_image.mp hj
    obtain ⟨his, hri⟩ := mem_filter.mp hi
    have : r + j = i := by omega
    simpa [this] using his
  · intro hj
    apply mem_image.mpr
    exact ⟨r + j, mem_filter.mpr ⟨hj, by omega⟩, by omega⟩

lemma sum_after {E : Type*} [AddCommMonoid E] (r : ℕ) (s : Finset ℕ) (f : ℕ → E) :
    (∑ j ∈ after r s, f (r + j)) = ∑ j ∈ s.filter (fun j => r ≤ j), f j := by
  apply sum_bij (fun j _ => r + j)
  · intro j hj
    exact mem_filter.mpr ⟨(mem_after r j s).mp hj, by omega⟩
  · intro i _ j _ he
    omega
  · intro j hj
    obtain ⟨hjs, hrj⟩ := mem_filter.mp hj
    refine ⟨j - r, (mem_after r (j - r) s).mpr ?_, by omega⟩
    simpa [Nat.add_sub_of_le hrj] using hjs
  · intro j _
    rfl

lemma after_past (history : ℕ → Finset ℕ) (r : ℕ)
    (hpast : ∀ n, history n ⊆ range n) :
    ∀ n, after r (history (r + n)) ⊆ range n := by
  intro n j hj
  have hh := mem_range.mp (hpast (r + n) ((mem_after r j _).mp hj))
  exact mem_range.mpr (by omega)

lemma after_closed (history : ℕ → Finset ℕ) (r : ℕ)
    (hclosed : ∀ n j, j ∈ history n → history j ⊆ history n) :
    ∀ n j, j ∈ after r (history (r + n)) →
      after r (history (r + j)) ⊆ after r (history (r + n)) := by
  intro n j hj t ht
  apply (mem_after r t _).mpr
  exact hclosed (r + n) (r + j) ((mem_after r j _).mp hj) ((mem_after r t _).mp ht)

lemma after_erase_zero (r : ℕ) (s : Finset ℕ) :
    (after r s).erase 0 = after r (s \ range (r + 1)) := by
  ext j
  simp only [mem_erase, mem_after, mem_sdiff, mem_range]
  constructor
  · rintro ⟨hj, hs⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hj⟩
    exact ⟨by omega, hs⟩

lemma sum_after_erase_zero {E : Type*} [AddCommMonoid E]
    (r : ℕ) (s : Finset ℕ) (f : ℕ → E) :
    (∑ j ∈ (after r s).erase 0, f (r + j)) = ∑ j ∈ s \ range (r + 1), f j := by
  rw [after_erase_zero, sum_after]
  congr 1
  ext j
  simp only [mem_filter, mem_sdiff, mem_range]
  constructor
  · exact And.left
  · rintro ⟨hj, hbound⟩
    exact ⟨⟨hj, hbound⟩, by omega⟩

lemma rebased_recurrence {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (v₀ : E) (reply momentum : ℕ → E) (β : ℕ → ℝ)
    (r n : ℕ) (hpast : ∀ j, history j ⊆ range j) (hreset : β r = 1)
    (hanchor : history r = range r)
    (hprefix : 0 < n → range (r + 1) ⊆ history (r + n))
    (hrec : ∀ j, momentum j = v₀ + ∑ i ∈ history j, β i • (reply i - momentum i)) :
    (if n = 0 then 0 else momentum (r + n)) =
      ∑ j ∈ after r (history (r + n)),
        β (r + j) • (reply (r + j) - if j = 0 then 0 else momentum (r + j)) := by
  by_cases hn : n = 0
  · have he : after r (history (r + n)) = ∅ := by
      apply subset_empty.mp
      simpa [hn] using after_past history r hpast n
    rw [he]
    simp [hn]
  have hnpos : 0 < n := by omega
  have hz : 0 ∈ after r (history (r + n)) := by
    apply (mem_after r 0 _).mpr
    simpa using hprefix hnpos (mem_range.mpr (by omega : r < r + 1))
  have hr : momentum r = v₀ + ∑ j ∈ range r, β j • (reply j - momentum j) := by
    rw [hrec r, hanchor]
  have hc := reset_cancels_history v₀ reply momentum β r (history (r + n))
    hreset (hprefix hnpos) hr
  rw [ite_eq_right hn, hrec (r + n), hc,
    ← sum_erase_add _ _ hz]
  simp only [Nat.add_zero, hreset, ite_true, sub_zero, one_smul]
  have he : (∑ j ∈ (after r (history (r + n))).erase 0,
      β (r + j) • (reply (r + j) - if j = 0 then 0 else momentum (r + j))) =
      ∑ j ∈ history (r + n) \ range (r + 1), β j • (reply j - momentum j) := by
    calc
      _ = ∑ j ∈ (after r (history (r + n))).erase 0,
          β (r + j) • (reply (r + j) - momentum (r + j)) := by
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_right (mem_erase.mp hj).1]
      _ = _ := sum_after_erase_zero r (history (r + n))
        (fun j => β j • (reply j - momentum j))
  rw [he]
  abel

lemma source_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (β : ℕ → ℝ) (reply momentum : ℕ → E) (N : ℕ)
    (hrec : ∀ n, n < N → momentum n = ∑ j ∈ history n, β j • (reply j - momentum j)) :
    ∀ n, n < N → momentum n =
      ∑ q ∈ range N, sourceCoefficient history hpast β q n • reply q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      have hsub : history n ⊆ range N := (hpast n).trans (range_mono hn.le)
      have hbirth : (∑ q ∈ range N, (if q ∈ history n then β q else 0) • reply q) =
          ∑ j ∈ history n, β j • reply j := by
        have he : (∑ q ∈ history n, (if q ∈ history n then β q else 0) • reply q) =
            ∑ q ∈ range N, (if q ∈ history n then β q else 0) • reply q := by
          apply sum_subset hsub
          intro q _ hq
          simp [hq]
        rw [← he]
        apply sum_congr rfl
        intro j hj
        rw [ite_eq_left hj]
      have hprior : (∑ q ∈ range N,
          (∑ j ∈ history n, β j * sourceCoefficient history hpast β q j) • reply q) =
          ∑ j ∈ history n, β j • momentum j := by
        simp only [Finset.sum_smul]
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        have hjn := mem_range.mp (hpast n hj)
        rw [ih j hjn (hjn.trans hn), Finset.smul_sum]
        apply sum_congr rfl
        intro q _
        rw [smul_smul]
      have he : (∑ q ∈ range N, sourceCoefficient history hpast β q n • reply q) =
          ∑ q ∈ range N, ((if q ∈ history n then β q else 0) • reply q -
            (∑ j ∈ history n, β j * sourceCoefficient history hpast β q j) • reply q) := by
        apply sum_congr rfl
        intro q _
        rw [sourceCoefficient_rec, sub_smul]
      rw [he]
      rw [sum_sub_distrib, hbirth, hprior, hrec n hn]
      simp only [smul_sub, sum_sub_distrib]

lemma estimator_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (β : ℕ → ℝ) (reply momentum : ℕ → E) (N n : ℕ) (hn : n < N)
    (hrec : ∀ j, j < N → momentum j = ∑ i ∈ history j, β i • (reply i - momentum i)) :
    (1 - β n) • momentum n + β n • reply n =
      ∑ q ∈ range N, sourceWeight history hpast β n q • reply q := by
  rw [source_expansion history hpast β reply momentum N hrec n hn]
  simp only [sourceWeight, estimatorSource, add_smul, sum_add_distrib, mul_smul, Finset.smul_sum]
  congr 1
  simp [ite_smul, hn, eq_comm]

def liftRow (r : ℕ) (v : ℕ → ℝ) (q : ℕ) : ℝ := if r ≤ q then v (q - r) else 0

lemma sum_liftRow (r c : ℕ) (v : ℕ → ℝ) :
    (∑ q ∈ range c, liftRow r v q) = ∑ j ∈ range (c - r), v j := by
  have he : (range c).filter (fun q => r ≤ q) = Ico r c := by
    ext q
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  simp only [liftRow]
  rw [← sum_filter, he, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro j _
  congr 1
  omega

lemma survival_shift (β : ℕ → ℝ) (r c n : ℕ) :
    survival (fun j => β (r + j)) c n = survival β (r + c) (r + n) := by
  simp only [survival, prod_Ico_eq_prod_range, Nat.add_sub_add_left, Nat.add_assoc]

lemma lifted_row_bounds (β v : ℕ → ℝ) (r n : ℕ) (Λ : ℝ) (hrn : r ≤ n)
    (hΛ : 0 ≤ Λ) (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1)
    (hv : ∀ q, q ≤ n - r → 0 ≤ v q ∧ v q ≤ β (r + q))
    (hmass : ∑ q ∈ range (n - r + 1), v q = 1)
    (htail : ∀ c, c ≤ n - r → (∑ q ∈ range c, v q) ≤
      Λ * survival (fun j => β (r + j)) c (n - r + 1)) :
    (∀ q, q ≤ n → 0 ≤ liftRow r v q ∧ liftRow r v q ≤ β q) ∧
    (∑ q ∈ range (n + 1), liftRow r v q) = 1 ∧
    (∀ c, c ≤ n → (∑ q ∈ range c, liftRow r v q) ≤ Λ * survival β c (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    by_cases hrq : r ≤ q
    · have hh := hv (q - r) (by omega)
      simpa [liftRow, hrq, Nat.add_sub_of_le hrq] using hh
    · simp only [liftRow, hrq, ite_false, le_refl, true_and]
      exact hβ q
  · rw [sum_liftRow, show n + 1 - r = n - r + 1 by omega]
    exact hmass
  · intro c hc
    rw [sum_liftRow]
    by_cases hcr : c ≤ r
    · simp only [Nat.sub_eq_zero_of_le hcr, range_zero, sum_empty]
      exact mul_nonneg hΛ (survival_nonnegative β hβ1 _ _)
    · have hh := htail (c - r) (by omega)
      rw [survival_shift,
        show r + (c - r) = c by omega,
        show r + (n - r + 1) = n + 1 by omega] at hh
      exact hh

noncomputable def renewalRow (history : ℕ → Finset ℕ)
    (hpast : ∀ n, history n ⊆ range n) (β : ℕ → ℝ) (r n : ℕ) : ℕ → ℝ :=
  liftRow r (sourceWeight (fun j => after r (history (r + j))) (after_past history r hpast)
    (fun j => β (r + j)) (n - r))

lemma renewal_row_bounds (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (β : ℕ → ℝ) (r n : ℕ) (frontier : ℕ → ℕ) (scale : ℕ → ℝ) (Λ : ℝ)
    (hrn : r ≤ n) (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1)
    (hreset : β r = 1) (hΛ : 0 ≤ Λ) (hscaleUpper : scale (n - r) ≤ Λ)
    (hclosed : ∀ i j, j ∈ history i → history j ⊆ history i)
    (hscale : ∀ j, j ≤ n - r → 1 ≤ scale j)
    (hp : ∀ j, j ≤ n - r → 0 ≤ 1 - β (r + j) * scale j)
    (hfrontier : ∀ j, j ≤ n - r → frontier j ≤ j)
    (hprefix : ∀ j, j ≤ n - r → range (frontier j) ⊆ after r (history (r + j)))
    (hgate : ∀ j, j ≤ n - r → 1 ≤ scale j *
      ∏ i ∈ range (j - frontier j), (1 - β (r + (frontier j + i)) * scale (frontier j + i))) :
    (∀ q, q ≤ n → 0 ≤ renewalRow history hpast β r n q ∧
      renewalRow history hpast β r n q ≤ β q) ∧
    (∑ q ∈ range (n + 1), renewalRow history hpast β r n q) = 1 ∧
    (∀ c, c ≤ n → (∑ q ∈ range c, renewalRow history hpast β r n q) ≤
      Λ * survival β c (n + 1)) := by
  have hh := finite_weight_bounds (fun j => after r (history (r + j))) frontier
    (fun j => β (r + j)) scale (n - r + 1) (by omega) (after_past history r hpast)
    (fun j _ => hβ (r + j)) (fun j hj => hscale j (by omega))
    (fun j hj => hp j (by omega))
    (fun j _ i hi => after_closed history r hclosed j i hi)
    (fun j hj => hfrontier j (by omega)) (fun j hj => hprefix j (by omega))
    (fun j hj => hgate j (by omega)) (by simpa using hreset)
  apply lifted_row_bounds β _ r n Λ hrn hΛ hβ hβ1
  · intro q hq
    exact hh.1 (n - r) (by omega) q (by omega)
  · exact hh.2.1 (n - r) (by omega)
  · intro c hc
    apply (hh.2.2 (n - r) (by omega) c hc).trans
    exact mul_le_mul_of_nonneg_right hscaleUpper
      (survival_nonnegative (fun j => β (r + j)) (fun j => hβ1 (r + j)) _ _)

lemma sum_liftRow_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r c : ℕ) (v : ℕ → ℝ) (reply : ℕ → E) :
    (∑ q ∈ range c, liftRow r v q • reply q) =
      ∑ j ∈ range (c - r), v j • reply (r + j) := by
  have he : (range c).filter (fun q => r ≤ q) = Ico r c := by
    ext q
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  simp only [liftRow, ite_smul, zero_smul]
  rw [← sum_filter, he, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro j _
  simp

lemma renewal_estimator_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (v₀ : E) (β : ℕ → ℝ) (reply momentum : ℕ → E) (r n : ℕ) (hrn : r ≤ n)
    (hreset : β r = 1) (hanchor : r < n → history r = range r)
    (hprefix : ∀ j, 0 < j → j ≤ n - r → range (r + 1) ⊆ history (r + j))
    (hrec : ∀ j, momentum j = v₀ + ∑ i ∈ history j, β i • (reply i - momentum i)) :
    (1 - β n) • momentum n + β n • reply n =
      ∑ q ∈ range (n + 1), renewalRow history hpast β r n q • reply q := by
  let A := fun j => after r (history (r + j))
  let b := fun j => β (r + j)
  let g := fun j => reply (r + j)
  let v := fun j => if j = 0 then 0 else momentum (r + j)
  have hv : ∀ j, j < n - r + 1 → v j = ∑ i ∈ A j, b i • (g i - v i) := by
    intro j hj
    by_cases hjzero : j = 0
    · have hempty : A j = ∅ := by
        apply subset_empty.mp
        simpa [A, hjzero] using after_past history r hpast j
      rw [hempty]
      simp [v, hjzero]
    · exact rebased_recurrence history v₀ reply momentum β r j hpast hreset
        (hanchor (by omega)) (fun _ => hprefix j (by omega) (by omega)) hrec
  have hh := estimator_expansion A (after_past history r hpast) b g v
    (n - r + 1) (n - r) (by omega) hv
  change _ = ∑ q ∈ range (n + 1), liftRow r (sourceWeight A (after_past history r hpast) b (n - r)) q • reply q
  rw [sum_liftRow_smul, show n + 1 - r = n - r + 1 by omega]
  rw [← hh]
  dsimp only [b, g, v]
  rw [Nat.add_sub_of_le hrn]
  by_cases hnr : n = r
  · simp [hnr, hreset]
  · simp [show n - r ≠ 0 by omega]

end LongTails.Proofs.BirchRetainedRenewal
