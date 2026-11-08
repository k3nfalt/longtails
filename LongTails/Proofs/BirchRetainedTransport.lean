import LongTails.Proofs.BirchRetainedCoefficients
import LongTails.Proofs.BirchCausalTransport

namespace LongTails.Proofs.BirchRetainedTransport

open Finset
open LongTails.Proofs.BirchRetainedWork
open LongTails.Proofs.BirchCausalTransport (displacement transportMass)

noncomputable def work (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, w j

lemma work_zero (w : ℕ → ℝ) : work w 0 = 0 := by simp [work]

lemma work_succ (w : ℕ → ℝ) (n : ℕ) : work w (n + 1) = work w n + w n := by
  simp [work, sum_range_succ]

lemma work_monotone (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) : Monotone (work w) := by
  intro m n hmn
  exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun j _ _ => hw j)

lemma work_interval (w : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ j ∈ Ico m n, w j) = work w n - work w m := by
  exact sum_Ico_eq_sub w hmn

lemma weighted_prefix (w : ℕ → ℝ) (n q : ℕ) (hq : q ≤ n) :
    (∑ t ∈ range n, if t < q then w t else 0) = work w q := by
  have hs : (∑ t ∈ range q, if t < q then w t else 0) =
      ∑ t ∈ range n, if t < q then w t else 0 := by
    apply sum_subset (range_mono hq)
    intro t _ ht
    simp only [mem_range] at ht
    simp [ht]
  rw [← hs]
  exact sum_congr rfl (fun t ht => ite_eq_left (mem_range.mp ht))

lemma weighted_tail (w : ℕ → ℝ) (n q : ℕ) (hq : q ≤ n) :
    (∑ t ∈ range n, if q ≤ t then w t else 0) = work w n - work w q := by
  have he : (∑ t ∈ range n, if t < q then w t else 0) +
      (∑ t ∈ range n, if q ≤ t then w t else 0) = work w n := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    by_cases ht : t < q
    · simp [ht, show ¬q ≤ t by omega]
    · simp [ht, show q ≤ t by omega]
  rw [weighted_prefix w n q hq] at he
  linarith

noncomputable def missingWork (history : ℕ → Finset ℕ) (w : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ (range q).filter (fun t => t ∉ history q), w t

lemma missingWork_extended (history : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (n q : ℕ) (hq : q ≤ n) :
    (∑ t ∈ range n, if t < q ∧ t ∉ history q then w t else 0) = missingWork history w q := by
  classical
  have hs : (∑ t ∈ range q, if t < q ∧ t ∉ history q then w t else 0) =
      ∑ t ∈ range n, if t < q ∧ t ∉ history q then w t else 0 := by
    apply sum_subset (range_mono hq)
    intro t _ ht
    simp only [mem_range] at ht
    simp [ht]
  rw [← hs]
  simp only [missingWork, sum_filter]
  apply sum_congr rfl
  intro t ht
  simp [mem_range.mp ht]

lemma displacement_split (history : ℕ → Finset ℕ) (start q t : ℕ) :
    displacement history start q t ≤
      (if t < q ∧ t ∉ history q then (1 : ℝ) else 0) +
        (if q ≤ t then 1 else 0) + (if start ≤ t then 1 else 0) := by
  classical
  unfold displacement
  split_ifs <;> simp_all
  omega

lemma displacement_work (history : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (n q start : ℕ) (hq : q ≤ n) (hstart : start ≤ n) (hw : ∀ t, 0 ≤ w t) :
    (∑ t ∈ range n, w t * displacement history start q t) ≤
      missingWork history w q + (work w n - work w q) + (work w n - work w start) := by
  have hh := sum_le_sum (s := range n) (fun t _ =>
    mul_le_mul_of_nonneg_left (displacement_split history start q t) (hw t))
  simp_rw [mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib] at hh
  rw [missingWork_extended history w n q hq, weighted_tail w n q hq,
    weighted_tail w n start hstart] at hh
  exact hh

lemma missingWork_le_window (history : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (frontier q : ℕ) (hfrontier : frontier ≤ q)
    (hprefix : range frontier ⊆ history q) (hw : ∀ t, 0 ≤ w t) :
    missingWork history w q ≤ work w q - work w frontier := by
  rw [← work_interval w frontier q hfrontier]
  apply sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hw j)
  intro j hj
  obtain ⟨hj, hnot⟩ := mem_filter.mp hj
  apply mem_Ico.mpr
  refine ⟨?_, mem_range.mp hj⟩
  by_contra h
  exact hnot (hprefix (mem_range.mpr (by omega)))

lemma source_age (w source : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ range (n + 1), source q * (work w n - work w q)) =
      ∑ t ∈ range n, w t * ∑ q ∈ range (t + 1), source q := by
  calc
    _ = ∑ q ∈ range (n + 1), ∑ t ∈ range n,
        if q ≤ t then source q * w t else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [← weighted_tail w n q (by have := mem_range.mp hq; omega), mul_sum]
      apply sum_congr rfl
      intro t _
      split_ifs <;> simp_all
    _ = ∑ t ∈ range n, ∑ q ∈ range (n + 1),
        if q ≤ t then source q * w t else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      have hp := weighted_prefix source (n + 1) (t + 1)
        (by have := mem_range.mp ht; omega)
      simp only [work] at hp
      rw [← hp, mul_sum]
      simp only [mul_ite, mul_zero]
      apply sum_congr rfl
      intro q _
      by_cases h : q ≤ t
      · simp [h, show q < t + 1 by omega, mul_comm]
      · simp [h, show ¬q < t + 1 by omega]

lemma survival_succ_le (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hβ1 : ∀ j, β j ≤ 1) (start n : ℕ) (hn : start ≤ n) :
    survival β start (n + 1) ≤ survival β start n := by
  rw [survival_succ_right β start n hn]
  exact mul_le_of_le_one_right (survival_nonnegative β hβ1 _ _)
    (sub_le_self _ (hβ n))

lemma source_age_bound (w β source : ℕ → ℝ) (n : ℕ) (Λ : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hwβ : ∀ j, w j ≤ β j)
    (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1) (hΛ : 0 ≤ Λ)
    (htail : ∀ c, c ≤ n → (∑ q ∈ range c, source q) ≤ Λ * survival β c (n + 1)) :
    (∑ q ∈ range (n + 1), source q * (work w n - work w q)) ≤ Λ := by
  rw [source_age]
  calc
    _ ≤ ∑ t ∈ range n, Λ * (β t * survival β (t + 1) n) := by
      apply sum_le_sum
      intro t ht
      have htn : t + 1 ≤ n := by have := mem_range.mp ht; omega
      have h₁ := mul_le_mul_of_nonneg_left (htail (t + 1) htn) (hw t)
      have h₂ := mul_le_mul_of_nonneg_left
        (survival_succ_le β hβ hβ1 (t + 1) n htn) (mul_nonneg (hw t) hΛ)
      have h₃ := mul_le_mul_of_nonneg_right (hwβ t)
        (mul_nonneg hΛ (survival_nonnegative β hβ1 (t + 1) n))
      nlinarith
    _ = Λ * ∑ t ∈ range n, β t * survival β (t + 1) n := by rw [mul_sum]
    _ ≤ Λ := by
      simpa using mul_le_mul_of_nonneg_left (reverse_occupation_le_one β hβ1 n) hΛ

lemma transport_row (history : ℕ → Finset ℕ) (w β source : ℕ → ℝ)
    (n start : ℕ) (δ H Λ : ℝ) (hstart : start ≤ n)
    (hw : ∀ j, 0 ≤ w j) (hwβ : ∀ j, w j ≤ β j)
    (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1) (hΛ : 0 ≤ Λ)
    (hs : ∀ q, 0 ≤ source q) (hmass : ∑ q ∈ range (n + 1), source q = 1)
    (hmissing : ∀ q, q ≤ n → missingWork history w q ≤ δ)
    (hmain : work w n - work w start ≤ H)
    (htail : ∀ c, c ≤ n → (∑ q ∈ range c, source q) ≤ Λ * survival β c (n + 1)) :
    (∑ t ∈ range n, w t * transportMass history start n t 0 source) ≤ δ + H + Λ := by
  have ha := source_age_bound w β source n Λ hw hwβ hβ hβ1 hΛ htail
  calc
    _ = ∑ q ∈ range (n + 1), source q *
        ∑ t ∈ range n, w t * displacement history start q t := by
      simp only [transportMass, zero_mul, zero_add, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ q ∈ range (n + 1), source q * (δ + H + (work w n - work w q)) := by
      apply sum_le_sum
      intro q hq
      have hqn : q ≤ n := by have := mem_range.mp hq; omega
      apply mul_le_mul_of_nonneg_left _ (hs q)
      have hd := displacement_work history w n q start hqn hstart hw
      linarith [hmissing q hqn]
    _ = δ + H + ∑ q ∈ range (n + 1), source q * (work w n - work w q) := by
      simp only [mul_add, sum_add_distrib]
      simp_rw [← sum_mul]
      rw [hmass]
      ring
    _ ≤ δ + H + Λ := by linarith

lemma weighted_interval (w : ℕ → ℝ) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    (∑ n ∈ range N, if a ≤ n ∧ n < b then w n else 0) = work w b - work w a := by
  have he : (range N).filter (fun n => a ≤ n ∧ n < b) = Ico a b := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [← sum_filter, he, work_interval w a b hab]

lemma weighted_forward_occupation (w β : ℕ → ℝ) (N c : ℕ)
    (hwβ : ∀ j, w j ≤ β j) (hβ1 : ∀ j, β j ≤ 1) :
    (∑ n ∈ range N, if c ≤ n then w n * survival β c n else 0) ≤ 1 := by
  have he : (range N).filter (fun n => c ≤ n) = Ico c N := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [← sum_filter, he]
  calc
    _ ≤ ∑ n ∈ Ico c N, β n * survival β c n :=
      sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hwβ n)
        (survival_nonnegative β hβ1 c n))
    _ ≤ 1 := by
      rw [sum_Ico_eq_sum_range]
      simpa [Nat.add_comm] using forward_occupation_le_one β hβ1 c (N - c)

lemma transport_before_release (history : ℕ → Finset ℕ) (source : ℕ → ℝ)
    (start n t c N : ℕ) (hn : n < N) (ht : t < start)
    (hs : ∀ q, 0 ≤ source q)
    (hrelease : ∀ q, q < N → c ≤ q → t ∈ history q) :
    transportMass history start n t 0 source ≤ ∑ q ∈ range c, source q := by
  have hsub : (range (n + 1)).filter (fun q => t ∉ history q) ⊆ range c := by
    intro q hq
    obtain ⟨hq, hnot⟩ := mem_filter.mp hq
    apply mem_range.mpr
    by_contra h
    exact hnot (hrelease q (by have := mem_range.mp hq; omega) (by omega))
  have he : transportMass history start n t 0 source =
      ∑ q ∈ (range (n + 1)).filter (fun q => t ∉ history q), source q := by
    simp only [transportMass, zero_add, displacement, ht, ite_true,
      mul_ite, mul_zero, mul_one, sum_filter]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp_all
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hs q)

lemma transport_column (history : ℕ → Finset ℕ) (w β : ℕ → ℝ)
    (source : ℕ → ℕ → ℝ) (start : ℕ → ℕ) (N t c : ℕ) (H E Λ : ℝ)
    (hpast : ∀ q, history q ⊆ range q)
    (hstart : ∀ n, start n ≤ n) (htc : t + 1 ≤ c) (hc : c ≤ N)
    (hw : ∀ j, 0 ≤ w j) (hwβ : ∀ j, w j ≤ β j)
    (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1) (hΛ : 0 ≤ Λ)
    (hs : ∀ n q, 0 ≤ source n q)
    (hmass : ∀ n, ∑ q ∈ range (n + 1), source n q = 1)
    (htail : ∀ n c, c ≤ n → (∑ q ∈ range c, source n q) ≤ Λ * survival β c (n + 1))
    (hrelease : ∀ q, q < N → c ≤ q → t ∈ history q)
    (hearly : work w c - work w (t + 1) ≤ E)
    (hblock : (∑ n ∈ range N, if start n ≤ t ∧ t < n then w n else 0) ≤ H) :
    (∑ n ∈ range N, w n * transportMass history (start n) n t 0 (source n)) ≤ H + E + Λ := by
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      w n * transportMass history (start n) n t 0 (source n) ≤
        (if start n ≤ t ∧ t < n then w n else 0) +
        (if t + 1 ≤ n ∧ n < c then w n else 0) +
        Λ * (if c ≤ n then w n * survival β c n else 0) := by
    have hwn := hw n
    have hsurv := survival_nonnegative β hβ1 c n
    have hlast : 0 ≤ Λ * (if c ≤ n then w n * survival β c n else 0) := by
      apply mul_nonneg hΛ
      split_ifs <;> positivity
    have hfirst : 0 ≤ (if start n ≤ t ∧ t < n then w n else 0) := by
      split_ifs <;> positivity
    have hsecond : 0 ≤ (if t + 1 ≤ n ∧ n < c then w n else 0) := by
      split_ifs <;> positivity
    by_cases hnt : n ≤ t
    · rw [LongTails.Proofs.BirchCausalTransport.transportMass_zero history (start n) n t
        0 (source n) hpast (hstart n) hnt, mul_zero]
      positivity
    have hbound := (LongTails.Proofs.BirchCausalTransport.transportMass_bounds
      history (start n) n t 0 (source n) (by norm_num) (hs n) (by simpa using hmass n)).2
    have hb := mul_le_mul_of_nonneg_left hbound (hw n)
    by_cases hst : start n ≤ t
    · rw [ite_eq_left ⟨hst, by omega⟩]
      nlinarith
    by_cases hnc : n < c
    · rw [ite_eq_right (show ¬(start n ≤ t ∧ t < n) by omega),
        ite_eq_left (show t + 1 ≤ n ∧ n < c by omega)]
      nlinarith
    have ho := transport_before_release history (source n) (start n) n t c N
      (mem_range.mp hn) (by omega) (hs n) hrelease
    have hsuc := mul_le_mul_of_nonneg_left
      (survival_succ_le β hβ hβ1 c n (by omega)) hΛ
    have hh := mul_le_mul_of_nonneg_left
      (ho.trans ((htail n c (by omega)).trans hsuc)) (hw n)
    rw [ite_eq_left (show c ≤ n by omega)]
    nlinarith
  have hh := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum] at hh
  rw [weighted_interval w N (t + 1) c htc hc] at hh
  have hf := mul_le_mul_of_nonneg_left
    (weighted_forward_occupation w β N c hwβ hβ1) hΛ
  nlinarith

lemma exists_release (history : ℕ → Finset ℕ) (frontier : ℕ → ℕ)
    (w : ℕ → ℝ) (N t : ℕ) (δ wmax : ℝ) (ht : t < N)
    (hpast : ∀ q, history q ⊆ range q)
    (hprefix : ∀ q, range (frontier q) ⊆ history q)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, j < N → w j ≤ wmax)
    (hwindow : ∀ q, q < N → work w q - work w (frontier q) ≤ δ) :
    ∃ c, t + 1 ≤ c ∧ c ≤ N ∧
      (∀ q, q < N → c ≤ q → t ∈ history q) ∧
      work w c - work w (t + 1) ≤ δ + wmax := by
  classical
  let s := (range N).filter (fun q => t ∉ history q)
  have hts : t ∈ s := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ht, ?_⟩
    intro h
    have := mem_range.mp (hpast t h)
    omega
  have hne : s.Nonempty := ⟨t, hts⟩
  let a := s.max' hne
  have has : a ∈ s := max'_mem s hne
  obtain ⟨haN, ha⟩ := mem_filter.mp has
  have haN' : a < N := mem_range.mp haN
  have hta : t ≤ a := le_max' s t hts
  have hfront : frontier a ≤ t := by
    by_contra h
    exact ha (hprefix a (mem_range.mpr (by omega)))
  have hmono := work_monotone w hw hfront
  have hdist := hwindow a haN'
  refine ⟨a + 1, by omega, by omega, ?_, ?_⟩
  · intro q hq hcq
    by_contra h
    have hqs : q ∈ s := mem_filter.mpr ⟨mem_range.mpr hq, h⟩
    have := le_max' s q hqs
    omega
  · rw [work_succ, work_succ]
    linarith [hw t, hmax a haN']

lemma transport_row_extended (history : ℕ → Finset ℕ) (w source : ℕ → ℝ)
    (N n start : ℕ) (hn : n ≤ N) (hstart : start ≤ n)
    (hpast : ∀ q, history q ⊆ range q) :
    (∑ t ∈ range N, w t * transportMass history start n t 0 source) =
      ∑ t ∈ range n, w t * transportMass history start n t 0 source := by
  symm
  apply sum_subset (range_mono hn)
  intro t _ ht
  rw [LongTails.Proofs.BirchCausalTransport.transportMass_zero history start n t 0 source
    hpast hstart (by simpa only [mem_range, not_lt] using ht), mul_zero]

lemma transport_certificate (history : ℕ → Finset ℕ) (frontier start : ℕ → ℕ)
    (w β : ℕ → ℝ) (source : ℕ → ℕ → ℝ) (N : ℕ) (δ H Λ wmax D : ℝ)
    (hpast : ∀ q, history q ⊆ range q)
    (hfrontier : ∀ q, frontier q ≤ q)
    (hprefix : ∀ q, range (frontier q) ⊆ history q)
    (hstart : ∀ n, start n ≤ n)
    (hw : ∀ j, 0 ≤ w j) (hwβ : ∀ j, w j ≤ β j)
    (hβ : ∀ j, 0 ≤ β j) (hβ1 : ∀ j, β j ≤ 1)
    (hδ : 0 ≤ δ) (hH : 0 ≤ H) (hΛ : 0 ≤ Λ)
    (hmax : ∀ j, j < N → w j ≤ wmax)
    (hs : ∀ n q, 0 ≤ source n q)
    (hmass : ∀ n, ∑ q ∈ range (n + 1), source n q = 1)
    (htail : ∀ n c, c ≤ n → (∑ q ∈ range c, source n q) ≤ Λ * survival β c (n + 1))
    (hwindow : ∀ q, q < N → work w q - work w (frontier q) ≤ δ)
    (hmain : ∀ n, n < N → work w n - work w (start n) ≤ H)
    (hblock : ∀ t, t < N →
      (∑ n ∈ range N, if start n ≤ t ∧ t < n then w n else 0) ≤ H)
    (hD : (δ + H + Λ) * (δ + H + wmax + Λ) ≤ D ^ 2) :
    ∀ t ∈ range N,
      (∑ n ∈ range N, w n *
        (∑ j ∈ range N, w j * transportMass history (start n) n j 0 (source n)) *
        (w t * transportMass history (start n) n t 0 (source n))) ≤ D ^ 2 * w t := by
  let C := fun n t => w t * transportMass history (start n) n t 0 (source n)
  have hC : ∀ n ∈ range N, ∀ t ∈ range N, 0 ≤ C n t := by
    intro n _ t _
    apply mul_nonneg (hw t)
    exact (LongTails.Proofs.BirchCausalTransport.transportMass_bounds history (start n) n t
      0 (source n) (by norm_num) (hs n) (by simpa using hmass n)).1
  have hrow : ∀ n ∈ range N, (∑ j ∈ range N, C n j) ≤ δ + H + Λ := by
    intro n hn
    change (∑ j ∈ range N, w j * transportMass history (start n) n j 0 (source n)) ≤ _
    rw [transport_row_extended history w (source n) N n (start n)
      (by have := mem_range.mp hn; omega) (hstart n) hpast]
    apply transport_row history w β (source n) n (start n) δ H Λ (hstart n)
      hw hwβ hβ hβ1 hΛ (hs n) (hmass n) _ (hmain n (mem_range.mp hn)) (htail n)
    intro q hq
    exact (missingWork_le_window history w (frontier q) q (hfrontier q) (hprefix q) hw).trans
      (hwindow q (by have := mem_range.mp hn; omega))
  have hcol : ∀ t ∈ range N, (∑ n ∈ range N, w n * C n t) ≤
      (δ + H + wmax + Λ) * w t := by
    intro t ht
    obtain ⟨c, htc, hc, hrelease, hearly⟩ := exists_release history frontier w N t δ wmax
      (mem_range.mp ht) hpast hprefix hw hmax hwindow
    have hh := transport_column history w β source start N t c H (δ + wmax) Λ
      hpast hstart htc hc hw hwβ hβ hβ1 hΛ hs hmass htail hrelease hearly (hblock t (mem_range.mp ht))
    have hm := mul_le_mul_of_nonneg_right hh (hw t)
    simp only [sum_mul] at hm
    convert hm using 1
    · dsimp only [C]
      apply sum_congr rfl
      intro n _
      ring
    · ring
  exact LongTails.Proofs.BirchCausalTransport.row_column_certificate (range N) C w
    (δ + H + Λ) (δ + H + wmax + Λ) D (fun j _ => hw j) (by positivity) hC hrow hcol hD

end LongTails.Proofs.BirchRetainedTransport
