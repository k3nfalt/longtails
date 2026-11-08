import LongTails.Proofs.BirchCollectionSampling
import LongTails.Proofs.BirchRetainedRenewal
import LongTails.Proofs.BirchRetainedTransport

namespace LongTails.Proofs.BirchCollectionWeights

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionSampling (CollectionOrdering)
open LongTails.Proofs.BirchRetainedRenewal
open LongTails.Proofs.BirchRetainedWork (survival survival_nonnegative)

lemma ordering_parameters (s : TraceState) (o : CollectionOrdering) (K : ℕ)
    (hp : CollectionParameters s) (hc : CompletedLedger s) (ho : o.Valid s K) :
    ∀ n, 0 ≤ o.movement s n ∧ o.movement s n ≤ o.refresh s n ∧ o.refresh s n ≤ 1 := by
  intro n
  by_cases hn : n < o.labels.length
  · have hlabel := ho.2.2.2.2.2.2.1 n hn
    simpa only [Ordering.movement, Ordering.refresh, hn, ite_true] using
      (direction_parameters s hp hc (o.label n) hlabel).2
  · simp [Ordering.movement, Ordering.refresh, hn]

lemma structural_renewal_bounds (s : TraceState) (o : CollectionOrdering) (c : Controls)
    (K B : ℕ) (hp : CollectionParameters s) (hc : CompletedLedger s) (hh : Histories s)
    (hs : Structural s o c K B) (n : ℕ) (hn : n < o.labels.length) :
    (∀ q, q ≤ n →
      0 ≤ renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q ∧
      renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q ≤
        o.refresh s q) ∧
    (∑ q ∈ range (n + 1),
      renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q) = 1 ∧
    (∀ cutoff, cutoff ≤ n →
      (∑ q ∈ range cutoff,
        renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q) ≤
        2 * survival (o.refresh s) cutoff (n + 1)) := by
  have ho := hs.1
  have hparams := ordering_parameters s o K hp hc ho
  obtain ⟨_, _, _, _, _, _, _, _, _, hrenew⟩ := hs
  obtain ⟨hrn, hreset, _, _, hdata⟩ := hrenew n hn
  apply renewal_row_bounds (o.history s) ho.2.2.2.2.2.2.2.2 (o.refresh s)
    (o.anchor n) n (o.renewalFrontier n) (o.scale n) 2 hrn
    (fun j => (hparams j).1.trans (hparams j).2.1) (fun j => (hparams j).2.2)
    hreset (by norm_num) (hdata _ (le_refl _)).2.1
    (ordering_history_closed s o K hh ho)
    (fun j hj => (hdata j hj).1) (fun j hj => (hdata j hj).2.2.1)
    (fun j hj => (hdata j hj).2.2.2.1)
  · intro j hj i hi
    apply (mem_after (o.anchor n) i (o.history s (o.anchor n + j))).mpr
    exact (hdata j hj).2.2.2.2.1 i (mem_range.mp hi)
  · intro j hj
    exact (hdata j hj).2.2.2.2.2

noncomputable def row (s : TraceState) (o : CollectionOrdering)
    (hpast : ∀ n, o.history s n ⊆ range n) (n q : ℕ) : ℝ :=
  if n < o.labels.length then
    if q ≤ n then renewalRow (o.history s) hpast (o.refresh s) (o.anchor n) n q else 0
  else if q = n then 1 else 0

lemma structural_row_bounds (s : TraceState) (o : CollectionOrdering) (c : Controls)
    (K B : ℕ) (hp : CollectionParameters s) (hc : CompletedLedger s) (hh : Histories s)
    (hs : Structural s o c K B) :
    let W := row s o hs.1.2.2.2.2.2.2.2.2
    (∀ n q, 0 ≤ W n q) ∧
    (∀ n, n < o.labels.length → ∀ q, q ≤ n → W n q ≤ o.refresh s q) ∧
    (∀ n, ∑ q ∈ range (n + 1), W n q = 1) ∧
    (∀ n cutoff, cutoff ≤ n → (∑ q ∈ range cutoff, W n q) ≤
      2 * survival (o.refresh s) cutoff (n + 1)) := by
  have hr := structural_renewal_bounds s o c K B hp hc hh hs
  have hparams := ordering_parameters s o K hp hc hs.1
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n q
    by_cases hn : n < o.labels.length
    · by_cases hq : q ≤ n
      · simpa only [row, hn, hq, ite_true] using (hr n hn).1 q hq |>.1
      · simp [row, hn, hq]
    · simp only [row, hn, ite_false]
      split_ifs <;> norm_num
  · intro n hn q hq
    simpa only [row, hn, hq, ite_true] using (hr n hn).1 q hq |>.2
  · intro n
    by_cases hn : n < o.labels.length
    · calc
        _ = ∑ q ∈ range (n + 1),
            renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q := by
          apply sum_congr rfl
          intro q hq
          simp [row, hn, show q ≤ n by have := mem_range.mp hq; omega]
        _ = 1 := (hr n hn).2.1
    · simp [row, hn]
  · intro n cutoff hcutoff
    by_cases hn : n < o.labels.length
    · calc
        _ = ∑ q ∈ range cutoff,
            renewalRow (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s) (o.anchor n) n q := by
          apply sum_congr rfl
          intro q hq
          simp [row, hn, show q ≤ n by have := mem_range.mp hq; omega]
        _ ≤ _ := (hr n hn).2.2 cutoff hcutoff
    · have hzero : (∑ q ∈ range cutoff, row s o hs.1.2.2.2.2.2.2.2.2 n q) = 0 := by
        apply sum_eq_zero
        intro q hq
        have hqn : q ≠ n := by have := mem_range.mp hq; omega
        simp [row, hn, hqn]
      rw [hzero]
      exact mul_nonneg (by norm_num) (survival_nonnegative (o.refresh s)
        (fun j => (hparams j).2.2) cutoff (n + 1))

noncomputable def extendedMomentum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (β : ℕ → ℝ) (reply momentum : ℕ → E) (N n : ℕ) : E :=
  if n < N then momentum n else ∑ j ∈ range N, β j • (reply j - momentum j)

lemma extendedMomentum_rec {E : Type*} [AddCommGroup E] [Module ℝ E]
    (history : ℕ → Finset ℕ) (hpast : ∀ n, history n ⊆ range n)
    (β : ℕ → ℝ) (reply momentum : ℕ → E) (N : ℕ)
    (hβ : ∀ n, N ≤ n → β n = 0) (hh : ∀ n, N ≤ n → history n = range n)
    (hrec : ∀ n, n < N → momentum n = ∑ j ∈ history n, β j • (reply j - momentum j)) :
    ∀ n, extendedMomentum β reply momentum N n =
      ∑ j ∈ history n, β j • (reply j - extendedMomentum β reply momentum N j) := by
  intro n
  by_cases hn : n < N
  · rw [extendedMomentum, ite_eq_left hn, hrec n hn]
    apply sum_congr rfl
    intro j hj
    have hjN : j < N := (mem_range.mp (hpast n hj)).trans hn
    simp [extendedMomentum, hjN]
  · have hNn : N ≤ n := by omega
    rw [extendedMomentum, ite_eq_right hn, hh n hNn]
    calc
      _ = ∑ j ∈ range N, β j • (reply j - extendedMomentum β reply momentum N j) := by
        apply sum_congr rfl
        intro j hj
        simp [extendedMomentum, mem_range.mp hj]
      _ = ∑ j ∈ range n, β j • (reply j - extendedMomentum β reply momentum N j) := by
        apply sum_subset (range_mono hNn)
        intro j _ hj
        have hNj : N ≤ j := by simpa only [mem_range, not_lt] using hj
        rw [hβ j hNj, zero_smul]

lemma structural_estimator_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : TraceState) (o : CollectionOrdering) (c : Controls) (K B : ℕ)
    (hs : Structural s o c K B) (reply momentum : ℕ → E)
    (hrec : ∀ n, n < o.labels.length → momentum n =
      ∑ j ∈ o.history s n, o.refresh s j • (reply j - momentum j))
    (n : ℕ) (hn : n < o.labels.length) :
    (1 - o.refresh s n) • momentum n + o.refresh s n • reply n =
      ∑ q ∈ range (n + 1), row s o hs.1.2.2.2.2.2.2.2.2 n q • reply q := by
  let v := extendedMomentum (o.refresh s) reply momentum o.labels.length
  have hv := extendedMomentum_rec (o.history s) hs.1.2.2.2.2.2.2.2.2 (o.refresh s)
    reply momentum o.labels.length
    (fun j hj => by simp [Ordering.refresh, show ¬j < o.labels.length by omega])
    (fun j hj => by simp [Ordering.history, show ¬j < o.labels.length by omega]) hrec
  have hrenew := hs.2.2.2.2.2.2.2.2.2 n hn
  obtain ⟨hrn, hreset, hanchor, hprefix, _⟩ := hrenew
  have he := renewal_estimator_expansion (o.history s) hs.1.2.2.2.2.2.2.2.2
    (0 : E) (o.refresh s) reply v (o.anchor n) n hrn hreset hanchor hprefix
    (fun j => by simpa only [zero_add] using hv j)
  have hvn : v n = momentum n := by simp [v, extendedMomentum, hn]
  rw [hvn] at he
  rw [he]
  apply sum_congr rfl
  intro q hq
  simp [row, hn, show q ≤ n by have := mem_range.mp hq; omega]

end LongTails.Proofs.BirchCollectionWeights
