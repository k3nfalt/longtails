import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LogisticPathLocality

open LongTails.Setups.TwoSampleQuadraticPerceptron

noncomputable def edgeForce {d : ℕ} (m : ℕ) (u : ℕ → Features d) (q : ℕ → ℝ) :
    Features d := ∑ i ∈ Finset.range m, q i • (u i - u (i+1))

lemma edgeForce_by_parts {d : ℕ} (n : ℕ) (u : ℕ → Features d) (q : ℕ → ℝ) :
    edgeForce (n+1) u q = q 0 • u 0 - q n • u (n+1) +
      ∑ j ∈ Finset.range n, (q (j+1) - q j) • u (j+1) := by
  induction n with
  | zero => simp [edgeForce, smul_sub]
  | succ n ih =>
    rw [show edgeForce (n+1+1) u q = edgeForce (n+1) u q +
      q (n+1) • (u (n+1) - u (n+1+1)) by simp only [edgeForce, Finset.sum_range_succ],
      ih, Finset.sum_range_succ, sub_smul, smul_sub]
    abel

lemma weighted_interior {d n j : ℕ} (hj : j < n) (u : ℕ → Features d) (v : Features d)
    (q : ℕ → ℝ) (k τ : ℝ) (hl : ⟪u 0,v⟫ = τ) (hr : ⟪u (n+1),v⟫ = -τ)
    (hd : ∀ i < n, ⟪u (i+1),v⟫ = if i=j then k else 0) :
    ⟪edgeForce (n+1) u q, v⟫ = (q 0 + q n)*τ + (q (j+1)-q j)*k := by
  rw [edgeForce_by_parts]
  simp only [inner_add_left, inner_sub_left, sum_inner, real_inner_smul_left, hl, hr]
  rw [Finset.sum_eq_single j]
  · rw [hd j hj, ite_eq_left rfl]
    ring
  · intro i hi hij
    simp [hd i (Finset.mem_range.mp hi), hij]
  · simp [hj]

lemma chain_sum {d : ℕ} (u : ℕ → Features d) (k n : ℕ) :
    ∑ i ∈ Finset.range n, (u (k+i) - u (k+i+1)) = u k - u (k+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_succ]
    abel

lemma boundary_force {d n : ℕ} (hn : 4 ≤ n) (u : ℕ → Features d) (q : ℕ → ℝ)
    (L N M R : ℝ) (hl : q 0 = L) (hr : q (n-1) = R)
    (hnl : q 1 = N) (hnr : q (n-2) = N)
    (hm : ∀ i, 2 ≤ i → i+2 < n → q i = M) :
    edgeForce n u q = L • u 0 + (N-L) • u 1 + (M-N) • u 2 -
      (M-N) • u (n-2) + (R-N) • u (n-1) - R • u n := by
  obtain ⟨k, hk⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  subst n
  simp only [show k+4-1=k+3 by omega, show k+4-2=k+2 by omega] at hr hnr ⊢
  unfold edgeForce
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
  have mid : (∑ j ∈ Finset.range k, q (j+1+1) • (u (j+1+1)-u (j+1+1+1))) =
      M • (u 2-u (k+2)) := by
    trans ∑ j ∈ Finset.range k, M • (u (j+1+1)-u (j+1+1+1))
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hm _ (by omega) (by have := Finset.mem_range.mp hj; omega)]
    · rw [← Finset.smul_sum]
      congr 1
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using chain_sum u 2 k
  rw [mid, hl, hr, hnl, hnr]
  module

end LongTails.Proofs.LogisticPathLocality
