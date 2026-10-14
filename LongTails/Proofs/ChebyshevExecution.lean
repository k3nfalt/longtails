import LongTails.Proofs.ChebyshevBatching
import LongTails.Proofs.AcceleratedMarkovExecution

open scoped BigOperators

namespace OracleTemplate.BatchedChebyshev

open StochasticGradient HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_prefix (g : E → Ω → E) (L : ℝ) (T M : ℕ) (x0 : E) (ξ : ℕ → Ω)
    {i : ℕ} (hiT : i ≤ T) (call : ℕ) (x : E) (j : ℕ) (hj : j < batch T M i) :
    advance (fun k s => (algorithm L T M x0).update s (g s.point (ξ k))) j call
      (⟨i, 0, x, 0⟩ : State E) =
      ⟨i, j, x, ∑ l ∈ Finset.range j, g x (ξ (call + l))⟩ := by
  induction j with
  | zero => simp [advance, algorithm, BatchedSGD.algorithm]
  | succ j ih =>
    erw [advance_add (K := j) (J := 1), ih (by omega)]
    simp only [advance, algorithm, BatchedSGD.algorithm, ite_eq_left hiT, ite_eq_left hj,
      Finset.sum_range_succ]

lemma advance_batch (g : E → Ω → E) (L : ℝ) (T M : ℕ) (x0 : E) (ξ : ℕ → Ω)
    {i : ℕ} (hiT : i ≤ T) (call : ℕ) (x : E) :
    advance (fun k s => (algorithm L T M x0).update s (g s.point (ξ k)))
      (batch T M i) call (⟨i, 0, x, 0⟩ : State E) =
      ⟨i + 1, 0, batchUpdate L T M i g x (fun j => ξ (call + j)), 0⟩ := by
  have hb := batch_pos T M i
  have he : batch T M i = (batch T M i - 1) + 1 := by omega
  conv_lhs => rw [he]
  erw [advance_add (K := batch T M i - 1) (J := 1),
    advance_prefix g L T M x0 ξ hiT call x _ (by omega)]
  simp only [advance, algorithm, BatchedSGD.algorithm, div_div, ite_eq_left hiT,
    show ¬batch T M i - 1 + 1 < batch T M i by omega, ite_false]
  congr 1
  unfold batchUpdate
  congr 2
  change _ = ∑ j : Fin (batch T M i), g x (ξ (call + j.val))
  have hsum := Fin.sum_univ_eq_sum_range (fun l : ℕ => g x (ξ (call + l))) (batch T M i)
  rw [hsum, he, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]

lemma advance_run (g : E → Ω → E) (L : ℝ) (T M : ℕ) (x0 : E) (ξ : ℕ → Ω)
    (n i call : ℕ) (x : E) (horizon : i + n ≤ T + 1) :
    advance (fun k s => (algorithm L T M x0).update s (g s.point (ξ k)))
      (calls T M n i) call (⟨i, 0, x, 0⟩ : State E) =
      ⟨i + n, 0, run L T M g n i x (fun j => ξ (call + j)), 0⟩ := by
  induction n generalizing i call x with
  | zero => simp [calls, run, advance, algorithm, BatchedSGD.algorithm]
  | succ n ih =>
    erw [calls, advance_add, advance_batch g L T M x0 ξ (by omega)]
    erw [ih (i + 1) (call + batch T M i) _ (by omega)]
    simp only [run]
    congr 1
    · omega
    · congr 1
      funext j
      simp only [Nat.add_comm, Nat.add_left_comm]

lemma advance_finished (g : E → Ω → E) (L : ℝ) (T M : ℕ) (x0 : E) (ξ : ℕ → Ω)
    (n call : ℕ) (s : State E) (hs : T < s.iteration) :
    (advance (fun k q => (algorithm L T M x0).update q (g q.point (ξ k))) n call s).point =
      s.point := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
    let s' := (algorithm L T M x0).update s (g s.point (ξ call))
    have hs' : T < s'.iteration := by
      by_cases hb : s.count + 1 < batch T M s.iteration
      · simpa [s', algorithm, BatchedSGD.algorithm, hb] using hs
      · simp only [s', algorithm, BatchedSGD.algorithm, ite_eq_right hb]
        omega
    have hp : s'.point = s.point := by
      by_cases hb : s.count + 1 < batch T M s.iteration
      · simp [s', algorithm, BatchedSGD.algorithm, hb]
      · simp [s', algorithm, BatchedSGD.algorithm, hb, not_le.mpr hs]
    simp only [advance]
    exact (ih (call + 1) s' hs').trans hp

lemma calls_eq_sum (T M n i : ℕ) :
    calls T M n i = ∑ j ∈ Finset.range n, batch T M (i + j) := by
  induction n generalizing i with
  | zero => simp [calls]
  | succ n ih =>
    rw [calls, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm]

lemma calls_le (T M : ℕ) : calls T M T 1 ≤ 2 * T + M := by
  by_cases hT : T = 0
  · subst T
    simp [calls]
  · rw [calls_eq_sum]
    simpa only [Nat.add_comm 1] using batch_sum_le (Nat.pos_of_ne_zero hT) M

lemma execute_algorithm [MeasurableSpace Ω] (p : MeasureTheory.ProbabilityMeasure Ω)
    (g : E → Ω → E) (L : ℝ) (T M : ℕ) (x0 : E) (K : ℕ)
    (hK : calls T M T 1 ≤ K) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := ⟨MeasureTheory.Measure.infinitePi (fun _ : ℕ =>
                (p : MeasureTheory.Measure Ω)), inferInstance⟩
              answer := fun _ (_, x) seed => g x seed }
      (algorithm L T M x0) (fun _ => K) () ξ = run L T M g T 1 x0 ξ := by
  erw [execute_advance]
  change (advance (fun k s => (algorithm L T M x0).update s (g s.point (ξ k)))
    K 0 (⟨1, 0, x0, 0⟩ : State E)).point = _
  erw [show K = calls T M T 1 + (K - calls T M T 1) by omega,
    advance_add, advance_run g L T M x0 ξ T 1 0 x0 (by omega)]
  simp only [Nat.zero_add]
  exact (advance_finished g L T M x0 ξ _ _ _ (by simp))

end OracleTemplate.BatchedChebyshev
