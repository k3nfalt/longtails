import LongTails.Algorithms.StochasticGeneralizedAccelerated
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending coupling)
open StochasticGradient (advance)
open HeavyTailedMarkovGradient (advance_add)

noncomputable def rawAdvance (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : State p.E) : State p.E :=
  advance (fun k state => (algorithm p).update state (g (((algorithm p).query state).2) (ξ k))) n call s

lemma rawAdvance_add (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n m call : ℕ) (s : State p.E) :
    rawAdvance p g ξ (n+m) call s = rawAdvance p g ξ m (call+n) (rawAdvance p g ξ n call s) :=
  advance_add _ _ _ _ _

lemma rawAdvance_first_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (m call j : ℕ) (hj : j < m) :
    rawAdvance p g ξ j call (.first s m 0 0) =
      .first s m j (∑ i ∈ Finset.range j, g (coupling s) (ξ (call+i))) := by
  induction j with
  | zero => simp [rawAdvance, advance]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ite_true, Finset.sum_range_succ]

lemma rawAdvance_second_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Pending p.E) (m call j : ℕ) (hj : j < m) :
    rawAdvance p g ξ j call (.second s m 0 0) =
      .second s m j (∑ i ∈ Finset.range j, g s.point (ξ (call+i))) := by
  induction j with
  | zero => simp [rawAdvance, advance]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ite_true, Finset.sum_range_succ]

lemma rawAdvance_first_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (m call : ℕ) (hm : 0 < m) :
    rawAdvance p g ξ m call (.first s m 0 0) =
      .second (prepare p.L0 p.L1 s (batchReply g (coupling s) (fun i : Fin m => ξ (call+i)))) m 0 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_eq_add_one]
  rw [rawAdvance_add, rawAdvance_first_prefix p g ξ s (j+1) call j (by omega)]
  simp only [rawAdvance, advance, algorithm, lt_self_iff_false, ite_false]
  congr 2
  unfold batchReply
  rw [← Finset.sum_range_succ, Finset.sum_range]

lemma rawAdvance_second_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Pending p.E) (m call : ℕ) (hm : 0 < m) :
    rawAdvance p g ξ m call (.second s m 0 0) =
      resume p (finish s (batchReply g s.point (fun i : Fin m => ξ (call+i)))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_eq_add_one]
  rw [rawAdvance_add, rawAdvance_second_prefix p g ξ s (j+1) call j (by omega)]
  simp only [rawAdvance, advance, algorithm, lt_self_iff_false, ite_false]
  congr 2
  unfold batchReply
  rw [← Finset.sum_range_succ, Finset.sum_range]

lemma rawAdvance_done (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (n call : ℕ) : rawAdvance p g ξ n call (.done s) = .done s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call+1)

lemma rawAdvance_two_batches (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (m call : ℕ) (hm : 0 < m) :
    rawAdvance p g ξ (2*m) call (.first s m 0 0) =
      resume p (step p.L0 p.L1 (fun x => batchReply g x (fun i : Fin m => ξ (call+i)))
        (fun x => batchReply g x (fun i : Fin m => ξ (call+m+i))) s) := by
  rw [show 2*m=m+m by omega, rawAdvance_add, rawAdvance_first_block p g ξ s m call hm,
    rawAdvance_second_block p g ξ _ m (call+m) hm]
  rfl

lemma prefixStep_two_batches (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (m call : ℕ) :
    prefixStep p.L0 p.L1 g s (fun i : Fin (2*m) => ξ (call+i)) =
      step p.L0 p.L1 (fun x => batchReply g x (fun i : Fin m => ξ (call+i)))
        (fun x => batchReply g x (fun i : Fin m => ξ (call+m+i))) s := by
  simp only [prefixStep, step, batchReply, firstHalf, secondHalf, Nat.add_assoc]
  rw [show 2*m/2=m by omega]

lemma rawAdvance_prefixStep (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (m call : ℕ) (hm : 0 < m) :
    rawAdvance p g ξ (2*m) call (.first s m 0 0) =
      resume p (prefixStep p.L0 p.L1 g s (fun i : Fin (2*m) => ξ (call+i))) := by
  rw [prefixStep_two_batches]
  exact rawAdvance_two_batches p g ξ s m call hm

end OracleTemplate.StochasticGeneralized
