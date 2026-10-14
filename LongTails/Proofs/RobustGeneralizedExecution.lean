import LongTails.Algorithms.RobustGeneralizedAccelerated
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling)
open StochasticGeneralized (prepare finish)
open StochasticGradient (advance)
open HeavyTailedMarkovGradient (advance_add)

noncomputable def replyPrefix {E : Type*} [Zero E] (n : ℕ) (v : ℕ → E) : ℕ → E :=
  fun i => if i < n then v i else 0

lemma replyPrefix_update {E : Type*} [Zero E] (n : ℕ) (v : ℕ → E) :
    Function.update (replyPrefix n v) n (v n) = replyPrefix (n+1) v := by
  classical
  ext i
  by_cases hi : i = n
  · subst i
    simp [replyPrefix]
  · by_cases hj : i < n
    · simp [Function.update_of_ne hi, replyPrefix, hj, show i < n+1 by omega]
    · simp [Function.update_of_ne hi, replyPrefix, hj, show ¬i < n+1 by omega]

lemma meanBlock_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (offset size : ℕ) {v w : ℕ → E} (h : ∀ i < size, v (offset+i) = w (offset+i)) :
    meanBlock offset size v = meanBlock offset size w := by
  unfold meanBlock
  congr 1
  exact Finset.sum_congr rfl (fun i _ => h i i.isLt)

lemma estimate_congr_prefix (p : Params) (a : ℝ) {v w : ℕ → p.E}
    (h : ∀ i < estimatorCost p a, v i = w i) : estimate p a v = estimate p a w := by
  have hp (i : Fin (pilotGroups p)) :
      meanBlock (i*pilotSize p a) (pilotSize p a) v =
        meanBlock (i*pilotSize p a) (pilotSize p a) w := by
    apply meanBlock_congr
    intro j hj
    apply h
    have hi := Nat.mul_le_mul_right (pilotSize p a) (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hi
    unfold estimatorCost
    omega
  have hm : meanBlock (pilotGroups p*pilotSize p a) (correctionSize p a) v =
      meanBlock (pilotGroups p*pilotSize p a) (correctionSize p a) w := by
    apply meanBlock_congr
    intro j hj
    apply h
    unfold estimatorCost
    omega
  dsimp only [estimate]
  rw [funext hp, hm]

lemma estimate_replyPrefix (p : Params) (a : ℝ) (v : ℕ → p.E) :
    estimate p a (replyPrefix (estimatorCost p a) v) = estimate p a v :=
  estimate_congr_prefix p a (fun i hi => by simp [replyPrefix, hi])

lemma estimatorCost_pos (p : Params) (a : ℝ) : 0 < estimatorCost p a := by
  have hm : 1 ≤ correctionSize p a := le_max_left _ _
  unfold estimatorCost
  omega

noncomputable def rawAdvance (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : State p.E) : State p.E :=
  advance (fun k state => (algorithm p).update state (g (((algorithm p).query state).2) (ξ k))) n call s

lemma rawAdvance_add (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (n m call : ℕ) (s : State p.E) :
    rawAdvance p g ξ (n+m) call s = rawAdvance p g ξ m (call+n) (rawAdvance p g ξ n call s) :=
  advance_add _ _ _ _ _

lemma rawAdvance_first_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (call j : ℕ) (hj : j < estimatorCost p (tentativeWeight s)) :
    rawAdvance p g ξ j call (.first s 0 (fun _ => 0)) =
      .first s j (replyPrefix j (fun i => g (coupling s) (ξ (call+i)))) := by
  induction j with
  | zero =>
    simp only [rawAdvance, advance]
    congr 1
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ↓reduceIte]
    rw [replyPrefix_update]

lemma rawAdvance_second_prefix (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Pending p.E) (call j : ℕ) (hj : j < estimatorCost p s.weight) :
    rawAdvance p g ξ j call (.second s 0 (fun _ => 0)) =
      .second s j (replyPrefix j (fun i => g s.point (ξ (call+i)))) := by
  induction j with
  | zero =>
    simp only [rawAdvance, advance]
    congr 1
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ↓reduceIte]
    rw [replyPrefix_update]

lemma rawAdvance_first_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (call : ℕ) :
    rawAdvance p g ξ (estimatorCost p (tentativeWeight s)) call (.first s 0 (fun _ => 0)) =
      .second (prepare p.L0 p.L1 s
        (estimate p (tentativeWeight s) (fun i => g (coupling s) (ξ (call+i))))) 0 (fun _ => 0) := by
  have hm := estimatorCost_pos p (tentativeWeight s)
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [he, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_first_prefix p g ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, he, Nat.succ_eq_add_one,
    lt_self_iff_false, ↓reduceIte, replyPrefix_update]
  rw [← Nat.succ_eq_add_one, ← he, estimate_replyPrefix]

lemma rawAdvance_second_block (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Pending p.E) (call : ℕ) :
    rawAdvance p g ξ (estimatorCost p s.weight) call (.second s 0 (fun _ => 0)) =
      resume p (finish s (estimate p s.weight (fun i => g s.point (ξ (call+i))))) := by
  have hm := estimatorCost_pos p s.weight
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [he, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_second_prefix p g ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, he, Nat.succ_eq_add_one,
    lt_self_iff_false, ↓reduceIte, replyPrefix_update]
  rw [← Nat.succ_eq_add_one, ← he, estimate_replyPrefix]

lemma rawAdvance_done (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (n call : ℕ) : rawAdvance p g ξ n call (.done s) = .done s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call+1)

lemma sampleEstimate_block (p : Params) (a : ℝ) (g : p.E → p.Ω → p.E)
    (x : p.E) (ξ : ℕ → p.Ω) (call : ℕ) :
    sampleEstimate p a g x (fun i : Fin (estimatorCost p a) => ξ (call+i)) =
      estimate p a (fun i => g x (ξ (call+i))) := by
  apply estimate_congr_prefix
  intro i hi
  simp only [sampleReplies, hi, ↓reduceDIte]

lemma rawAdvance_two_blocks (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (call : ℕ) :
    rawAdvance p g ξ (2*estimatorCost p (tentativeWeight s)) call (.first s 0 (fun _ => 0)) =
      resume p (StochasticGeneralized.step p.L0 p.L1
        (fun x => estimate p (tentativeWeight s) (fun i => g x (ξ (call+i))))
        (fun x => estimate p (tentativeWeight s)
          (fun i => g x (ξ (call+estimatorCost p (tentativeWeight s)+i)))) s) := by
  rw [show 2*estimatorCost p (tentativeWeight s) =
    estimatorCost p (tentativeWeight s)+estimatorCost p (tentativeWeight s) by omega,
    rawAdvance_add, rawAdvance_first_block]
  let v := estimate p (tentativeWeight s) (fun i => g (coupling s) (ξ (call+i)))
  have h := rawAdvance_second_block p g ξ (prepare p.L0 p.L1 s v)
    (call+estimatorCost p (tentativeWeight s))
  simp only [show (prepare p.L0 p.L1 s v).weight = tentativeWeight s from rfl] at h
  exact h

lemma sampleStep_two_blocks (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (call : ℕ) :
    sampleStep p g s (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i)) =
      StochasticGeneralized.step p.L0 p.L1
        (fun x => estimate p (tentativeWeight s) (fun i => g x (ξ (call+i))))
        (fun x => estimate p (tentativeWeight s)
          (fun i => g x (ξ (call+estimatorCost p (tentativeWeight s)+i)))) s := by
  have hd : 2*estimatorCost p (tentativeWeight s)/2 = estimatorCost p (tentativeWeight s) := by omega
  have hfirst (x : p.E) : sampleEstimate p (tentativeWeight s) g x
      (StochasticGeneralized.firstHalf (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i))) =
      estimate p (tentativeWeight s) (fun i => g x (ξ (call+i))) := by
    apply estimate_congr_prefix
    intro i hi
    have hib : i < 2*estimatorCost p (tentativeWeight s)/2 := by omega
    simp only [sampleReplies, hib, ↓reduceDIte, StochasticGeneralized.firstHalf]
  have hsecond (x : p.E) : sampleEstimate p (tentativeWeight s) g x
      (StochasticGeneralized.secondHalf (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i))) =
      estimate p (tentativeWeight s)
        (fun i => g x (ξ (call+estimatorCost p (tentativeWeight s)+i))) := by
    apply estimate_congr_prefix
    intro i hi
    have hib : i < 2*estimatorCost p (tentativeWeight s)/2 := by omega
    simp only [sampleReplies, ↓reduceDIte, StochasticGeneralized.secondHalf, hd, hi, Nat.add_assoc]
  unfold sampleStep
  simp_rw [hfirst, hsecond]

lemma rawAdvance_sampleStep (p : Params) (g : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω)
    (s : Iterate p.E) (call : ℕ) :
    rawAdvance p g ξ (2*estimatorCost p (tentativeWeight s)) call (.first s 0 (fun _ => 0)) =
      resume p (sampleStep p g s
        (fun i : Fin (2*estimatorCost p (tentativeWeight s)) => ξ (call+i))) := by
  rw [sampleStep_two_blocks]
  exact rawAdvance_two_blocks p g ξ s call

end OracleTemplate.RobustGeneralized
