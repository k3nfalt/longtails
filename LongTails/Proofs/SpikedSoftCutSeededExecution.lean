import LongTails.Proofs.SpikedSoftCutEpochProcess

namespace LongTails.Proofs.SpikedSoftCutSeededExecution

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutEpochProcess
open SpikedSoftCutMethodExecution

noncomputable def seededReplies (q : Params) (c : Config) (g : Space q → q.Ω → Space q) :
    ℕ → ℕ → OuterState q → (ℕ → q.Ω) → ℕ → Space q
  | _, 0, _, ξ, i => g 0 (ξ i)
  | k, remaining+1, s, ξ, i =>
    if i < epochCost c k then epochReplies q c k s g ξ i
    else seededReplies q c g (k+1) remaining (nextState q c k s (epochReplies q c k s g ξ))
      (fun j => ξ (epochCost c k+j)) (i-epochCost c k)

noncomputable def terminalState (q : Params) (c : Config) (g : Space q → q.Ω → Space q) :
    ℕ → ℕ → OuterState q → (ℕ → q.Ω) → OuterState q
  | _, 0, s, _ => s
  | k, remaining+1, s, ξ => terminalState q c g (k+1) remaining
      (nextState q c k s (epochReplies q c k s g ξ)) (fun j => ξ (epochCost c k+j))

lemma seededReplies_prefix (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (k remaining : ℕ) (s : OuterState q) (ξ : ℕ → q.Ω) (i : ℕ) (hi : i < epochCost c k) :
    seededReplies q c g k (remaining+1) s ξ i = epochReplies q c k s g ξ i := by
  simp only [seededReplies, hi, ite_true]

lemma seededReplies_tail (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (k remaining : ℕ) (s : OuterState q) (ξ : ℕ → q.Ω) :
    (fun i => seededReplies q c g k (remaining+1) s ξ (epochCost c k+i)) =
      seededReplies q c g (k+1) remaining (nextState q c k s (epochReplies q c k s g ξ))
        (fun j => ξ (epochCost c k+j)) := by
  funext i
  have hi : ¬epochCost c k+i < epochCost c k := by omega
  simp only [seededReplies, hi, ite_false, Nat.add_sub_cancel_left]

lemma seededReplies_nextState (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (g : Space q → q.Ω → Space q) (k remaining : ℕ) (s : OuterState q) (ξ : ℕ → q.Ω) :
    nextState q c k s (seededReplies q c g k (remaining+1) s ξ) =
      nextState q c k s (epochReplies q c k s g ξ) :=
  nextState_prefix q c hT hn k s _ _ (seededReplies_prefix q c g k remaining s ξ)

lemma queryFrom_first_epoch (q : Params) (c : Config) (k remaining : ℕ)
    (s : OuterState q) (r : ℕ → Space q) (i : ℕ) (hi : i < epochCost c k) :
    queryFrom q c k (remaining+1) s r i = queryFrom q c k 1 s r i := by
  simp only [queryFrom, hi, ite_true]

lemma seededReplies_response (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (hb : 0 < c.b) (g : Space q → q.Ω → Space q) (remaining k : ℕ)
    (s : OuterState q) (ξ : ℕ → q.Ω) (i : ℕ) :
    g (queryFrom q c k remaining s (seededReplies q c g k remaining s ξ) i) (ξ i) =
      seededReplies q c g k remaining s ξ i := by
  induction remaining generalizing k s ξ i with
  | zero => rfl
  | succ remaining ih =>
    by_cases hi : i < epochCost c k
    · rw [seededReplies_prefix q c g k remaining s ξ i hi, queryFrom_first_epoch q c k remaining s _ i hi]
      have hq := queryFrom_prefix q c hT hn 1 k s
        (seededReplies q c g k (remaining+1) s ξ) (epochReplies q c k s g ξ) i
        (fun j hj => seededReplies_prefix q c g k remaining s ξ j (lt_trans hj hi))
      rw [hq]
      exact epochReplies_response q c hb k s g ξ i hi
    · have hg : ¬i < c.T*c.b := by unfold epochCost at hi; omega
      simp only [queryFrom, hg, ite_false, hi]
      rw [seededReplies_nextState q c hT hn, seededReplies_tail]
      have hh := ih (k+1) (nextState q c k s (epochReplies q c k s g ξ))
        (fun j => ξ (epochCost c k+j)) (i-epochCost c k)
      have he : epochCost c k+(i-epochCost c k) = i := by omega
      simpa only [he, seededReplies, hi, ite_false] using hh

lemma seeded_output (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (g : Space q → q.Ω → Space q) (remaining k : ℕ) (s : OuterState q) (ξ : ℕ → q.Ω) :
    outputFrom q c k remaining s (seededReplies q c g k remaining s ξ) =
      saved q (terminalState q c g k remaining s ξ) := by
  induction remaining generalizing k s ξ with
  | zero => rfl
  | succ remaining ih =>
    simp only [outputFrom, terminalState]
    rw [seededReplies_nextState q c hT hn, seededReplies_tail]
    exact ih _ _ _

end LongTails.Proofs.SpikedSoftCutSeededExecution
