import LongTails.Algorithms.CoarseGeneralizedWarmstart
import LongTails.Proofs.SgdExecution
import Mathlib.Tactic

namespace OracleTemplate.CoarseGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def SearchValid (t : Tuning) : Search E → Prop
  | .done _ => True
  | .left s => s.index < t.rounds
  | .right s => s.index < t.rounds
  | .bracket s _ _ _ r => s.index < t.rounds ∧ 0 < r

def searchRank (t : Tuning) : Search E → ℤ
  | .done _ => 0
  | .left s => ((t.rounds : ℤ) - s.index) * (t.depth + 2)
  | .right s => ((t.rounds : ℤ) - s.index) * (t.depth + 2) - 1
  | .bracket s _ _ _ r => ((t.rounds : ℤ) - s.index - 1) * (t.depth + 2) + r

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma resume_valid (t : Tuning) (s : Iterate E) : SearchValid t (resume t s) := by
  unfold resume
  split
  · trivial
  · exact Nat.lt_of_not_ge ‹_›

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma resume_rank (t : Tuning) (s : Iterate E) (hs : s.index ≤ t.rounds) :
    searchRank t (resume t s) = ((t.rounds : ℤ) - s.index) * (t.depth + 2) := by
  unfold resume
  split
  · have he : s.index = t.rounds := by omega
    simp [searchRank, he]
  · rfl

lemma finish_valid (t : Tuning) (s : Iterate E) (y h : E) : SearchValid t (finish t s y h) :=
  resume_valid _ _

lemma finish_rank (t : Tuning) (s : Iterate E) (y h : E) (hs : s.index < t.rounds) :
    searchRank t (finish t s y h) =
      ((t.rounds : ℤ) - s.index - 1) * (t.depth + 2) := by
  unfold finish
  rw [resume_rank _ _ (by change s.index + 1 ≤ t.rounds; omega)]
  simp only [advance, Nat.cast_add, Nat.cast_one]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma search_rank_pos (t : Tuning) (s : Search E) (hs : SearchValid t s)
    (hne : ∀ x, s ≠ .done x) : 0 < searchRank t s := by
  cases s with
  | done x => exact False.elim (hne x rfl)
  | left s =>
      change s.index < t.rounds at hs
      dsimp [searchRank]
      have hh : (s.index : ℤ) < t.rounds := by exact_mod_cast hs
      have hd : (0 : ℤ) ≤ t.depth := Int.natCast_nonneg _
      positivity
  | right s =>
      change s.index < t.rounds at hs
      dsimp [searchRank]
      have hh : (s.index : ℤ) + 1 ≤ t.rounds := by exact_mod_cast hs
      have hm := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ t.rounds - s.index by omega)
        (show (0 : ℤ) ≤ t.depth + 2 by omega)
      nlinarith
  | bracket s lo hi h r =>
      rcases hs with ⟨hs, hr⟩
      dsimp [searchRank]
      have hh : (s.index : ℤ) + 1 ≤ t.rounds := by exact_mod_cast hs
      have hr' : (0 : ℤ) < r := by exact_mod_cast hr
      have hm : (0 : ℤ) ≤ (t.rounds - s.index - 1) * (t.depth + 2) := by
        apply mul_nonneg <;> omega
      omega

lemma search_update_valid (t : Tuning) (s : Search E) (h : E) (hs : SearchValid t s) :
    SearchValid t (searchUpdate t s h) := by
  classical
  cases s with
  | done x => trivial
  | left s =>
      dsimp [searchUpdate, assess]
      split_ifs
      · trivial
      · exact finish_valid _ _ _ _
      · exact finish_valid _ _ _ _
      · exact hs
  | right s =>
      dsimp [searchUpdate, assess]
      split_ifs
      · trivial
      · exact finish_valid _ _ _ _
      · exact finish_valid _ _ _ _
      · exact finish_valid _ _ _ _
      · exact ⟨hs, Nat.pos_of_ne_zero ‹_›⟩
  | bracket s lo hi upper r =>
      rcases hs with ⟨hs, hr⟩
      dsimp [searchUpdate, assess]
      split_ifs
      · trivial
      · exact finish_valid _ _ _ _
      · exact finish_valid _ _ _ _
      · exact ⟨hs, by omega⟩
      · exact finish_valid _ _ _ _
      · exact ⟨hs, by omega⟩

lemma assess_rank_le (t : Tuning) (s : Iterate E) (y h : E) (next : Search E)
    {B : ℤ} (hB : 0 ≤ B) (hf : searchRank t (finish t s y h) ≤ B)
    (hn : searchRank t next ≤ B) : searchRank t (assess t s y h next) ≤ B := by
  classical
  unfold assess
  split_ifs
  · exact hB
  · exact hf
  · exact hn

lemma search_update_rank (t : Tuning) (s : Search E) (h : E) (hs : SearchValid t s)
    (hne : ∀ x, s ≠ .done x) :
    searchRank t (searchUpdate t s h) ≤ searchRank t s - 1 := by
  classical
  have hB : 0 ≤ searchRank t s - 1 := by have := search_rank_pos t s hs hne; omega
  cases s with
  | done x => exact False.elim (hne x rfl)
  | left s =>
      have hf (y : E) : searchRank t (finish t s y h) ≤ searchRank t (.left s) - 1 := by
        rw [finish_rank t s y h hs]
        dsimp [searchRank]
        nlinarith [Int.natCast_nonneg t.depth]
      dsimp only [searchUpdate]
      apply assess_rank_le _ _ _ _ _ hB (hf _)
      split_ifs
      · exact hf _
      · simp [searchRank]
  | right s =>
      have hf (y : E) : searchRank t (finish t s y h) ≤ searchRank t (.right s) - 1 := by
        rw [finish_rank t s y h hs]
        dsimp [searchRank]
        nlinarith [Int.natCast_nonneg t.depth]
      dsimp only [searchUpdate]
      apply assess_rank_le _ _ _ _ _ hB (hf _)
      split_ifs
      · exact hf _
      · exact hf _
      · dsimp [searchRank]; nlinarith
  | bracket s lo hi upper r =>
      rcases hs with ⟨hs, hr⟩
      have hf (y h' : E) : searchRank t (finish t s y h') ≤
          searchRank t (.bracket s lo hi upper r) - 1 := by
        rw [finish_rank t s y h' hs]
        dsimp [searchRank]
        have hr' : (1 : ℤ) ≤ r := by exact_mod_cast hr
        omega
      dsimp only [searchUpdate]
      apply assess_rank_le _ _ _ _ _ hB (hf _ _)
      split_ifs
      · exact hf _ _
      · dsimp [searchRank]; omega
      · exact hf _ _
      · dsimp [searchRank]; omega

lemma advance_done (t : Tuning) (reply : ℕ → E → E) (x : E) (n call : ℕ) :
    StochasticGradient.advance (fun k s => searchUpdate t s (reply k (searchPoint s)))
      n call (.done x) = .done x := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call + 1)

lemma search_terminal (t : Tuning) (reply : ℕ → E → E) (n call : ℕ) (s : Search E)
    (hs : SearchValid t s) (hn : searchRank t s ≤ (n : ℤ)) :
    ∃ x, StochasticGradient.advance (fun k s => searchUpdate t s (reply k (searchPoint s)))
      n call s = .done x := by
  classical
  induction n generalizing call s with
  | zero =>
      change ∃ x, s = .done x
      by_contra h
      push Not at h
      have hp := search_rank_pos t s hs h
      norm_num at hn
      omega
  | succ n ih =>
      by_cases hd : ∃ x, s = .done x
      · obtain ⟨x, rfl⟩ := hd
        exact ⟨x, advance_done t reply x (n + 1) call⟩
      · have hne : ∀ x, s ≠ .done x := by simpa using hd
        rw [StochasticGradient.advance]
        apply ih (call + 1) _ (search_update_valid t s _ hs)
        have hh := search_update_rank t s (reply call (searchPoint s)) hs hne
        push_cast at hn
        omega

lemma warm_terminal (t : Tuning) (reply : ℕ → E → E) (x0 : E) :
    ∃ x, StochasticGradient.advance (fun k s => searchUpdate t s (reply k (searchPoint s)))
      (t.rounds * (t.depth + 2)) 0 ((warmAlgorithm t x0).initial ()) = .done x := by
  apply search_terminal _ _ _ _ _ (resume_valid _ _)
  rw [resume_rank _ _ (Nat.zero_le _)]
  simp

lemma advance_append_step {State : Type*} (step : ℕ → State → State)
    (n call : ℕ) (s : State) :
    StochasticGradient.advance step (n + 1) call s =
      step (call + n) (StochasticGradient.advance step n call s) := by
  induction n generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ n ih =>
      rw [StochasticGradient.advance, ih]
      congr 1
      omega

end OracleTemplate.CoarseGeneralized
