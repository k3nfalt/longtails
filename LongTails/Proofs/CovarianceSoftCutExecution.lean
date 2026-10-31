import LongTails.Algorithms.CovarianceSoftCutMethod
import LongTails.Proofs.CovarianceSoftCutTrajectory
import LongTails.Proofs.CovarianceSoftCutTournament
import LongTails.Proofs.Execution

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutExecution

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open OracleTemplate

def prefixReplies (q : Params) (k : ℕ) (replies : ℕ → Space q) : ℕ → Space q :=
  fun i => if i < k then replies i else 0

lemma prefixReplies_agrees (q : Params) (k : ℕ) (replies : ℕ → Space q) (i : ℕ) (hi : i < k) :
    prefixReplies q k replies i = replies i := by simp [prefixReplies, hi]

lemma update_prefixReplies (q : Params) (k : ℕ) (replies : ℕ → Space q) :
    Function.update (prefixReplies q k replies) k (replies k) = prefixReplies q (k+1) replies := by
  funext i
  by_cases hi : i = k
  · subst i
    simp [prefixReplies]
  · by_cases hik : i < k
    · have hi' : i < k+1 := by omega
      simp [Function.update_of_ne hi, prefixReplies, hik, hi']
    · have hi' : ¬ i < k+1 := by omega
      simp [Function.update_of_ne hi, prefixReplies, hik, hi']

lemma execute_historyMethod (q : Params) (query : ℕ → (ℕ → Space q) → Space q)
    (output : (ℕ → Space q) → Space q)
    (hquery : ∀ k r s, (∀ i, i < k → r i = s i) → query k r = query k s)
    (O : Oracle (Space q) (Space q)) (N : ℕ) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → (Fin 1 × Space q) → Space q)
    (hanswer : ∀ history point, O.answer history point (ξ history.length) = response history.length point)
    (replies : ℕ → Space q)
    (hresponse : ∀ i, i < N → response i (0, query i replies) = replies i)
    (houtput : ∀ r s, (∀ i, i < N → r i = s i) → output r = output s) :
    execute O (historyMethod q query output) (fun _ => N) () ξ = output replies := by
  let A := historyMethod q query output
  let step := fun sc : A.State × ℕ => (A.update sc.1 (response sc.2 (A.query sc.1)), sc.2+1)
  have hi (k : ℕ) (hk : k ≤ N) : step^[k] (A.initial (), 0) = ((k, prefixReplies q k replies), k) := by
    induction k with
    | zero =>
      rw [Function.iterate_zero_apply]
      change ((0, fun _ : ℕ => (0 : Space q)), 0) = ((0, prefixReplies q 0 replies), 0)
      congr 2
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      change ((k+1, Function.update (prefixReplies q k replies) k
        (response k (0, query k (prefixReplies q k replies)))), k+1) = _
      rw [hquery k (prefixReplies q k replies) replies (prefixReplies_agrees q k replies),
        hresponse k (by omega), update_prefixReplies]
  rw [execute_indexed_of_answer O (historyMethod q query output) N () ξ response hanswer]
  change output (step^[N] (A.initial (), 0)).1.2 = _
  rw [hi N le_rfl]
  exact houtput _ replies (prefixReplies_agrees q N replies)

open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutTrajectory
open LongTails.Proofs.CovarianceSoftCutTournament

lemma leaves_prefix (q : Params) (c : Config) (r s : ℕ → Space q)
    (heq : ∀ i, i < generatorCost c → r i = s i) : leaves q c r = leaves q c s := by
  funext i
  unfold leaves
  split_ifs with hi
  · apply generatorPoint_eq_of_prefix
    intro j hj
    exact heq j (lt_of_lt_of_le hj (Nat.mul_le_mul_right c.b hi.le))
  · rfl

lemma method_query_prefix (q : Params) (c : Config) (t : ℕ) (r s : ℕ → Space q)
    (heq : ∀ i, i < t → r i = s i) : query q c t r = query q c t s := by
  unfold query
  split_ifs with hg hw
  · apply generatorPoint_eq_of_prefix
    intro i hi
    exact heq i (lt_of_lt_of_le hi (Nat.div_mul_le_self t c.b))
  · have hcost : generatorCost c ≤ t := Nat.le_of_not_gt hg
    have hl := leaves_prefix q c r s (fun i hi => heq i (lt_of_lt_of_le hi hcost))
    rw [hl]
    congr 1
    apply selectionProbe_prefix
    intro i hi
    apply heq
    have hb := Nat.div_mul_le_self (t-generatorCost c) (c.n*c.m)
    change generatorCost c+i < t
    omega
  · rfl

lemma method_output_prefix (q : Params) (c : Config) (N : ℕ) (hN : workCost c ≤ N)
    (r s : ℕ → Space q) (heq : ∀ i, i < N → r i = s i) : output q c r = output q c s := by
  have hgen : generatorCost c ≤ N := by unfold workCost at hN; omega
  have hl := leaves_prefix q c r s (fun i hi => heq i (lt_of_lt_of_le hi hgen))
  unfold output
  rw [hl]
  apply selectionOutput_prefix
  intro i hi
  apply heq
  change i < selectionCost c at hi
  unfold workCost at hN
  omega

end LongTails.Proofs.CovarianceSoftCutExecution
