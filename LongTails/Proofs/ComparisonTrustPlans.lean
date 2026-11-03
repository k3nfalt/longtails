import LongTails.Algorithms.ComparisonTrustRegion
import LongTails.Proofs.QueryPlan

namespace LongTails.Proofs.ComparisonTrustPlans

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion

variable {E S : Type*}

lemma eval_loop (g : E × E → Bool) (c : ℕ) (step : ℕ → S → Plan E S c) (k i : ℕ) (s : S) :
    QueryPlan.eval g (loop c step k i s) =
      loopPure (fun i s => QueryPlan.eval g (step i s)) k i s := by
  induction k generalizing i s with
  | zero => rfl
  | succ k ih =>
    simp only [loop, loopPure, QueryPlan.eval_bind, ih]

lemma loopPure_succ (step : ℕ → S → S) (k i : ℕ) (s : S) :
    loopPure step (k + 1) i s = step (i + k) (loopPure step k i s) := by
  induction k generalizing i s with
  | zero => rfl
  | succ k ih =>
    rw [loopPure, ih (i + 1) (step i s), loopPure]
    congr 1
    omega

lemma loopPure_induction (step : ℕ → S → S) (P : ℕ → S → Prop) (s : S) (h0 : P 0 s)
    (hstep : ∀ k s, P k s → P (k + 1) (step k s)) (k : ℕ) : P k (loopPure step k 0 s) := by
  induction k with
  | zero => simpa [loopPure] using h0
  | succ k ih =>
    rw [loopPure_succ, zero_add]
    exact hstep k _ ih

lemma eval_cmpPlan (g : E × E → Bool) (a b : E) : QueryPlan.eval g (cmpPlan a b) = g (a, b) := rfl

end LongTails.Proofs.ComparisonTrustPlans
