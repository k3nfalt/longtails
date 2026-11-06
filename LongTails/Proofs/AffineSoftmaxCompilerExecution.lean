import LongTails.Algorithms.AffineSoftmaxCompiler
import LongTails.Proofs.AffineSoftmaxQuerySafety

namespace LongTails.Proofs.AffineSoftmaxCompilerExecution

open MeasureTheory
open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxCompiler
open AffineSoftmaxQuerySafety

lemma execute_program_eq_eval {E Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (m : ℕ) [NeZero m] (initial : E)
    (plan : Ω → Program (Fin m × E) (ℝ × E) E) (oracle : Oracle (Fin m × E) (ℝ × E))
    (reply : Fin m × E → ℝ × E) (X : Set E) (hi : initial ∈ X)
    (hreply : ∀ history seed i x, x ∈ X → oracle.answer history (0, (i, x)) seed = reply (i, x))
    (K : ℕ) (seed : Ω) (oracleSeed : (k : ℕ) → oracle.Seed k)
    (hq : QueriesWithin reply (fun q => q.2 ∈ X) (plan seed)) (hc : Program.cost reply (plan seed) ≤ K) :
    output P m initial plan oracle K seed oracleSeed = Program.eval reply (plan seed) := by
  let A := programAlgorithm P m initial plan
  let step := fun p : Program (Fin m × E) (ℝ × E) E => p.update (reply (p.query (0, initial)))
  let state := fun k => step^[k] (plan seed)
  let T := Program.cost reply (plan seed)
  have hs k : QueriesWithin reply (fun q => q.2 ∈ X) (state k) :=
    queriesWithin_iterate reply _ (0, initial) k (plan seed) hq
  apply execute_eq_of_safe_prefix oracle A (fun _ => K) seed oracleSeed state (fun k _ => K - k) T
    (Program.eval reply (plan seed))
  · rfl
  · intro history
    have hx := queriesWithin_query reply _ (state history.length) (0, initial) hi (hs history.length)
    change state (history.length + 1) = (state history.length).update
      (oracle.answer history (0, (state history.length).query (0, initial)) (oracleSeed history.length))
    rw [hreply history (oracleSeed history.length) _ _ hx]
    exact Function.iterate_succ_apply' step history.length (plan seed)
  · rfl
  · intro k
    funext i
    have he : i = 0 := Fin.eq_zero i
    subst i
    simp only [programAlgorithm, A, Function.update_self]
    omega
  · intro k hk
    change k < Program.cost reply (plan seed) at hk
    omega
  · intro k hk
    have he := Program.iterate_of_cost_le reply (0, initial) k (plan seed) hk
    change Program.output initial (state k) = _
    rw [show state k = .done (Program.eval reply (plan seed)) from he]
    rfl
  · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul] using hc

end LongTails.Proofs.AffineSoftmaxCompilerExecution
