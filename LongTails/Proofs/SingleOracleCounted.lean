import LongTails.Proofs.SgdExecution

namespace OracleTemplate

def executeCounted {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → O.Seed k) : Output × ℕ :=
  (execute O A (fun _ => K) seed ξ, K)

lemma executeCounted_advance {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → O.Seed k) (response : ℕ → (Fin 1 × Query) → Reply)
    (h : ∀ history query, O.answer history query (ξ history.length) =
      response history.length query) :
    executeCounted O A K seed ξ =
      (A.output (StochasticGradient.advance
        (fun k state => A.update state (response k (A.query state)))
        K 0 (A.initial seed)), K) := by
  rw [executeCounted, StochasticGradient.execute_advance_of_answer O A K seed ξ response h]

end OracleTemplate
