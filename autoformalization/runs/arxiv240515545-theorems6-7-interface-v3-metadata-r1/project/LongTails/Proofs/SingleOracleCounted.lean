import LongTails.Proofs.SgdExecution

namespace OracleTemplate

def executeCounted {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → O.Seed k) : Output × ℕ :=
  (execute O A (fun _ => K) seed ξ, K)

lemma executeCounted_advance {Query Reply Output : Type*} (O : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    executeCounted O A K seed ξ =
      (A.output (StochasticGradient.advance
        (fun k state => A.update state (O.answer k (A.query state) (ξ k)))
        K 0 (A.initial seed)), K) := by
  rw [executeCounted, StochasticGradient.execute_advance]

end OracleTemplate
