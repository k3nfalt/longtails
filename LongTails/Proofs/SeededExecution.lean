import LongTails.Algorithms.Seeded
import LongTails.Proofs.SgdExecution

namespace OracleTemplate

open StochasticGradient

lemma advance_seeded {Q V U S : Type} [MeasurableSpace S]
    (A : Algorithm Q V U) (μ : MeasureTheory.ProbabilityMeasure S)
    (reply : ℕ → S → ℕ → A.State → V) (K k : ℕ) (seed : S) (s : A.State) :
    advance (fun j t => (seeded A μ).update t (reply j t.2.1 t.1 t.2.2)) K k (k,seed,s) =
      (k+K,seed,advance (fun j state => A.update state (reply j seed j state)) K k s) := by
  induction K generalizing k s with
  | zero => simp [advance, seeded]
  | succ K ih =>
    simp only [advance,seeded]
    simpa only [seeded,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (k+1) (A.update s (reply k seed k s))

end OracleTemplate
