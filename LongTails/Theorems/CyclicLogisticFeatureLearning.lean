import LongTails.Setups.CyclicLogisticFeatureLearning
import LongTails.Algorithms.CyclicLogisticFeatureLearning
import LongTails.Proofs.CyclicLogisticExecution

namespace OracleTemplate.CyclicLogisticFeatureLearning

open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Algorithms.CyclicLogisticFeatureLearning
open LongTails.Proofs.CyclicLogisticExecution
open LongTails.Proofs.CyclicLogisticTuning

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let L := 1 + Real.log (2 + p.n / (p.μ * p.κ))
  p.n * (⌈8388608 * (p.n : ℝ) ^ 2 * L ^ 2 / (p.ρ * p.μ * p.κ ^ 2)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.CyclicLogisticFeatureLearning.spec budget := by
  refine ⟨algorithm, ?_, fun p hp => compliant p (tuned p hp).positive⟩
  rintro p hp D O ⟨G, ha⟩
  change ∀ (ω : Unit × ((k : ℕ) → O.Seed k)) (i : Fin p.n), 0 < (answer p D
    (i, execute O (algorithm p) (budget p) ω.1 ω.2)).margin
  rintro ⟨⟨⟩, ξ⟩ i
  have hb : budget p = fun _ => (horizon p + 1) * p.n := by
    funext j
    exact (congrArg (fun k : ℕ => p.n.val * (k + 1)) (horizon_eq p).symm).trans (Nat.mul_comm ..)
  have h := output_correct D hp G O (fun history q ω => ha history (0,q) ω) ξ i i.isLt
  rw [hb]
  change 0 < (answer p D (i, output p O ((horizon p + 1) * p.n) ξ)).margin
  exact h

end OracleTemplate.CyclicLogisticFeatureLearning
