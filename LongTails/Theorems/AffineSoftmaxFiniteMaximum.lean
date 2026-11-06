import LongTails.Setups.SmoothFiniteMaximum
import LongTails.Algorithms.AffineSoftmaxFiniteMaximum
import LongTails.Proofs.AffineSoftmaxFiniteMaximum

namespace OracleTemplate.AffineSoftmaxFiniteMaximum

open LongTails.Setups.SmoothFiniteMaximum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => Nat.ceil (2000000000000000000000 * ((1 + Nat.clog 2 (Nat.ceil (2 + (p.m : ℝ) + p.G * p.R / p.ε + p.L * p.R ^ 2 / p.ε)) : ℕ) : ℝ) ^ 7 * ((p.m : ℝ) + p.m * (p.L * p.R ^ 2 / p.ε) ^ (1 / 3 : ℝ) + (p.m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (p.L * p.R ^ 2 / p.ε) + (p.m : ℝ) ^ (6 / 7 : ℝ) * (p.G * p.L * p.R ^ 3 / p.ε ^ 2) ^ (2 / 7 : ℝ) + p.G * p.R / p.ε))

theorem result : Convergence LongTails.Setups.SmoothFiniteMaximum.spec budget := by
  refine ⟨LongTails.Algorithms.AffineSoftmaxFiniteMaximum.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I oracle ha
  apply LongTails.Proofs.AffineSoftmaxFiniteMaximum.successful_execution p hp I oracle ha
  exact LongTails.Proofs.AffineSoftmaxPublicBudget.amplification_budget_le p.hm hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

end OracleTemplate.AffineSoftmaxFiniteMaximum
