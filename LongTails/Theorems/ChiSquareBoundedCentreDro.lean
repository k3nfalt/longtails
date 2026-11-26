import LongTails.Setups.ChiSquareConstrainedDro
import LongTails.Proofs.ChiSquareBoundedCentreDroConvergence

namespace OracleTemplate.ChiSquareBoundedCentreDro

open LongTails.Setups.ChiSquareConstrainedDro

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  let D := min q.B (q.G * q.R)
  let K := 1 + Nat.log 2 ⌊8 * q.B / q.ε⌋₊
  if D ≤ q.ε then 0 else K * (⌈256 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + 35 * q.B ^ 2) / q.ε ^ 2⌉₊ + 5)

theorem result : Convergence LongTails.Setups.ChiSquareConstrainedDro.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hq I O ha
  dsimp only
  unfold budget
  dsimp only
  by_cases h : min q.B (q.G * q.R) ≤ q.ε
  · rw [ite_eq_left h]
    exact initial_success q hq I O ha h
  · have HK := usedCalls_le_budget q hq.1
    rw [ite_eq_right h] at HK
    rw [ite_eq_right h]
    exact positive_success q hq I O ha h HK

end OracleTemplate.ChiSquareBoundedCentreDro
