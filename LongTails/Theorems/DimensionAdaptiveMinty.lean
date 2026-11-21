import LongTails.Setups.FiniteDimensionalWeakMinty
import LongTails.Proofs.MintyDimensionRun

open MeasureTheory

namespace LongTails.Theorems.DimensionAdaptiveMinty

open OracleTemplate LongTails.Setups.FiniteDimensionalWeakMinty
open LongTails.Algorithms.DimensionAdaptiveMinty LongTails.Proofs.MintyDimensionRun

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  2 * ⌈1024 * p.d * Real.log (1 + (p.L * p.R) ^ 2 / (p.d * p.ε ^ 2))⌉₊

theorem result : Convergence LongTails.Setups.FiniteDimensionalWeakMinty.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp F O had
  obtain ⟨ho, hl, z, _, hz, hm⟩ := had
  let n := ⌈1024 * p.d * Real.log (1 + (p.L * p.R / p.ε)^2 / p.d)⌉₊
  have hb : budget p = fun _ => 2 * n := by
    funext i
    simp only [budget, LongTails.Proofs.MintyDimensionBudget.scaled_ratio, n]
  have he (v : (algorithm p).Seed × ((k : ℕ) → O.Seed k)) :
      execute O (algorithm p) (budget p) v.1 v.2 = output p (trajectory p F n) :=
    by rw [hb]; exact execute_eq p F O ho n v.1 v.2
  apply constant_output _ F _ (output p (trajectory p F n)) p.ε he
  exact accuracy p hp F hl z hz hm n (Nat.le_ceil _)

end LongTails.Theorems.DimensionAdaptiveMinty
