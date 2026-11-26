import LongTails.Setups.HighDimensionalHessianStableSkewMonotone
import LongTails.Proofs.BallAnchoredBudget
import LongTails.Proofs.HsExecution

namespace LongTails.Theorems.HessianStableExpectedNewton

open OracleTemplate MeasureTheory
open LongTails.Setups.HighDimensionalHessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredExecution
open LongTails.Proofs.BallAnchoredBudget
open LongTails.Proofs.HsExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 17 * (1 + (p.M * p.D) ^ ((2 : ℝ) / 3)) * Real.log (3 + p.M * p.D + p.M * p.Λ * (p.D + 1 / p.M) ^ 2 / p.ε) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.HighDimensionalHessianStableSkewMonotone.spec budget := by
  refine ⟨fun pub => algorithm (p := (toGeneral pub).pub), ?_, fun _ _ => trivial⟩
  intro P hp F O hadm
  obtain ⟨hF, hJ, hdiff, ⟨S, hskew, hsa, hpsd, hstab⟩, ⟨xs, hxs, hx0, hbound⟩⟩ := hadm
  have hp0 := hp.1
  have hreg : Regular (toGeneral P).pub F S :=
    ⟨hp0.1, hp0.2.1, hp0.2.2.1, fun x => (hdiff x).hasFDerivAt, hskew, hsa, hpsd, hstab⟩
  have hR : Region (toGeneral P).pub F xs (toGeneral P).Λ := ⟨hxs, hx0, hp0.2.2.2, hbound⟩
  obtain ⟨n, hn, σ, hσ, hfin, hacc⟩ := run_finishes hreg hR
  have hpos : Pos (toGeneral P).pub (toGeneral P).Λ := ⟨hp0.1, hp0.2.1, hp0.2.2.1, hp0.2.2.2⟩
  have hT : ∀ ch, n ≤ budget P ch := by
    intro ch
    have h1 : (totalBound (toGeneral P).pub (toGeneral P).Λ : ℝ) ≤ (budget P ch : ℝ) :=
      (total_le hpos).trans (Nat.le_ceil _)
    exact hn.trans (Nat.cast_le.mp h1)
  exact const_success _ _ ‖F σ.z‖ P.ε
    (fun ω => congrArg (fun z => ‖F z‖)
      (execution_output (toGeneral P) F O hF hJ (budget P) n hT σ hσ hfin ω.1 ω.2)) hacc

end LongTails.Theorems.HessianStableExpectedNewton
