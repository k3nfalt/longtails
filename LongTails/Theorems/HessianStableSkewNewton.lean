import LongTails.Setups.HessianStableSkewMonotone
import LongTails.Proofs.BallAnchoredBudget

namespace LongTails.Theorems.HessianStableSkewNewton

open OracleTemplate MeasureTheory
open LongTails.Setups.HessianStableSkewMonotone
open LongTails.Algorithms.BallAnchoredNewton
open LongTails.Proofs.BallAnchoredInner
open LongTails.Proofs.BallAnchoredSearch
open LongTails.Proofs.BallAnchoredExecution
open LongTails.Proofs.BallAnchoredBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 17 * (1 + (p.pub.M * p.pub.D) ^ ((2 : ℝ) / 3)) * Real.log (3 + p.pub.M * p.pub.D + p.pub.M * p.Λ * (p.pub.D + 1 / p.pub.M) ^ 2 / p.pub.ε) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.HessianStableSkewMonotone.spec budget := by
  refine ⟨fun pub => algorithm (p := pub), ?_, fun _ _ => trivial⟩
  intro P hp F O hadm
  obtain ⟨hF, hJ, hdiff, ⟨S, hskew, hsa, hpsd, hstab⟩, ⟨xs, hxs, hx0, hbound⟩⟩ := hadm
  have hreg : Regular P.pub F S :=
    ⟨hp.1, hp.2.1, hp.2.2.1, fun x => (hdiff x).hasFDerivAt, hskew, hsa, hpsd, hstab⟩
  have hR : Region P.pub F xs P.Λ := ⟨hxs, hx0, hp.2.2.2, hbound⟩
  obtain ⟨n, hn, σ, hσ, hfin, hacc⟩ := run_finishes hreg hR
  have hpos : Pos P.pub P.Λ := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have hT : ∀ ch, n ≤ budget P ch := by
    intro ch
    have h1 : (totalBound P.pub P.Λ : ℝ) ≤ (budget P ch : ℝ) :=
      (total_le hpos).trans (Nat.le_ceil _)
    exact hn.trans (Nat.cast_le.mp h1)
  apply Filter.Eventually.of_forall
  rintro ⟨seed, ξ⟩
  change ‖F (execute O algorithm (budget P) seed ξ)‖ ≤ P.pub.ε
  rw [execution_output P F O hF hJ (budget P) n hT σ hσ hfin seed ξ]
  exact hacc

end LongTails.Theorems.HessianStableSkewNewton
