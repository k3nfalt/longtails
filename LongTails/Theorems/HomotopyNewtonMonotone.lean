import LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
import LongTails.Proofs.HomotopyNewtonBudget

namespace LongTails.Theorems.HomotopyNewtonMonotone

open OracleTemplate MeasureTheory
open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP
open LongTails.Proofs.HomotopyNewtonSchedule
open LongTails.Proofs.MonotoneTensorBounds
open LongTails.Proofs.HomotopyNewtonOuter
open LongTails.Proofs.HomotopyNewtonExecution
open LongTails.Proofs.HomotopyNewtonBudget

noncomputable def budget : (let S := LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 ^ 21 * (1 + (p.L * p.D ^ 3 / p.ε) ^ (1 / 4 : ℝ)) * Real.log (2 + p.H₀ * p.D / p.ε + p.L * p.D ^ 3 / p.ε) ^ 2⌉₊

theorem result :
    Convergence LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone.spec budget := by
  refine ⟨fun p => algorithm (p := p), ?_, fun _ _ => trivial⟩
  intro p hp F O hadm
  obtain ⟨hsmooth, hlip, hmono, hH0, xs, hxs, hD⟩ := hadm.2.2
  have hv : Valid p := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have hreg : Regular F p.L := ⟨hsmooth, hlip, hmono, hp.1.le⟩
  have hH : ∀ y ∈ Metric.closedBall p.x0 (5 * p.D), ‖fderiv ℝ F y‖ ≤ stiff p := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hg := hreg.jac_growth p.x0 y
    have hy2 : ‖y - p.x0‖ ^ 2 ≤ (5 * p.D) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
    unfold stiff
    nlinarith [mul_le_mul_of_nonneg_left hy2 hp.1.le]
  obtain ⟨hfacts, -, -⟩ := aep_invariant hreg hv hxs hD hH (outerCount p)
  have hticks := ticks_budget hv hreg hxs hD hH
  apply Filter.Eventually.of_forall
  rintro ⟨seed, ξ⟩
  change ‖F (execute O algorithm (budget p) seed ξ)‖ ≤ p.ε
  rw [execution_output p F O hadm (fun l hl => (hfacts l hl).succ) (budget p)
    (fun _ => Nat.cast_le.mp (hticks.trans (Nat.le_ceil _))) seed ξ]
  exact final_accuracy hreg hv hxs hD hH

end LongTails.Theorems.HomotopyNewtonMonotone
