import LongTails.Setups.RhoSmoothRadiusConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.RhoSmoothUpperRun

namespace LongTails.Theorems.RhoSmoothConvexUpperBound

open OracleTemplate LongTails.Setups.RhoSmoothRadiusConvex LongTails.Algorithms.RhoSmoothThreePhase
open LongTails.Proofs.RhoSmoothLocal LongTails.Proofs.RhoSmoothPhaseOne
open LongTails.Proofs.RhoSmoothUpperRun

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let G := (p.L0 / p.L1) ^ (1 / p.ρ)
  ⌈9 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + 262144 * (1 + (p.L0 * p.R / G) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.RhoSmoothRadiusConvex.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p hp N hN f oracle ⟨hc, hg, hgd, hH, u, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have H : Hyp f g p.L0 p.L1 p.ρ :=
    ⟨hp.1, hp.2.1, by linarith [hp.2.2.1], hc, hg [] seed0, hgd [] seed0, hH [] seed0⟩
  refine ⟨u, hmin, MeasureTheory.ae_of_all _ fun seed => ?_⟩
  have hexec : execute oracle (algorithm p) (fun _ => N) seed.1 seed.2 =
      point ((trans p g)^[N] (.cut p.x0)) := by
    rw [execute_eq_of_answer_eq oracle g
      (fun k x sample => (hg k sample x).unique (hg [] seed0 x))]
    exact execute_iterate g (algorithm p) N seed.1
  change f (execute oracle (algorithm p) (fun _ => N) seed.1 seed.2) - f u ≤ p.ε
  rw [hexec]
  exact run_accuracy p hp H hmin N (budget_sufficient p hp N hN) hdist

end LongTails.Theorems.RhoSmoothConvexUpperBound
