import LongTails.Setups.WassersteinSmoothComposite
import LongTails.Proofs.WassersteinPotential

open MeasureTheory OracleTemplate
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Algorithms.WassersteinAcceleratedProximal
open LongTails.Proofs.WassersteinExecution
open LongTails.Proofs.WassersteinPotential

namespace LongTails.Theorems.WassersteinAcceleratedProximal

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 + 3 * ⌈2 * p.R * Real.sqrt (p.L / p.ε)⌉₊

theorem result : Convergence spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp I O hO
    obtain ⟨hL, hR, hε⟩ := hp
    apply Filter.Eventually.of_forall
    intro ω
    have hn : 2 * p.R * Real.sqrt (p.L / p.ε) ≤
        (⌈2 * p.R * Real.sqrt (p.L / p.ε)⌉₊ : ℝ) := Nat.le_ceil _
    have hh := run_accuracy hO hL hR hε ω.2
      (fun n q => executeAnswerAt O (algorithm p.toPublic) ω.1 ω.2 n (0, q))
      (response_correct hO ω.1 ω.2) ⌈2 * p.R * Real.sqrt (p.L / p.ε)⌉₊ hn
    change execute O (algorithm p.toPublic) (budget p) ω.1 ω.2 ∈ I.Q ∧
      objective I (execute O (algorithm p.toPublic) (budget p) ω.1 ω.2) -
        objective I I.minimizer ≤ p.ε
    unfold budget
    rw [execute_eq_run]
    exact hh
  · intro p hp
    trivial

end LongTails.Theorems.WassersteinAcceleratedProximal
