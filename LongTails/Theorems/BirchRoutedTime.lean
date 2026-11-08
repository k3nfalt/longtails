import LongTails.Setups.BirchRoutedTime
import LongTails.Proofs.BirchResourcePublic

namespace LongTails.Theorems.BirchRoutedTime

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchRoutedTime
open LongTails.Algorithms.BirchCollections (algorithm)
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourcePublic

noncomputable def budget : (let S := LongTails.Setups.BirchRoutedTime.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun p _ => (1 + ⌈240 * p.geometry.L * p.geometry.Δ / (1 / 8 * p.geometry.ε)⌉₊) * (1 + ⌈32 * p.geometry.κ * p.geometry.σ ^ 2 / p.geometry.ε⌉₊)

lemma budget_eq (p : Params) : budget p = fun _ => rounds p * block p := by
  funext _
  simp [budget, rounds, block, LongTails.Setups.BirchCollections.horizon,
    LongTails.Setups.BirchCollections.batchSize, tuned, controls]

noncomputable def controller (p : Params) :
    Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ) := by
  classical
  exact if hp : Valid p then
    let l := routedPlan p hp
    clocked (algorithm (compiledParams p.geometry l.layout l.positive)) (rounds p * window p)
  else clocked (algorithm (tuned p.geometry)) 0

theorem result : Convergence spec budget := by
  classical
  refine ⟨controller, ?_, ?_⟩
  · intro p hp I O hI
    let l := routedPlan p hp
    have hc : controller p = clocked (algorithm (compiledParams p.geometry l.layout l.positive))
        (rounds p * window p) := by
      unfold controller
      exact dite_eq_left hp
    have h := clocked_success p.geometry l.layout l.positive l.valid hp.1
      (rounds p * window p) I O hI
    dsimp only at h
    rw [l.paid] at h
    rw [budget_eq]
    have hgen (A : Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ))
        (he : A = clocked (algorithm (compiledParams p.geometry l.layout l.positive))
          (rounds p * window p)) :
        spec.successful p I (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          execute O A (fun _ => rounds p * block p) z.1 z.2)
          ⟨((A.law : Measure _).prod (O.law : Measure _)), inferInstance⟩ := by
      subst A
      exact h
    exact hgen (controller p) hc
  · intro p hp
    let l := routedPlan p hp
    refine ⟨l.jobs, l.layout, l.positive, l.legal, l.window, l.unit, l.parent, ?_⟩
    unfold controller
    exact dite_eq_left hp

end LongTails.Theorems.BirchRoutedTime
