import LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox
import LongTails.Proofs.BlackBoxFinal

namespace OracleTemplate.BlackBoxDiagonal

open LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => q.d + 1 + ⌈21 * Real.sqrt (2 / q.μ) * (Real.log (1 + q.Δ / (q.μ ^ 2 * q.ε)) + (q.d + 1) * (3 + Real.logb 2 (1 / q.μ)) ^ 4)⌉₊

theorem result : Convergence LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun q => q.d + 1 + ⌈21 * Real.sqrt (2 / q.μ) * (Real.log (1 + q.Δ / (q.μ ^ 2 * q.ε)) + (q.d + 1) * (3 + Real.logb 2 (1 / q.μ)) ^ 4)⌉₊)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hμ, hμ1, hw, _, hε⟩ K hK f oracle ⟨_, hor, hsmooth, hsc, ⟨xstar, hmin, hgap⟩⟩
  have Hy : BHyp f q.w q.μ := ⟨hw, hμ, hμ1, hsmooth, hsc⟩
  have hexec (seed : (algorithm q.toPublic).Seed × ((k : ℕ) → oracle.Seed k)) :
      execute oracle (algorithm q.toPublic) (fun _ => K) seed.1 seed.2 =
        ((stepOf f q.x0)^[K] (initial q.x0)).base := by
    rw [execute_eq_of_answer_eq oracle (fun x => (f x, gradient f x))
      (fun k x sample => hor k sample x)]
    exact (execute_iterate (fun x => (f x, gradient f x)) (algorithm q.toPublic) K seed.1).trans rfl
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  intro seed
  change f (execute oracle (algorithm q.toPublic) (fun _ => K) seed.1 seed.2) - f xstar ≤ q.ε
  rw [hexec]
  exact accurate_after Hy q.x0 hmin hgap hε K hK

end OracleTemplate.BlackBoxDiagonal
