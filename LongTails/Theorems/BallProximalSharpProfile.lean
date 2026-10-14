import LongTails.Setups.ConvexBallProximal
import LongTails.Proofs.BallProximalSharpness

open MeasureTheory

namespace OracleTemplate.BallProximal

open LongTails.Setups.ConvexBallProximal

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈min ((p.R / p.t) ^ 2) ((p.R / p.t) * Real.sqrt (min (1 / 2) (max 0 (1 - p.ε / p.Δ)) ^ 2 + max 0 (Real.log (p.Δ / (2 * p.ε))) / 2))⌉₊

theorem result : Convergence LongTails.Setups.ConvexBallProximal.spec budget := by
  refine ⟨fun p => algorithm p.x0, ?_, ?_⟩
  · intro p hv I O h
    obtain ⟨z, hz, hmin, hR, hΔ⟩ := h.2.2.2.2
    refine ⟨z, hz, hmin, Filter.Eventually.of_forall ?_⟩
    rintro ⟨seed, ξ⟩
    let K := ⌈min ((p.R / p.t) ^ 2) ((p.R / p.t) * Real.sqrt (accuracyCoefficient p.Δ p.ε))⌉₊
    change execute O (algorithm p.x0) (fun _ => K) seed ξ ∈ I.C ∧
      I.f (execute O (algorithm p.x0) (fun _ => K) seed ξ) - I.f z ≤ p.ε
    rw [execute_algorithm]
    exact ⟨iterate_feasible p I O h ξ K, execution_accuracy p I O hv h ξ hz hR hΔ le_rfl⟩
  · intro p hv
    rfl

end OracleTemplate.BallProximal
