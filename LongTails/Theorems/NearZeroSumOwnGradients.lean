import LongTails.Setups.NearZeroSumGames
import LongTails.Proofs.NearZeroSumConvergence

open MeasureTheory

namespace OracleTemplate.NearZeroSum.OwnGradients

open LongTails.Setups.NearZeroSumGames

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈16777216 * p.L / min p.μ p.ν * Real.sqrt ((min p.μ p.ν + p.δ) / (p.μ + p.ν + p.δ)) * Real.log (2 + p.D ^ 2 / p.ε) * Real.log (2 + 524288 * p.L ^ 2 * p.D ^ 2 / ((min p.μ p.ν) ^ 2 * p.ε))⌉₊

theorem result : Convergence LongTails.Setups.NearZeroSumGames.spec budget := by
  refine ⟨nearZeroSumGameOutput, ?_, by intros; trivial⟩
  intro p hp I oracle hadm
  rcases hp with ⟨hX, hY, hcX, hcY, hx0, hy0, hdiam, hμ, hμL, hν, hνL, hδ, hδL, hD, hε⟩
  rcases hadm with ⟨hstrongX, hstrongY, hconvexG, ⟨s, hs⟩, H, G, P, hgradH, hgradG,
    hplus, hminus, hgradLip, hproj, hfield, hproject⟩
  have geom : GameGeometry p I H G := ⟨hcX, hcY, hstrongX, hstrongY, hconvexG, hgradH, hgradG, hgradLip⟩
  have hP : ConstrainedMonotone.Proj (domain p) P := ⟨fun u => (hproj u).1, fun u => (hproj u).2⟩
  have hC := (domain_compact hX hY).isComplete
  have hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖ownGradient H G u - ownGradient H G v‖ ≤ 2 * p.L * ‖u - v‖ := by
    intro u hu v hv
    exact own_gradient_lipschitz (p := p) (H := H) (G := G) (z := u) (w := v)
      (hplus u hu v hv) (hminus u hu v hv)
  have hns := equilibrium_normal hcX hcY hs (hgradH s hs.1) (hgradG s hs.1)
  have haccuracy := oriented_game_accuracy geom hC hP hμ hν hμL hνL hδ hδL hD.le hε
    hlip hdiam (initialPoint p) s ⟨hx0, hy0⟩ hs.1 hns
  have hcost := game_calls_bound p hμ hν hμL hνL hδ hδL hε
  let m := min p.μ p.ν
  let β := m + 16 * p.δ
  let cfg := tunedFoamConfig p.L (max p.μ p.ν) m p.δ p.D p.ε
  let N := ⌈2 * (m + β) / m * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
  refine ⟨s, hs, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ω⟩
  cases seed
  have he := execute_oriented_proximalFoam (ownGradient H G) P hP cfg β N (budget p 0)
    (initialPoint p) ⟨hx0, hy0⟩ (decide (p.μ < p.ν)) oracle hfield hproject ω hcost
  change execute oracle (orientedProximalFoam cfg β N (initialPoint p) (decide (p.μ < p.ν)))
      (fun _ => budget p 0) () ω ∈ domain p ∧
    ‖execute oracle (orientedProximalFoam cfg β N (initialPoint p) (decide (p.μ < p.ν)))
      (fun _ => budget p 0) () ω - s‖ ^ 2 ≤ p.ε
  rw [he]
  exact haccuracy

end OracleTemplate.NearZeroSum.OwnGradients
