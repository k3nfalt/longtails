import LongTails.Setups.WeakMintySecondOrder
import LongTails.Proofs.WeakMintyHybridExecution

namespace OracleTemplate.WeakMintyHybrid.FullRangeSecondOrderWeakMinty

open LongTails.Setups.WeakMintySecondOrder

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈1048576 * (1 + q.L₂ * q.R ^ 2 / q.ε) * Real.log (2 / (1 - q.ρ * q.L₁ / 2)) / (1 - q.ρ * q.L₁ / 2) ^ 5⌉₊

theorem result : Convergence LongTails.Setups.WeakMintySecondOrder.spec budget := by
  refine ⟨fun p => hybrid p.L₁ p.L₂ p.ρ p.ε p.x0, ?_, fun _ _ => trivial⟩
  intro q hq F oracle hadm
  rcases hq with ⟨hL₁, hL₂, hρ, hρL, hR, hε⟩
  rcases hadm with ⟨J, hF, hJ, hder, hjlip, hlip, z, _, hdist, hm⟩
  have h : Hyp F J q.L₁ q.L₂ q.ρ z := ⟨hder, hjlip, hlip, hm⟩
  let δ := 1 - q.ρ * q.L₁ / 2
  let N := ⌈16384 * (q.L₂ * q.R ^ 2 / q.ε) / δ ^ 4⌉₊ + 1
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hN : ‖q.x0 - z‖ ^ 2 < N * ((margin q.L₁ q.ρ) ^ 4 * q.ε / (16384 * q.L₂)) :=
    iteration_sufficient hδ hL₂ hε (norm_nonneg _) hdist
  have hK : N * (innerCount (margin q.L₁ q.ρ) + 2) ≤ budget q 0 :=
    total_budget hδ hδ1 (by positivity : 0 ≤ q.L₂ * q.R ^ 2 / q.ε)
  exact Filter.Eventually.of_forall (fun seed =>
    execute_accurate h hL₁ hL₂ hρ hρL hε q.x0 hN hK oracle hF hJ seed.1 seed.2)

end OracleTemplate.WeakMintyHybrid.FullRangeSecondOrderWeakMinty
