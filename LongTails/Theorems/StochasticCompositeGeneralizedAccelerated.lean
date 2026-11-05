import LongTails.Setups.StochasticCompositeGeneralizedSmooth
import LongTails.Proofs.StochasticCompositeGeneralizedCost
import LongTails.Proofs.StochasticCompositeGeneralizedConvergence

open MeasureTheory Set
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ (128 + 128 / (p.α - 1)) * (1 + Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * p.G) * p.R ^ 2 / p.ε) + (1 + p.L1 * p.R) * Real.log (2 + (1 + p.L1 * p.R) * Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) + (p.σ * p.R / p.ε) ^ (p.α / (p.α - 1))) * (Real.log ((8 + p.L1 * p.R + (p.L0 + 192 * p.L1 * p.σ + p.L1 * p.G) * p.R ^ 2 / p.ε + p.Δ / (p.L0 * p.R ^ 2) + p.σ * p.R / p.ε) / p.δ)) ^ (2 + 1 / (p.α - 1))⌉₊

theorem result : Convergence LongTails.Setups.StochasticCompositeGeneralizedSmooth.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro p ⟨hL0, hL1, hR, hΔ, hG, hσ, hα, hα2, hε, hδ, hδ1⟩ I O
    ⟨g, μ, P, hIID, rfl, hc, hg, hcont, hsmooth, hQ, _hQm, hψ, _hψm, hproxMeas, hprox, hx,
      ⟨xs, hxs, hmin, hd, hgap, hGx⟩, ho⟩
  have hyp : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1 :=
    ⟨hL0, hL1, hc, hg, hcont, hsmooth, hQ, hψ, hprox⟩
  let K := ⌈20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * p.G) * p.R ^ 2 / p.ε) + (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) * Real.sqrt (p.Δ / (p.L0 * p.R ^ 2)))⌉₊
  have hK : 20 * Real.sqrt ((p.L0 + 192 * p.L1 * p.σ + p.L1 * p.G) * p.R ^ 2 / p.ε) +
      (6 + 256 * p.L1 * p.R) * Real.log (2 + (3 + 192 * p.L1 * p.R) *
        Real.sqrt (p.Δ / (p.L0 * p.R ^ 2))) ≤ K := Nat.le_ceil _
  have hB (ξ : ℕ → p.Ω) : StochasticGeneralized.blockCalls (phaseCost p.toPublic) (phaseNext p.toPublic I g)
      (initialState p.toPublic) ξ (4 * K) ≤ budget p 0 :=
    explicit_call_budget p.toPublic I g p.G hG hL0 hL1 hR hσ hα hα2 hΔ hε hδ hδ1 ξ
  have hO : ({ Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) seed => match query with | .gradient x => g x seed | .prox a z v => I.prox a z v } : Oracle (Query p.toPublic) p.E) =
      { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) seed => oracleReply p.toPublic I g query seed } := by
    congr 1
    funext history query seed
    rcases query with ⟨i, query⟩
    cases query <;> rfl
  erw [hO]
  have hbf : budget p = (fun _ => budget p 0) := by
    funext i
    rfl
  rw [hbf]
  refine ⟨?_, xs, hxs, hmin, ?_⟩
  · convert measurable_execute_output p.toPublic I hL0 hL1 hR hσ hΔ ho.measurable hproxMeas P (budget p 0) using 1 <;> rfl
  convert execution_high_probability p.toPublic I (μ : Measure _) ho hyp hR hσ hα hα2 hΔ hε hδ hδ1
    xs hxs hmin hx hd hgap hGx P hIID hproxMeas K (budget p 0) hK hB using 1; rfl

end OracleTemplate.StochasticCompositeGeneralized
