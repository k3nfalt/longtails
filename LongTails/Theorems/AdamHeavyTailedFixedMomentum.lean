import LongTails.Setups.HeavyTailedAdam
import LongTails.Proofs.AdamHeavyTailedRate

namespace OracleTemplate.AdamHeavyTailedFixedMomentum

open LongTails.Setups.HeavyTailedAdam

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 1 + ⌈400000000 * q.Δ * q.L / q.ε ^ 2 * (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedAdam.spec budget := by
  let makeAlgorithm := fun q : Params =>
    let ρ := 1 / (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))
    let τ := q.ε / (100000 * Real.sqrt ρ)
    let η := τ * ρ / (100000 * q.L)
    let n := ⌈400000000 * q.Δ * q.L / q.ε ^ 2 * (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))⌉₊
    Adam.method (9 / 10) ρ η τ n q.x0
  refine ⟨makeAlgorithm, ?_, ?_⟩
  · rintro q ⟨hL, hσ, hα, hα2, hΔ, hε⟩ f O
      ⟨g, p, P, h_samples, rfl, hf, hlip, hgap, hg, hgi, hmean, hm, hmass⟩
    have hh := LongTails.Proofs.AdamHeavyTailedRate.execution_accuracy p P h_samples hg hgi
      hf hL hΔ hσ hε hlip hα hα2 hmean hm hmass q.x0 hgap
    have hbudget : budget q = fun _ =>
        ⌈400000000 * q.Δ * q.L / q.ε ^ 2 * (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))⌉₊ + 1 := by
      funext i
      dsimp [budget]
      omega
    simp only [spec, makeAlgorithm, hbudget]
    convert hh using 1 <;> rfl
  · rintro q ⟨hL, hσ, hα, _, _, hε⟩
    let ρ := 1 / (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))
    let τ := q.ε / (100000 * Real.sqrt ρ)
    let η := τ * ρ / (100000 * q.L)
    let n := ⌈400000000 * q.Δ * q.L / q.ε ^ 2 * (1000000000000 + (100000 * q.σ / q.ε) ^ (q.α / (q.α - 1)))⌉₊
    have htune := LongTails.Proofs.AdamHeavyTailedTuning.tuning_parameters hσ hε hα
    have hρ : 0 < ρ := htune.1
    have hρ1 : ρ ≤ 1 := by linarith [htune.2.1]
    have hτ : 0 < τ := hε.trans_le htune.2.2.1
    have hη : 0 < η := by dsimp [η]; positivity
    exact ⟨9 / 10, ρ, η, τ, n, by norm_num, by norm_num, hρ, hρ1, hη, hτ, rfl⟩

end OracleTemplate.AdamHeavyTailedFixedMomentum
