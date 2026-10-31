import LongTails.Setups.AffineHeavyTailedAdam
import LongTails.Algorithms.AffineHeavyTailedAdam
import LongTails.Proofs.AffineAdamRate

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.FixedMemoryAdamAffineHeavyTails

open LongTails.Setups.AffineHeavyTailedAdam LongTails.Algorithms.AffineHeavyTailedAdam

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => (1 + ⌈(131072 * (q.σ1 + (∑ i, q.σ0 i) / q.ε)) ^ (q.p / (q.p - 1))⌉₊) * (1 + ⌈4294967296 * q.Δ * (q.L0 + q.L1 * q.ε) / q.ε ^ 2⌉₊)

theorem result : Convergence LongTails.Setups.AffineHeavyTailedAdam.spec budget := by
  refine ⟨fun q => method (config q) q.x0, ?_, ?_⟩
  · intro q hq f O hO
    obtain ⟨g, p, P, h_samples, rfl, hgrad, hlip, hgap, hg, hi, hm, hpi, hmom⟩ := hO
    have h := LongTails.Proofs.AffineAdamRate.output_accuracy q hq p P h_samples
      hg hgrad hlip hgap hi hm hpi hmom
    have hb : budget q = fun _ => (config q).batchSize * ((config q).lastIndex + 1) := by
      funext i
      norm_num [budget, config]
      ring
    rw [hb]
    exact h
  · intro q hq
    have h := LongTails.Proofs.AffineAdamParameters.tuning_pos q hq
    exact ⟨config q, by norm_num [config], by norm_num [config],
      by norm_num [config], by norm_num [config], h.1, h.2.1, h.2.2, rfl⟩

end LongTails.Theorems.FixedMemoryAdamAffineHeavyTails
