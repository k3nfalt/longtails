import LongTails.Setups.UscgHighProbability
import LongTails.Proofs.UscgSharpGuarantee
import LongTails.Proofs.UscgSharpLowerResult

open MeasureTheory

namespace LongTails.Theorems.SharpMomentumFiniteVarianceHighProbability

open OracleTemplate
open LongTails.Setups.UscgHighProbability
open LongTails.Algorithms.UscgSharpConfidence
open LongTails.Proofs.UscgSharpGuarantee
open LongTails.Proofs.UscgSharpTuning
open LongTails.Proofs.UscgSharpExecution

noncomputable def budget : (let S := LongTails.Setups.UscgHighProbability.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => if 2 * p.L * p.Δ ≤ p.ε ^ 2 then 1 else ⌈4096 * (2 + 65536 * p.ζ ^ 2 * p.σ ^ 2 / p.ε ^ 2) * (1 + p.L * p.Δ / p.ε ^ 2 + Real.sqrt (p.L * p.Δ / p.ε ^ 2) * (1 + Real.log (1 / p.δ)))⌉₊

theorem result : Convergence LongTails.Setups.UscgHighProbability.spec budget := by
  refine ⟨configured, ?_, ?_⟩
  · intro p hp f O hO
    obtain ⟨g, lmo, P₀, P, hIID, hO, hlmo, H⟩ := hO
    subst O
    change spec.successful p f
      (fun seed : Unit × (ℕ → p.Ω) => execute (canonicalOracle p.toPublic g lmo P)
        (configured p.toPublic) (fun _ => horizon p.toPublic) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod (P : Measure _), inferInstance⟩
    let F : Unit × (ℕ → p.Ω) → (ℕ → p.Ω) := fun seed k => seed.2 (2 * k)
    have hmap : MeasurePreserving F ((Measure.dirac ()).prod (P : Measure _))
        (Measure.infinitePi fun _ : ℕ => (P₀ : Measure _)) :=
      (even_stream_law hIID).comp measurePreserving_snd
    have he : (fun seed : Unit × (ℕ → p.Ω) => execute (canonicalOracle p.toPublic g lmo P)
        (configured p.toPublic) (fun _ => horizon p.toPublic) seed.1 seed.2) =
        fun seed => canonicalOutput p.toPublic g lmo (F seed) := by
      funext seed
      rcases seed with ⟨⟨⟩, ξ⟩
      exact execute_canonical p.toPublic g lmo P ξ
    rw [he]
    have hp' := hp
    rcases hp with ⟨_, hR, hRb, _, _, hL, _, _, hΔ, hε, hδ, hδ1⟩
    have hδone : p.δ ≤ 1 := by linarith
    have hT := horizon_pos p.toPublic hL.le hΔ hδ hδone
    have hm := canonical_measurable p.toPublic H.measurable hlmo
    have hgap := average_measurable (f := f) H.measurable hlmo hR.le hRb
    refine ⟨hm.comp hmap.measurable, fun _ => hT, hgap.comp hmap.measurable, ?_⟩
    have hset : MeasurableSet {ξ | p.ε < averageStationarity p.toPublic f (canonicalOutput p.toPublic g lmo ξ)} :=
      measurableSet_lt measurable_const hgap
    change ((Measure.dirac ()).prod (P : Measure _))
      (F ⁻¹' {ξ | p.ε < averageStationarity p.toPublic f (canonicalOutput p.toPublic g lmo ξ)}) ≤ ENNReal.ofReal p.δ
    rw [hmap.measure_preimage hset.nullMeasurableSet]
    have hh := ENNReal.ofReal_le_ofReal (canonical_tail hp' hlmo H)
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  · intro p hp
    rcases hp with ⟨_, _, _, _, _, hL, _, _, hΔ, hε, hδ, hδ1⟩
    exact configured_allowed p.toPublic hL.le hΔ hε hδ (by linarith)

end LongTails.Theorems.SharpMomentumFiniteVarianceHighProbability
