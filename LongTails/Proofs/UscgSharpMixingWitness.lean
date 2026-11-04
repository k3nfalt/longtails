import LongTails.Proofs.UscgSharpLowerWitness
import LongTails.Proofs.UscgSharpMixingPath
import LongTails.Proofs.UscgSharpMixingNoise

namespace LongTails.Proofs.UscgSharpMixingWitness

open MeasureTheory ProbabilityTheory
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open UscgSharpScalar UscgSharpScalarPath UscgSharpLowerWitness

lemma mixing_witness {L σ Δ ε δ α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (ha : 0 < α) (ha1 : α < 1) (hη : 0 < η) (hT : 0 < T)
    (hδ : δ < 1 / 2) (hA : 8192 ≤ σ ^ 2 / ε ^ 2) (hD : 256 ≤ L * Δ / ε ^ 2)
    (hmemory : 4096 / (σ ^ 2 / ε ^ 2 + 16) ≤ α)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) :
    Nonempty (Witness L σ Δ ε δ α η T lmo) := by
  have hp := UscgSharpMixingConstants.public_threshold hA hmemory
  let p : unitInterval := ⟨16 / (σ ^ 2 / ε ^ 2 + 16), hp.1.le, hp.2.1⟩
  have hpp : 0 < (p : ℝ) := hp.1
  have hratio : 256 ≤ α / p := hp.2.2.2
  have hC := (UscgSharpMixingConstants.radius_bounds ha hpp hratio).1
  let noise := UscgSharpMixingNoise.noise p (2 * ε)
  let R := (Real.log (4 * α / p) + 2) / α
  have hgap : (2 * ε) * 0 + (2 * ε) ^ 2 / (2 * L) ≤ Δ := by
    have hh := (le_div_iff₀ (sq_pos_of_pos he)).mp hD
    have hh' : (2 * ε) ^ 2 / (2 * L) ≤ Δ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    nlinarith
  have hvar : (∫ b, noise b ^ 2 ∂bernoulliMeasure true false p) ≤ σ ^ 2 := by
    rw [UscgSharpMixingNoise.noise_variance p hpp]
    exact (UscgSharpMixingNoise.public_variance he).le
  have hbad : ∀ ξ ∈ UscgSharpMixingNoise.sparseEvent R T,
      ε * T < ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
        (gradient (lift (UscgSharpInstances.ramp L (2 * ε) 0))
          (trajectory α η (UscgSharpInstances.rampSlope L (2 * ε) 0) noise lmo ξ t).1) := by
    intro ξ hξ
    have hx := UscgSharpMixingPath.positive_constant_path noise lmo ξ
      (fun t => UscgSharpMixingNoise.indicator (ξ t)) ha ha1 hη (by positivity) hpp hC
      (fun _ => UscgSharpMixingNoise.indicator_le_one _) hlmo (fun _ => rfl) hξ
    have hn : ∀ t < T, 0 ≤ position α η (fun _ => 2 * ε) noise lmo ξ t := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        exact (initial _ _ _ _).1.ge
      · exact (hx t (by omega) ht.le).le
    rw [UscgSharpMixingPath.ramp_stationarity noise lmo ξ (by positivity) hn]
    have ht : (0 : ℝ) < T := by exact_mod_cast hT
    nlinarith
  refine ⟨{
    Ω := Bool
    measurableΩ := inferInstance
    law := bernoulliMeasure true false p
    probability := inferInstance
    f := UscgSharpInstances.ramp L (2 * ε) 0
    f' := UscgSharpInstances.rampSlope L (2 * ε) 0
    noise := noise
    derivative := UscgSharpInstances.ramp_derivative L (2 * ε) 0
    problem := UscgSharpInstances.ramp_problem hL (by positivity) (by norm_num) hgap
      (measurable_of_countable _) Integrable.of_finite
      (UscgSharpMixingNoise.noise_mean p hpp _) Integrable.of_finite hvar
    failure := ?_ }⟩
  have hs := UscgSharpMixingNoise.sparse_probability_of_memory p hpp ha hratio T
  have hm := measureReal_mono hbad (measure_ne_top (UscgSharpMixingNoise.streamLaw p) _)
  exact (hδ.trans hs).trans_le hm

end LongTails.Proofs.UscgSharpMixingWitness
