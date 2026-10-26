import LongTails.Proofs.AdamFinitePaths
import LongTails.Proofs.AdamSampledExecution
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.AdamFiniteLaw

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.AdamSeparationModel

lemma pi_uniform {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] :
    (Measure.pi fun _ : I => (PMF.uniformOfFintype Ω).toMeasure) =
      (PMF.uniformOfFintype (I → Ω)).toMeasure := by
  apply Measure.ext_of_singleton
  intro ω
  simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, ENNReal.inv_pow]

def blockPrefix (B H : ℕ) (ξ : ℕ → Bool) : Fin H → Fin B → Bool :=
  fun t j => ξ (B * t.val + j.val)

lemma blockPrefix_law (B H : ℕ) :
    MeasurePreserving (blockPrefix B H) (signStream : Measure _)
      (PMF.uniformOfFintype (Fin H → Fin B → Bool)).toMeasure := by
  have hind := signStream_iid.independent
  have hmarg := signStream_iid.marginal
  have hb := OracleTemplate.FiniteVariance.infinite_block_law (Ω := Bool) (signLaw : Measure Bool)
    (signStream : Measure (ℕ → Bool)) hind hmarg B
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving
    (Measure.pi fun _ : Fin B => (signLaw : Measure Bool)) H
  have h := hp.comp hb
  change MeasurePreserving _ _ (Measure.pi fun _ : Fin H =>
    Measure.pi fun _ : Fin B => (PMF.uniformOfFintype Bool).toMeasure) at h
  simp only [pi_uniform] at h
  convert h using 1
  funext ξ t j
  simp [blockPrefix, Nat.mul_comm]

lemma output_integral {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (B H : ℕ) [NeZero H] (draw : S → Fin H) (hd : Measurable draw)
    (hlaw : P.map draw = (PMF.uniformOfFintype (Fin H)).toMeasure)
    (F : Fin H → (Fin H → Fin B → Bool) → ℝ) :
    (∫ z : S × (ℕ → Bool), F (draw z.1) (blockPrefix B H z.2) ∂P.prod (signStream : Measure _)) =
      ((H : ℝ) * Fintype.card (Fin H → Fin B → Bool))⁻¹ * ∑ j, ∑ ω, F j ω := by
  have hd' : MeasurePreserving draw P (PMF.uniformOfFintype (Fin H)).toMeasure := ⟨hd, hlaw⟩
  have hm := hd'.prod (blockPrefix_law B H)
  have hi := integral_map (μ := P.prod (signStream : Measure _)) hm.measurable.aemeasurable
    (measurable_of_finite (fun z : Fin H × (Fin H → Fin B → Bool) => F z.1 z.2)).aestronglyMeasurable
  rw [hm.map_eq] at hi
  simp only [Prod.map_fst, Prod.map_snd] at hi
  rw [← hi, integral_prod _ (Integrable.of_finite)]
  simp only [OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin,
    ← Finset.mul_sum]
  ring

lemma trajectory_blockPrefix (a : LongTails.Setups.SpectralSmoothAdamComparison.AdamTuning)
    (r ℓ c w D s : ℝ) (B H t : ℕ) (ht : t ≤ H) (ξ : ℕ → Bool) :
    AdamScalarProcess.trajectory a r ℓ c w D
      (AdamFinitePaths.pathNoise s B H (blockPrefix B H ξ)) t =
      AdamScalarProcess.trajectory a r ℓ c w D (AdamSampledExecution.streamNoise s B ξ) t := by
  apply AdamScalarProcess.trajectory_prefix
  intro j hj
  simp only [AdamFinitePaths.pathNoise, AdamSampledExecution.streamNoise,
    dite_eq_left (show j < H by omega)]
  rfl

end LongTails.Proofs.AdamFiniteLaw
