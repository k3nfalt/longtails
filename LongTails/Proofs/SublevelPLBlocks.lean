import LongTails.Proofs.SublevelPLEstimator
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def reindex (m b : ℕ) (ξ : Fin (m * b) → Ω) : Fin m → Fin b → Ω :=
  fun i l => ξ (finProdFinEquiv (i, l))

lemma measurable_reindex (m b : ℕ) : Measurable (reindex (Ω := Ω) m b) := by
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun l => measurable_pi_apply _

lemma reindex_preserving (p : Measure Ω) [IsProbabilityMeasure p] (m b : ℕ) :
    MeasurePreserving (reindex (Ω := Ω) m b) (Measure.pi fun _ : Fin (m * b) => p)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin b => p) := by
  have hr := measurePreserving_piCongrLeft (fun _ : Fin m × Fin b => p)
    (finProdFinEquiv (m := m) (n := b)).symm
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin b) Ω)
      (Measure.pi fun _ : Fin m × Fin b => p)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin b => p) := by
    refine ⟨(MeasurableEquiv.curry (Fin m) (Fin b) Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : Fin b) => p))
  have h := hc.comp hr
  convert h using 1
  funext ξ
  funext i l
  simp [reindex, MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma blockMean_eq (m b : ℕ) (r : Fin (m * b) → E) (i : Fin m) :
    blockMean m b r i = (1 / (b : ℝ)) • ∑ l : Fin b, reindex m b r i l := by
  simp [blockMean, reindex, one_div]

lemma subbatch_failure (p : Measure Ω) [IsProbabilityMeasure p]
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X p) (u : E)
    (hX2i : Integrable (fun ω => ‖X ω - u‖ ^ 2) p)
    (hmean : (∫ ω, X ω ∂p) = u) {σ2 : ℝ} (hvar : (∫ ω, ‖X ω - u‖ ^ 2 ∂p) ≤ σ2)
    (b : ℕ) (hb : 0 < b) {B : ℝ} (hB : 0 < B) (hbB : 144 * σ2 ≤ b * (B / 2) ^ 2) :
    (Measure.pi fun _ : Fin b => p).real
      {ζ | B / 6 < ‖(1 / (b : ℝ)) • ∑ l : Fin b, X (ζ l) - u‖} ≤ 1 / 16 := by
  have hv := RobustGradient.finite_mean_variance (P := p) hX hXi u hX2i hmean b hb
  have hr : 0 < B / 6 := by positivity
  have h := RobustGradient.norm_tail_le_second_moment (P := Measure.pi fun _ : Fin b => p)
    (X := fun ζ : Fin b → Ω => (1 / (b : ℝ)) • ∑ l : Fin b, X (ζ l) - u) hv.1 hr
    (v := σ2 / b) (by rw [hv.2]; exact div_le_div_of_nonneg_right hvar (by positivity))
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have : σ2 / b * (B / 6) ^ 2 = σ2 * (B / 2) ^ 2 / (9 * b) := by
    field_simp
    ring
  rw [div_le_iff₀ hb'] at *
  nlinarith [hbB]

end OracleTemplate.SublevelRobustGradient
