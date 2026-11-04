import LongTails.Proofs.SymmetricThirdOrderHessian
import LongTails.Proofs.AdaptivePilotConfidence

namespace LongTails.Proofs.SymmetricThirdOrderEstimation

open MeasureTheory OracleTemplate.RobustGradient

variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [IsProbabilityMeasure P] in
lemma three_sigma_tail {X : Ω → V} (u : V) {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ σ ^ 2) :
    P.real {ω | 3 * σ < ‖X ω - u‖} ≤ 1 / 9 := by
  by_cases hz : σ = 0
  · have he : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) = 0 :=
      le_antisymm (by simpa [hz] using hm) (integral_nonneg (fun _ => sq_nonneg _))
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp he
    have hnull : P {ω | 3 * σ < ‖X ω - u‖} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with ω hω
      change ‖X ω - u‖ ^ 2 = 0 at hω
      have hn : ‖X ω - u‖ = 0 := by nlinarith [norm_nonneg (X ω - u)]
      simp [hz, hn]
    simp [measureReal_def, hnull]
  · have hp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    have hh := norm_tail_le_second_moment hi (by positivity : 0 < 3 * σ) hm
    have he : σ ^ 2 / (3 * σ) ^ 2 = 1 / 9 := by field_simp; ring
    exact hh.trans (le_of_eq he)

lemma pilot_second_moment_failure {X : Ω → V} (hX : Measurable X) (u : V)
    {σ : ℝ} (hσ : 0 ≤ σ) (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ σ ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | 9 * σ < ‖pilotCenter (18 * σ) (fun i => X (ξ i)) - u‖} ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ k) := by
  have hp : P.real {ω | (18 * σ) / 6 < ‖X ω - u‖} ≤ 1 / 9 := by
    rw [show (18 * σ) / 6 = 3 * σ by ring]
    exact three_sigma_tail u hσ hi hm
  have hh := pilotCenter_failure_probability_le hX u (18 * σ)
    (by norm_num : (0 : ℝ) < 1 / 9) (by norm_num : (1 / 9 : ℝ) ≤ 1) hp k
  have hs : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
    norm_num
  rw [hs] at hh
  rw [show (18 * σ) / 2 = 9 * σ by ring,
    show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] at hh
  exact hh

section Hessian

open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderHessian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma measurable_hessianPilot (k : ℕ) :
    Measurable (fun w : ℝ × (Fin k → E →L[ℝ] E) => hessianPilot w.1 w.2) := by
  exact continuous_symmetricHessian.measurable.comp
    ((measurable_pilotCenter k).comp ((measurable_fst.const_mul 18).prodMk measurable_snd))

lemma hessianPilot_failure {X : Ω → E →L[ℝ] E} (hX : Measurable X) (H : E →L[ℝ] E)
    (hH : ∀ x y : E, ⟪x, H y⟫ = ⟪H x, y⟫) {σ : ℝ} (hσ : 0 ≤ σ)
    (hi : Integrable (fun ω => ‖X ω - H‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - H‖ ^ 2 ∂P) ≤ σ ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | 9 * σ < ‖hessianPilot σ (fun i => X (ξ i)) - H‖} ≤
      ENNReal.ofReal ((2 / 3 : ℝ) ^ k) := by
  apply (measure_mono ?_).trans (pilot_second_moment_failure hX H hσ hi hm k)
  intro ξ hξ
  exact lt_of_lt_of_le hξ (symmetricHessian_error _ H hH)

end Hessian

section Gradient

open LongTails.Algorithms.SymmetricThirdOrder
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma measurable_gradientPilot (k m : ℕ) :
    Measurable (fun w : ℝ × (Fin k → Fin m → E) => gradientPilot w.1 w.2) := by
  have h : Measurable (fun w : ℝ × (Fin k → Fin m → E) =>
      (2 * w.1, fun i : Fin k => (1 / (m : ℝ)) • ∑ j, w.2 i j)) := by fun_prop
  exact (measurable_pilotCenter k).comp h

lemma gradientPilot_failure {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (u : E) (hmean : ∫ ω, X ω ∂P = u) {σ a : ℝ} (ha : 0 < a)
    (hi : Integrable (fun ω => ‖X ω - u‖ ^ 2) P)
    (hm : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ σ ^ 2) (k m : ℕ) (hmpos : 0 < m)
    (hsize : 144 * σ ^ 2 ≤ (m : ℝ) * a ^ 2) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => P)
      {ξ | a < ‖gradientPilot a (fun i j => X (ξ i j)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hbatch : (σ ^ 2 / (m : ℝ)) / ((2 * a) / 6) ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (2 * a) / 6))).mpr
    apply (div_le_iff₀ hmreal).mpr
    nlinarith
  have hh := pilot_means_failure_probability hX hXi u hmean hi hm
    (by positivity : 0 < 2 * a) k m hmpos hbatch
  simpa only [gradientPilot, show (2 * a) / 2 = a by ring] using hh

end Gradient

end LongTails.Proofs.SymmetricThirdOrderEstimation
