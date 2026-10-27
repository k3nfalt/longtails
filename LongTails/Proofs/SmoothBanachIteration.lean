import LongTails.Algorithms.SmoothBanachAnchoring
import LongTails.Proofs.SmoothBanachNoise
import LongTails.Proofs.SmoothBanachTuning
import LongTails.Proofs.GapStrongGrowthIteration
import LongTails.Proofs.ClippedExtragradientIteration

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SmoothBanachIteration

open LongTails.Algorithms.SmoothBanachAnchoring
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma picard_measurable (a η : ℝ) (b : E) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : E × Ω => picardStep a η b w.1 (g w.1 w.2)) := by
  unfold picardStep
  fun_prop

lemma picard_iterates_second_moment (P : ProbabilityMeasure Ω)
    (C : ℝ) (hC : 0 ≤ C) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (a η σ : ℝ) (hη : 0 ≤ η) (hstep : η * (1 + a) ≤ 1)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ z, Integrable (g z) (P : Measure Ω))
    (hg2 : ∀ z, Integrable (fun ω => ‖g z ω - T z‖ ^ 2) (P : Measure Ω))
    (hmean : ∀ z, (∫ ω, g z ω ∂(P : Measure Ω)) = T z)
    (hvar : ∀ z, (∫ ω, ‖g z ω - T z‖ ^ 2 ∂(P : Measure Ω)) ≤ σ ^ 2)
    (n : ℕ) :
    Integrable (fun ξ =>
      ‖iterateSamples (fun z ω => picardStep a η b z (g z ω)) n x ξ - u‖ ^ 2)
      (Measure.pi fun _ : Fin n => (P : Measure Ω)) ∧
    (∫ ξ, ‖iterateSamples (fun z ω => picardStep a η b z (g z ω)) n x ξ - u‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => (P : Measure Ω))) ≤
      ((1 - η * a) ^ 2) ^ n * ‖x - u‖ ^ 2 +
        (C * η ^ 2 * σ ^ 2) * ∑ j ∈ Finset.range n, ((1 - η * a) ^ 2) ^ j := by
  apply OracleTemplate.GapStrongGrowth.iterateSamples_measurable_integral
    (picard_measurable a η b hg) P (fun z => ‖z - u‖ ^ 2)
    (by fun_prop) (fun z => sq_nonneg _) (sq_nonneg (1 - η * a))
  intro z
  exact SmoothBanachNoise.picard_second_moment C hC J hsmooth T hT a η σ hη hstep
    b z u hu (g z) (hg.comp measurable_prodMk_left) (hgi z) (hg2 z) (hmean z) (hvar z)

omit [CompleteSpace E] in
lemma picard_iterates_parameter_measurable (a η : ℝ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (n : ℕ) :
    Measurable (fun w : E × E × (Fin n → Ω) =>
      iterateSamples (fun z ω => picardStep a η w.1 z (g z ω)) n w.2.1 w.2.2) := by
  apply OracleTemplate.ClippedExtragradient.measurable_iterateSamples_parameter
    (advance := fun (b z : E) (ω : Ω) => picardStep a η b z (g z ω)) (k := n)
  unfold picardStep
  fun_prop

lemma normalized_inner_bound (P : ProbabilityMeasure Ω)
    (C : ℝ) (hC : 0 ≤ C) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (a δ σ S : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : 0 < S)
    (hstep : δ / a * (1 + a) ≤ 1) (n : ℕ) (hn : 8 * S ≤ δ * n)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0)
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ z, Integrable (g z) (P : Measure Ω))
    (hg2 : ∀ z, Integrable (fun ω => ‖g z ω - T z‖ ^ 2) (P : Measure Ω))
    (hmean : ∀ z, (∫ ω, g z ω ∂(P : Measure Ω)) = T z)
    (hvar : ∀ z, (∫ ω, ‖g z ω - T z‖ ^ 2 ∂(P : Measure Ω)) ≤ σ ^ 2) :
    Integrable (fun ξ => a ^ 2 *
      ‖iterateSamples (fun z ω => picardStep a (δ / a) b z (g z ω)) n x ξ - u‖ ^ 2)
      (Measure.pi fun _ : Fin n => (P : Measure Ω)) ∧
    (∫ ξ, a ^ 2 *
      ‖iterateSamples (fun z ω => picardStep a (δ / a) b z (g z ω)) n x ξ - u‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => (P : Measure Ω))) ≤
      (a ^ 2 * ‖x - u‖ ^ 2) / (64 * S ^ 2) + C * δ * σ ^ 2 := by
  have hi := picard_iterates_second_moment P C hC J hsmooth T hT a (δ / a) σ
    (by positivity) hstep b x u hu g hg hgi hg2 hmean hvar n
  have he : 1 - δ / a * a = 1 - δ := by rw [div_mul_cancel₀ _ ha.ne']
  simp only [he] at hi
  refine ⟨hi.1.const_mul (a ^ 2), ?_⟩
  rw [integral_const_mul]
  have hdecay := SmoothBanachTuning.contraction_decay δ S hδ.le hδ1 hS n hn
  have hgeom := SmoothBanachTuning.contraction_geometric_sum δ hδ.le hδ1 n
  calc
    _ ≤ a ^ 2 * (((1 - δ) ^ 2) ^ n * ‖x - u‖ ^ 2 +
        C * (δ / a) ^ 2 * σ ^ 2 * ∑ j ∈ Finset.range n, ((1 - δ) ^ 2) ^ j) :=
      mul_le_mul_of_nonneg_left hi.2 (sq_nonneg a)
    _ = ((1 - δ) ^ 2) ^ n * (a ^ 2 * ‖x - u‖ ^ 2) +
        (C * δ * σ ^ 2) * (δ * ∑ j ∈ Finset.range n, ((1 - δ) ^ 2) ^ j) := by
      field_simp
    _ ≤ (1 / (64 * S ^ 2)) * (a ^ 2 * ‖x - u‖ ^ 2) + C * δ * σ ^ 2 * 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_right hdecay (by positivity))
        (mul_le_mul_of_nonneg_left hgeom (by positivity))
    _ = _ := by ring

end LongTails.Proofs.SmoothBanachIteration
