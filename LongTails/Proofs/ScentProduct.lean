import LongTails.Setups.CompositionalEntropicRisk
import LongTails.Proofs.LinearDecaySgdExpectation
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OracleTemplate.Scent

open MeasureTheory
open LongTails.Setups.CompositionalEntropicRisk

section PiEval

variable {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (law : Fin n → Measure Ξ)
  [∀ i, IsProbabilityMeasure (law i)]

lemma pi_map_eval_prob (i : Fin n) : (Measure.pi law).map (Function.eval i) = law i := by
  rw [Measure.pi_map_eval]
  simp [measure_univ]

lemma prod_map_eval_prob (i : Fin n) :
    ((Measure.pi law).prod (Measure.pi law)).map
      (fun x : (Fin n → Ξ) × (Fin n → Ξ) => (x.1 i, x.2 i)) = (law i).prod (law i) := by
  have h := Measure.map_prod_map (Measure.pi law) (Measure.pi law)
    (measurable_pi_apply i) (measurable_pi_apply i)
  rw [pi_map_eval_prob law i] at h
  rw [h]
  rfl

variable {X : Type*} [NormedAddCommGroup X]

lemma integrable_section (i : Fin n) {F : Ξ × Ξ → X} (hF : AEStronglyMeasurable F ((law i).prod (law i)))
    (hi : Integrable F ((law i).prod (law i))) :
    Integrable (fun x : (Fin n → Ξ) × (Fin n → Ξ) => F (x.1 i, x.2 i))
      ((Measure.pi law).prod (Measure.pi law)) := by
  have hmeas : Measurable (fun x : (Fin n → Ξ) × (Fin n → Ξ) => (x.1 i, x.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  have := (integrable_map_measure (by rw [prod_map_eval_prob law i]; exact hF)
    hmeas.aemeasurable).mp (by rw [prod_map_eval_prob law i]; exact hi)
  exact this

variable [NormedSpace ℝ X]

lemma integral_section (i : Fin n) {F : Ξ × Ξ → X}
    (hF : AEStronglyMeasurable F ((law i).prod (law i))) :
    ∫ x : (Fin n → Ξ) × (Fin n → Ξ), F (x.1 i, x.2 i) ∂((Measure.pi law).prod (Measure.pi law)) =
      ∫ y, F y ∂((law i).prod (law i)) := by
  have hmeas : Measurable (fun x : (Fin n → Ξ) × (Fin n → Ξ) => (x.1 i, x.2 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
  rw [← prod_map_eval_prob law i, integral_map hmeas.aemeasurable (by rw [prod_map_eval_prob law i]; exact hF)]

end PiEval

section Mixture

variable {q : Params} (I : Instance q)

instance : IsProbabilityMeasure (sampleLaw I) := by
  unfold sampleLaw; infer_instance

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma integral_uniform (H : Fin q.n → X) :
    ∫ i, H i ∂((PMF.uniformOfFintype (Fin q.n)).toMeasure) = (q.n : ℝ)⁻¹ • ∑ i, H i := by
  rw [PMF.integral_eq_sum, Finset.smul_sum]
  congr 1
  funext i
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma mixture_integrable (F : Fin q.n → q.Ξ × q.Ξ → X)
    (hF : ∀ i, Measurable (F i))
    (hi : ∀ i, Integrable (F i) ((I.law i : Measure q.Ξ).prod (I.law i))) :
    Integrable (fun ω : Seed q => F ω.1 (ω.2.1 ω.1, ω.2.2 ω.1)) (sampleLaw I) := by
  unfold sampleLaw
  set ν := (Measure.pi fun i => (I.law i : Measure q.Ξ)).prod (Measure.pi fun i => (I.law i : Measure q.Ξ))
  have hmeas : Measurable (fun ω : Fin q.n × ((Fin q.n → q.Ξ) × (Fin q.n → q.Ξ)) =>
      F ω.1 (ω.2.1 ω.1, ω.2.2 ω.1)) := by
    apply measurable_from_prod_countable_right
    intro i
    exact (hF i).comp (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun i =>
      integrable_section (fun i => (I.law i : Measure q.Ξ)) i (hF i).aestronglyMeasurable (hi i)
  · exact Integrable.of_finite

lemma mixture_integral (F : Fin q.n → q.Ξ × q.Ξ → X)
    (hF : ∀ i, Measurable (F i))
    (hi : ∀ i, Integrable (F i) ((I.law i : Measure q.Ξ).prod (I.law i))) :
    ∫ ω : Seed q, F ω.1 (ω.2.1 ω.1, ω.2.2 ω.1) ∂(sampleLaw I) =
      (q.n : ℝ)⁻¹ • ∑ i, ∫ y, F i y ∂((I.law i : Measure q.Ξ).prod (I.law i)) := by
  have hint := mixture_integrable I F hF hi
  unfold sampleLaw at hint ⊢
  rw [integral_prod _ hint]
  rw [integral_uniform]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_section (fun i => (I.law i : Measure q.Ξ)) i (hF i).aestronglyMeasurable

lemma integrable_fst_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : Integrable f μ) : Integrable (fun y : α × β => f y.1) (μ.prod ν) := by
  have := hf.mul_prod (integrable_const (1 : ℝ) (μ := ν))
  simpa using this

end Mixture

end OracleTemplate.Scent
