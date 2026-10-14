import tutorial.ToBeDiscovered.Proofs.SgdConvergence
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_selected {g : E → Ω → E} (ho : Measurable (Function.uncurry g))
    (η : ℝ) (K : ℕ) (i : Fin K) :
    Measurable (fun z : E × (Fin K → Ω) => selected g η K z.1 z.2 i) := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · have ht : Measurable (fun z : E × (Fin (K + 1) → Ω) =>
          (z.1 - η • g z.1 (z.2 0), fun k : Fin K => z.2 k.succ)) := by
        have hh : Measurable (fun z : E × (Fin (K + 1) → Ω) => g z.1 (z.2 0)) :=
          ho.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
        exact (measurable_fst.sub (hh.const_smul η)).prodMk (by fun_prop)
      exact (ih j).comp ht

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma sum_selected (f : E → ℝ) (g : E → Ω → E) (η : ℝ)
    (K : ℕ) (x : E) (ξ) :
    ∑ i : Fin K, ‖gradient f (selected g η K x ξ i)‖ ^ 2 = cost f g η K x ξ := by
  induction K generalizing x with
  | zero => simp [cost]
  | succ K ih =>
    simp only [Fin.sum_univ_succ, selected, Fin.cases_zero, Fin.cases_succ, cost]
    rw [ih]


omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma selected_le_cost (f : E → ℝ) (g : E → Ω → E) (η : ℝ)
    (K : ℕ) (x : E) (ξ) (i : Fin K) :
    ‖gradient f (selected g η K x ξ i)‖ ^ 2 ≤ cost f g η K x ξ := by
  rw [← sum_selected]
  exact Finset.single_le_sum
    (f := fun j : Fin K => ‖gradient f (selected g η K x ξ j)‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma selected_rate {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η lower : ℝ}
    (hL : 0 < L) (hη : 0 < η) (hηL : η * L ≤ 1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hb : ∀ x, lower ≤ f x) (ho : StochasticGradient E Ω p f g σ)
    (N : ℕ) [NeZero N] (x : E) :
    let μ := (PMF.uniformOfFintype (Fin N)).toMeasure
    let Q := Measure.pi (fun _ : Fin N => p)
    let out := fun z : Fin N × (Fin N → Ω) => selected g η N x z.2 z.1
    Measurable out ∧ Integrable (fun z => ‖gradient f (out z)‖ ^ 2) (μ.prod Q) ∧
      η / 2 * N * (∫ z, ‖gradient f (out z)‖ ^ 2 ∂μ.prod Q) ≤
        f x - lower + N * (L * η ^ 2 / 2 * σ ^ 2) := by
  dsimp only
  let μ := (PMF.uniformOfFintype (Fin N)).toMeasure
  let Q := Measure.pi (fun _ : Fin N => p)
  let out := fun z : Fin N × (Fin N → Ω) => selected g η N x z.2 z.1
  have hm : Measurable out := measurable_from_prod_countable_right (fun i =>
    (measurable_selected ho.measurable η N i).comp (measurable_const.prodMk measurable_id))
  have hc := expected_cost hL hη hηL hg hlip hb ho N x
  have hd := gradient_measurable hL.le hlip
  have hi : Integrable (fun z => ‖gradient f (out z)‖ ^ 2) (μ.prod Q) :=
    (measurePreserving_snd.integrable_comp_of_integrable hc.1).mono_nonneg
      ((hd.comp hm).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))
      (Filter.Eventually.of_forall (fun z => selected_le_cost f g η N x z.2 z.1))
  refine ⟨hm, hi, ?_⟩
  have havg (ξ : Fin N → Ω) :
      (∫ i, ‖gradient f (selected g η N x ξ i)‖ ^ 2 ∂μ) =
        (N : ℝ)⁻¹ * cost f g η N x ξ := by
    simp [μ, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
      ← Finset.mul_sum, sum_selected]
  have he : (∫ z, ‖gradient f (out z)‖ ^ 2 ∂μ.prod Q) =
      (N : ℝ)⁻¹ * (∫ ξ, cost f g η N x ξ ∂Q) := by
    rw [integral_prod_symm _ hi]
    simp only [out, havg, integral_const_mul]
  rw [he]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  convert hc.2 using 1; field_simp; ring

lemma iid_prefix {Ξ : Type*} [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    (h : IID ξ p P) (N : ℕ) :
    MeasurePreserving (fun ω (i : Fin N) => ξ i ω) P (Measure.pi fun _ : Fin N => p) := by
  refine ⟨Measurable.of_eval (fun i => h.measurable i), ?_⟩
  have hi := h.independent.precomp (g := fun i : Fin N => i.val) Fin.val_injective
  simpa only [h.marginal] using
    hi.map_fun_eq_pi_map (fun i : Fin N => (h.measurable i.val).aemeasurable)

end OracleTemplate.StochasticNonconvex
