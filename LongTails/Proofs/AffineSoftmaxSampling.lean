import LongTails.Algorithms.AffineSoftmaxQueries
import LongTails.Proofs.AffineSoftmaxResidual
import LongTails.Algorithms.FiniteCategoricalSampler
import LongTails.Algorithms.AffineSoftmaxEstimator
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxSampling

open LongTails.Algorithms.AffineSoftmaxEstimator

lemma halfSuccess_ne_zero : halfSuccess ≠ 0 := by
  intro h
  have hh := congrArg (fun p : unitInterval => (p : ℝ)) h
  norm_num [halfSuccess] at hh

lemma countLaw_mean : (∫ k : ℕ, (k : ℝ) ∂(countLaw : Measure ℕ)) = 1 := by
  change (∫ k : ℕ, (k : ℝ) ∂geometricMeasure halfSuccess) = 1
  rw [integral_geometricMeasure halfSuccess_ne_zero]
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (1 / 2 : ℝ)
  have he : (∑' n : ℕ, ((1 - (halfSuccess : ℝ)) ^ n * (halfSuccess : ℝ)) • (n : ℝ)) =
      ∑' n : ℕ, (1 / 2 : ℝ) * ((n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    congr 1
    funext n
    norm_num [halfSuccess, smul_eq_mul]
    ring
  rw [he, hs.tsum_eq]
  norm_num

lemma countLaw_integrable : Integrable (fun k : ℕ => (k : ℝ)) (countLaw : Measure ℕ) := by
  by_contra h
  have hi := integral_undef h
  rw [countLaw_mean] at hi
  norm_num at hi

lemma estimator_calls_mean :
    (∫ k : ℕ, ((k + 1 : ℕ) : ℝ) ∂(countLaw : Measure ℕ)) = 2 := by
  simp only [Nat.cast_add, Nat.cast_one]
  rw [integral_add countLaw_integrable (integrable_const _), countLaw_mean]
  norm_num

lemma reciprocal_mean_series {Z : ℝ} (hZ : 1 ≤ Z) (hZ2 : Z ≤ 2) :
    HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) * (2 - Z) ^ k) (1 / Z) := by
  have h0 : 0 ≤ (2 - Z) / 2 := by linarith
  have h1 : (2 - Z) / 2 < 1 := by linarith
  have hs := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 / 2 : ℝ)
  have hz : Z ≠ 0 := by linarith
  convert hs using 1
  · funext k
    simp only [pow_succ, div_eq_mul_inv, mul_pow, one_pow]
    ring
  · have hd : 1 - (2 - Z) / 2 = Z / 2 := by ring
    rw [hd]
    field_simp

lemma reciprocal_mean {Z : ℝ} (hZ : 1 ≤ Z) (hZ2 : Z ≤ 2) :
    (∫ k : ℕ, (2 - Z) ^ k ∂(countLaw : Measure ℕ)) = 1 / Z := by
  change (∫ k : ℕ, (2 - Z) ^ k ∂geometricMeasure halfSuccess) = 1 / Z
  rw [integral_geometricMeasure halfSuccess_ne_zero]
  convert (reciprocal_mean_series hZ hZ2).tsum_eq using 1
  congr 1
  funext k
  norm_num [halfSuccess, smul_eq_mul, pow_succ]

lemma reciprocal_eq_prod (ws : List ℝ) :
    reciprocal ws = (ws.map (fun w => 2 - w)).prod := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [reciprocal, ih]

lemma reciprocal_ofFn {k : ℕ} (w : Fin k → ℝ) :
    reciprocal (List.ofFn w) = ∏ j, (2 - w j) := by
  rw [reciprocal_eq_prod, ← List.ofFn_comp', List.prod_ofFn]

lemma reciprocal_fixed_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (w : Ω → ℝ) (k : ℕ) :
    (∫ x : Fin k → Ω, reciprocal (List.ofFn (fun j => w (x j)))
      ∂Measure.pi (fun _ => (μ : Measure Ω))) =
      (∫ x, 2 - w x ∂(μ : Measure Ω)) ^ k := by
  simp_rw [reciprocal_ofFn]
  simpa using (integral_fintype_prod_eq_pow (ι := Fin k)
    (μ := (μ : Measure Ω)) (fun x => 2 - w x))

lemma reciprocal_random_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (w : Ω → ℝ) {Z : ℝ}
    (hmean : (∫ x, 2 - w x ∂(μ : Measure Ω)) = 2 - Z)
    (hZ : 1 ≤ Z) (hZ2 : Z ≤ 2) :
    (∫ k : ℕ, (∫ x : Fin k → Ω,
      reciprocal (List.ofFn (fun j => w (x j)))
      ∂Measure.pi (fun _ => (μ : Measure Ω)))
      ∂(countLaw : Measure ℕ)) = 1 / Z := by
  simp_rw [reciprocal_fixed_mean, hmean]
  exact reciprocal_mean hZ hZ2

lemma independent_correction_mean {Ω Ξ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : ProbabilityMeasure Ω) (ν : ProbabilityMeasure Ξ)
    (R : Ω → ℝ) (N : Ξ → E) (b : E)
    (hR : Integrable R (μ : Measure Ω)) (hN : Integrable N (ν : Measure Ξ)) :
    (∫ u : Ω × Ξ, b + R u.1 • N u.2
      ∂(μ : Measure Ω).prod (ν : Measure Ξ)) =
      b + (∫ u, R u ∂(μ : Measure Ω)) • (∫ v, N v ∂(ν : Measure Ξ)) := by
  rw [integral_add (integrable_const _) (hR.smul_prod hN), integral_prod_smul]
  simp

lemma centered_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : ProbabilityMeasure Ω) (X : Ω → E)
    (hX : Integrable X (μ : Measure Ω))
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) (μ : Measure Ω)) :
    (∫ ω, ‖X ω - (∫ v, X v ∂(μ : Measure Ω))‖ ^ 2 ∂(μ : Measure Ω)) ≤
      ∫ ω, ‖X ω‖ ^ 2 ∂(μ : Measure Ω) := by
  let a := ∫ v, X v ∂(μ : Measure Ω)
  change (∫ ω, ‖X ω - a‖ ^ 2 ∂(μ : Measure Ω)) ≤ _
  simp_rw [norm_sub_sq_real]
  have hi : Integrable (fun ω => 2 * ⟪X ω, a⟫) (μ : Measure Ω) :=
    (hX.inner_const a).const_mul 2
  have hd : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪X ω, a⟫) (μ : Measure Ω) :=
    hX2.sub hi
  rw [integral_add hd (integrable_const _),
    integral_sub hX2 hi, integral_const_mul]
  have hint : (∫ ω, ⟪X ω, a⟫ ∂(μ : Measure Ω)) = ⟪a, a⟫ := by
    calc
      _ = ∫ ω, ⟪a, X ω⟫ ∂(μ : Measure Ω) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = _ := integral_inner (𝕜 := ℝ) hX a
  rw [hint]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ ω, ‖X ω‖ ^ 2 ∂(μ : Measure Ω)) - 2 * ⟪a, a⟫ + ‖a‖ ^ 2 ≤ _
  rw [real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖a‖]


open LongTails.Algorithms.FiniteCategoricalSampler in
lemma categorical_draw_measurable (ι : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι] :
    Measurable (Function.uncurry (draw ι)) :=
  (Classical.choose_spec (Kernel.exists_measurable_map_eq_unitInterval (kernel ι))).1

open LongTails.Algorithms.FiniteCategoricalSampler in
lemma categorical_draw_law (ι : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    (w : Weights ι) :
    (volume : Measure unitInterval).map (draw ι w) = (law ι w).toMeasure :=
  (Classical.choose_spec (Kernel.exists_measurable_map_eq_unitInterval (kernel ι))).2 w


open LongTails.Algorithms.FiniteCategoricalSampler in
lemma categorical_draw_integral (ι : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : Weights ι) (f : ι → E) :
    (∫ u : unitInterval, f (draw ι w u)) = ∑ i, (w.val i).toReal • f i := by
  have hm : Measurable (draw ι w) :=
    (categorical_draw_measurable ι).comp (measurable_const.prodMk measurable_id)
  rw [← integral_map_of_stronglyMeasurable hm (StronglyMeasurable.of_discrete),
    categorical_draw_law, PMF.integral_eq_sum]
  rfl


open LongTails.Algorithms.AffineSoftmaxQueries in
lemma gibbsWeights_measurable (ι : Type*) [Fintype ι] [Nonempty ι] (τ : ℝ) :
    Measurable (gibbsWeights (ι := ι) τ) := by
  have hc (i : ι) : Continuous (fun v : ι → ℝ => gibbsWeight τ v i) := by
    unfold gibbsWeight
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro v
      exact (Finset.sum_pos (fun j _ => Real.exp_pos (v j / τ)) Finset.univ_nonempty).ne'
  exact (Measurable.of_eval (fun i => ENNReal.measurable_ofReal.comp (hc i).measurable)).subtype_mk

open LongTails.Algorithms.AffineSoftmaxQueries LongTails.Algorithms.FiniteCategoricalSampler in
lemma gibbs_draw_integral (ι : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (τ : ℝ) (v : ι → ℝ) (f : ι → E) :
    (∫ u : unitInterval, f (draw ι (gibbsWeights τ v) u)) =
      ∑ i, gibbsWeight τ v i • f i := by
  rw [categorical_draw_integral]
  apply Finset.sum_congr rfl
  intro i _
  rw [gibbsWeights, ENNReal.toReal_ofReal (LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_pos τ v i).le]


open LongTails.Algorithms.AffineSoftmaxQueries in
lemma rows_projection_law (k : ℕ) :
    (rowsLaw : Measure Rows).map (fun rows => rows k) =
      Measure.pi (fun _ : Fin k => (volume : Measure unitInterval)) :=
  (measurePreserving_eval_infinitePi (fun n : ℕ =>
    Measure.pi (fun _ : Fin n => (volume : Measure unitInterval))) k).map_eq

open LongTails.Algorithms.AffineSoftmaxQueries in
lemma selected_row_measurable {Y : Type*} [MeasurableSpace Y]
    (f : (k : ℕ) → (Fin k → unitInterval) → Y) (hf : ∀ k, Measurable (f k)) :
    Measurable (fun z : ℕ × Rows => f z.1 (z.2 z.1)) :=
  measurable_from_prod_countable_right (fun k => (hf k).comp (measurable_pi_apply k))

open LongTails.Algorithms.AffineSoftmaxQueries in
lemma rows_integral (k : ℕ) (f : (Fin k → unitInterval) → ℝ) (hf : Measurable f) :
    (∫ rows, f (rows k) ∂(rowsLaw : Measure Rows)) =
      ∫ row, f row ∂Measure.pi (fun _ : Fin k => (volume : Measure unitInterval)) := by
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply k) hf.stronglyMeasurable,
    rows_projection_law]


open LongTails.Algorithms.FiniteCategoricalSampler in
lemma categorical_draw_integrable (ι : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Nonempty ι] [StandardBorelSpace ι]
    {E : Type*} [NormedAddCommGroup E]
    (w : Weights ι) (f : ι → E) :
    Integrable (fun u : unitInterval => f (draw ι w u)) volume := by
  have hm : Measurable (draw ι w) :=
    (categorical_draw_measurable ι).comp (measurable_const.prodMk measurable_id)
  have hf : Integrable f (law ι w).toMeasure := Integrable.of_finite
  rw [← categorical_draw_law ι w] at hf
  exact (integrable_map_measure StronglyMeasurable.of_discrete.aestronglyMeasurable hm.aemeasurable).1 hf

end LongTails.Proofs.AffineSoftmaxSampling
