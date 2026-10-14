import LongTails.Setups.FixedBatchConfidence
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.FixedBatchConfidence

open LongTails.Setups.FixedBatchConfidence

def pair (x y : ℝ) : Space := WithLp.toLp 2 ![x, y]

@[simp] lemma pair_zero (x y : ℝ) : pair x y 0 = x := rfl

@[simp] lemma pair_one (x y : ℝ) : pair x y 1 = y := rfl

lemma pair_inner (x y z w : ℝ) : ⟪pair x y, pair z w⟫ = x * z + y * w := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, pair, mul_comm]

lemma pair_norm_sq (x y : ℝ) : ‖pair x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, pair_inner]
  ring

lemma pair_inner_vector (a c : ℝ) (x : Space) : ⟪pair a c, x⟫ = a * x 0 + c * x 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, pair, mul_comm]

lemma model_minimum {q : Params} {p : ProbabilityMeasure Space}
    {f : Space → ℝ} {u : Space} (h : Model q p f u) :
    IsMinOn f Set.univ u ∧ f u = 0 := by
  have hu : f u = 0 := by simp [h.population u]
  refine ⟨?_, hu⟩
  intro x _
  change f u ≤ f x
  rw [hu, h.population x]
  apply integral_nonneg
  intro a
  positivity

lemma two_atom_model (q : Params) (p : unitInterval) (u a v : Space)
    (ha : ‖a‖ ^ 2 ≤ q.L) (hv : ‖v‖ ^ 2 ≤ q.L)
    (hu : ‖q.x0 - u‖ ≤ q.R) :
    Model q ⟨bernoulliMeasure a v p, inferInstance⟩
      (fun x => (p : ℝ) * (⟪a, x - u⟫ ^ 2 / 2) +
        (1 - p) * (⟪v, x - u⟫ ^ 2 / 2)) u := by
  constructor
  · change ∀ᵐ z ∂bernoulliMeasure a v p, ‖z‖ ^ 2 ≤ q.L
    rw [bernoulliMeasure_def, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure (by simpa using ha) _
    · exact Measure.ae_smul_measure (by simpa using hv) _
  · exact hu
  · intro x
    change _ = ∫ z, ⟪z, x - u⟫ ^ 2 / 2 ∂bernoulliMeasure a v p
    rw [integral_bernoulliMeasure]
    rfl

lemma strict_failure_not_successful {q : Params} {p : ProbabilityMeasure Space}
    {f : Space → ℝ} {u : Space} (hm : Model q p f u)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (output : Ω → Space)
    (hfail : ENNReal.ofReal q.δ <
      (P : Measure Ω) {ω | q.ε < f (output ω) - f u}) :
    ¬spec.successful q f output P := by
  rintro ⟨_, v, hv, hprob⟩
  have hmin := (model_minimum hm).1
  have he : f v = f u := le_antisymm (hv (Set.mem_univ u)) (hmin (Set.mem_univ v))
  rw [he] at hprob
  exact (not_lt_of_ge hprob) hfail

end OracleTemplate.FixedBatchConfidence
