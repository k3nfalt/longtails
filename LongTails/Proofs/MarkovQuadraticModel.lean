import LongTails.Setups.MarkovQuadraticInterpolation
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MarkovQuadratic

open LongTails.Setups.MarkovQuadraticInterpolation

variable {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
  {κ : Kernel (Fin m) (Fin m)} {H : Fin m → q.E →L[ℝ] q.E}
  {f : q.E → ℝ} {u : q.E}

lemma sample_loss_integrable (π : ProbabilityMeasure (Fin m))
    (H : Fin m → q.E →L[ℝ] q.E) (u x : q.E) :
    Integrable (fun i => ⟪x - u, H i (x - u)⟫ / 2) (π : Measure (Fin m)) := by
  exact Integrable.of_finite

lemma sample_gradient_integrable (π : ProbabilityMeasure (Fin m))
    (H : Fin m → q.E →L[ℝ] q.E) (u x : q.E) :
    Integrable (fun i => H i (x - u)) (π : Measure (Fin m)) := by
  exact Integrable.of_finite

lemma sample_gradient_measurable (H : Fin m → q.E →L[ℝ] q.E) (u : q.E) :
    Measurable (fun z : q.E × Fin m => H z.2 (z.1 - u)) := by
  apply Continuous.measurable
  apply continuous_prod_of_discrete_right.mpr
  intro i
  exact (H i).continuous.comp (continuous_id.sub continuous_const)

end OracleTemplate.MarkovQuadratic

namespace LongTails.Setups.MarkovQuadraticInterpolation.Model

open OracleTemplate OracleTemplate.MarkovQuadratic

variable {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
  {κ : Kernel (Fin m) (Fin m)} {H : Fin m → q.E →L[ℝ] q.E}
  {f : q.E → ℝ} {u : q.E}

lemma minimizer (h : Model q m π κ H f u) : IsMinOn f Set.univ u := by
  intro x hx
  have hn : 0 ≤ f x - f u := by
    rw [h.population x]
    apply integral_nonneg
    intro i
    exact div_nonneg (h.positive i (x - u)) (by norm_num)
  exact sub_nonneg.mp hn

lemma objective_upper (h : Model q m π κ H f u) (x : q.E) :
    f x - f u ≤ q.L * ‖x - u‖ ^ 2 / 2 := by
  rw [h.population x]
  calc
    (∫ i, ⟪x - u, H i (x - u)⟫ / 2 ∂(π : Measure (Fin m))) ≤
        ∫ _ : Fin m, q.L * ‖x - u‖ ^ 2 / 2 ∂(π : Measure (Fin m)) := by
      apply integral_mono (sample_loss_integrable π H u x) (integrable_const _)
      intro i
      exact div_le_div_of_nonneg_right (h.smooth i (x - u)) (by norm_num)
    _ = q.L * ‖x - u‖ ^ 2 / 2 := by simp

lemma continuous_objective_gap (h : Model q m π κ H f u) :
    Continuous (fun x => f x - f u) := by
  simp only [h.population, integral_fintype (sample_loss_integrable π H u _)]
  apply continuous_finsetSum
  intro i hi
  have hi : Continuous (fun x : q.E => ⟪x - u, H i (x - u)⟫ / 2) :=
    ((continuous_id.sub continuous_const).inner
      ((H i).continuous.comp (continuous_id.sub continuous_const))).div_const (2 : ℝ)
  simpa only [smul_eq_mul] using hi.const_mul ((π : Measure (Fin m)).real {i})

end LongTails.Setups.MarkovQuadraticInterpolation.Model
