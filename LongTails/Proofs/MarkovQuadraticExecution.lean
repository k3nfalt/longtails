import LongTails.Algorithms.MarkovQuadraticSgd
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.MarkovQuadraticModel
import LongTails.Proofs.QuadraticContractions

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MarkovQuadratic

open LongTails.Setups.MarkovQuadraticInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma execute_lastSgd {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E) (η : ℝ) (x0 : E)
    (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (lastSgd η x0) (fun _ => K) () ξ = iterate g η x0 ξ K := by
  erw [StochasticGradient.execute_advance]
  have h : ∀ n call, StochasticGradient.advance
      (fun k x => x - η • g x (ξ k)) n call (iterate g η x0 ξ call) =
      iterate g η x0 ξ (call + n) := by
    intro n
    induction n with
    | zero => intro call; rfl
    | succ n ih =>
      intro call
      rw [StochasticGradient.advance]
      change StochasticGradient.advance _ n (call + 1)
        (iterate g η x0 ξ (call + 1)) = _
      rw [ih]
      congr 1
      omega
  simpa only [lastSgd, iterate, Nat.zero_add] using (h K 0)

lemma measurable_iterate {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (η : ℝ) (x0 : E) (K : ℕ) : Measurable (fun ξ => iterate g η x0 ξ K) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    change Measurable (fun ξ => iterate g η x0 ξ K -
      η • g (iterate g η x0 ξ K) (ξ K))
    exact ih.sub ((hg.comp (ih.prodMk (measurable_pi_apply K))).const_smul η)

end OracleTemplate.MarkovQuadratic

namespace LongTails.Setups.MarkovQuadraticInterpolation.Model

open OracleTemplate OracleTemplate.MarkovQuadratic

variable {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
  {κ : ProbabilityTheory.Kernel (Fin m) (Fin m)} {H : Fin m → q.E →L[ℝ] q.E}
  {f : q.E → ℝ} {u : q.E}

lemma iterate_radius (h : Model q m π κ H f u) {η : ℝ}
    (hL : 0 < q.L) (hη : 0 ≤ η) (hηL : η * q.L ≤ 2)
    (ξ : ℕ → Fin m) (n : ℕ) :
    ‖iterate (fun x i => H i (x - u)) η q.x0 ξ n - u‖ ≤ q.R := by
  induction n with
  | zero => exact h.radius
  | succ n ih =>
    have hc := quadratic_step_contract (H (ξ n)) hL (h.symmetric (ξ n))
      (h.positive (ξ n)) (h.smooth (ξ n)) hη hηL
      (iterate (fun x i => H i (x - u)) η q.x0 ξ n - u)
    rw [iterate]
    rw [show iterate (fun x i => H i (x - u)) η q.x0 ξ n -
        η • H (ξ n) (iterate (fun x i => H i (x - u)) η q.x0 ξ n - u) - u =
        (iterate (fun x i => H i (x - u)) η q.x0 ξ n - u) -
        η • H (ξ n) (iterate (fun x i => H i (x - u)) η q.x0 ξ n - u) by abel]
    exact hc.trans ih

lemma iterate_gap_upper (h : Model q m π κ H f u) {η : ℝ}
    (hL : 0 < q.L) (hη : 0 ≤ η) (hηL : η * q.L ≤ 2)
    (ξ : ℕ → Fin m) (n : ℕ) :
    f (iterate (fun x i => H i (x - u)) η q.x0 ξ n) - f u ≤ q.L * q.R ^ 2 / 2 := by
  have hr := h.iterate_radius hL hη hηL ξ n
  have hn := norm_nonneg (iterate (fun x i => H i (x - u)) η q.x0 ξ n - u)
  have hs : ‖iterate (fun x i => H i (x - u)) η q.x0 ξ n - u‖ ^ 2 ≤ q.R ^ 2 := by
    nlinarith
  exact (h.objective_upper _).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs hL.le) (by norm_num))

lemma integrable_iterate_gap (h : Model q m π κ H f u) {η : ℝ}
    (hL : 0 < q.L) (hη : 0 ≤ η) (hηL : η * q.L ≤ 2)
    (P : Measure (ℕ → Fin m)) [IsFiniteMeasure P] (n : ℕ) :
    Integrable (fun ξ => f (iterate (fun x i => H i (x - u)) η q.x0 ξ n) - f u) P := by
  have hm := h.continuous_objective_gap.measurable.comp
    (measurable_iterate (fun x i => H i (x - u))
      (sample_gradient_measurable H u) η q.x0 n)
  refine (integrable_const (q.L * q.R ^ 2 / 2)).mono' hm.aestronglyMeasurable ?_
  apply ae_of_all
  intro ξ
  have hn : 0 ≤ f (iterate (fun x i => H i (x - u)) η q.x0 ξ n) - f u :=
    sub_nonneg.mpr (h.minimizer (Set.mem_univ _))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using h.iterate_gap_upper hL hη hηL ξ n

end LongTails.Setups.MarkovQuadraticInterpolation.Model
