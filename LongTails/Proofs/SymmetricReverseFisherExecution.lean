import LongTails.Algorithms.SymmetricReverseFisherGD
import LongTails.Proofs.Execution
import LongTails.Proofs.SymmetricReverseFisherDynamics

open MeasureTheory OracleTemplate WithLp

namespace LongTails.Proofs.SymmetricReverseFisherExecution

open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Algorithms.SymmetricReverseFisherGD

lemma step_pos (p : Params) (h : 0 ≤ p.upper) : 0 < step p := by
  unfold step
  positivity

lemma algorithm_gdFamily (p : Params) (h : 0 ≤ p.upper) : gdFamily p (algorithm p) := by
  refine ⟨id, fun _ => step p, fun _ => step_pos p h, ?_, ?_, ?_⟩
  all_goals intros; rfl

lemma initial_norm (p : Params) (seed : Fin p.dimension → ℝ) : ‖initial p seed‖ = 1 := by
  unfold initial
  dsimp only
  split_ifs with hz
  · simp
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

lemma initial_measurable (p : Params) : Measurable (initial p) := by
  unfold initial
  dsimp only
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · exact measurable_const
  · fun_prop

lemma output_eq_iterate (p : Params) (μ : Space p)
    (oracle : Oracle (Space p) (Space p))
    (h : ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2)
    (K : ℕ) (seed : Fin p.dimension → ℝ) (ξ : (k : ℕ) → oracle.Seed k) :
    output p oracle K seed ξ =
      (fun x => x - step p • gradient (loss μ) x)^[K] (initial p seed) := by
  unfold output
  erw [execute_eq_of_answer_eq oracle (gradient (loss μ)) (fun k x seed => h k (0, x) seed),
    execute_iterate]
  rfl

open LongTails.Proofs.SymmetricReverseFisherDynamics

lemma score_neg_parameter {p : Params} (μ x : Space p) : score (-μ) x = score μ x := by
  simp [score, Real.tanh_neg]
lemma loss_neg_parameter {p : Params} (μ x : Space p) : loss (-μ) x = loss μ x := by
  simp only [loss, score_neg_parameter]
lemma gradient_neg_parameter {p : Params} (μ x : Space p) : gradient (loss (-μ)) x = gradient (loss μ) x := by
  have hf : loss (-μ) = loss μ := funext (loss_neg_parameter μ)
  rw [hf]
lemma gdStep_neg_parameter {p : Params} (μ x : Space p) (η : ℝ) : gdStep (-μ) η x = gdStep μ η x := by
  simp only [gdStep, gradient_neg_parameter]
lemma iterate_neg_parameter {p : Params} (μ x : Space p) (η : ℝ) (k : ℕ) :
    (gdStep (-μ) η)^[k] x = (gdStep μ η)^[k] x := by
  have hf : gdStep (-μ) η = gdStep μ η := funext (fun x => gdStep_neg_parameter μ x η)
  rw [hf]

open LongTails.Proofs.SymmetricReverseFisherGradient

lemma gradient_loss_continuous {p : Params} (μ : Space p) : Continuous (gradient (loss μ)) := by
  have h : LipschitzWith ⟨48+20*‖μ‖, by positivity⟩ (gradient (loss μ)) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      change ‖gradient (loss μ) x - gradient (loss μ) y‖ ≤ (48+20*‖μ‖)*‖x-y‖
      exact gradient_loss_lipschitz μ x y)
  exact h.continuous
lemma gdStep_continuous {p : Params} (μ : Space p) (η : ℝ) : Continuous (gdStep μ η) := by
  exact continuous_id.sub ((gradient_loss_continuous μ).const_smul η)
lemma output_measurable (p : Params) (μ : Space p) (oracle : Oracle (Space p) (Space p))
    (h : ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2) (K : ℕ) :
    Measurable (fun z : (Fin p.dimension → ℝ) × ((k : ℕ) → oracle.Seed k) =>
      output p oracle K z.1 z.2) := by
  simp_rw [output_eq_iterate p μ oracle h K]
  exact ((gdStep_continuous μ (step p)).iterate K).measurable.comp
    ((initial_measurable p).comp measurable_fst)

end LongTails.Proofs.SymmetricReverseFisherExecution
