import LongTails.Algorithms.UntiedReverseFisherGD
import LongTails.Proofs.Execution
import LongTails.Proofs.UntiedReverseFisherBranches
import LongTails.Proofs.SymmetricReverseFisherExecution

open MeasureTheory OracleTemplate WithLp
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherExecution

open LongTails.Setups.UntiedGaussianReverseFisher
open LongTails.Algorithms.UntiedReverseFisherGD
open LongTails.Proofs.UntiedReverseFisherLoss
open LongTails.Proofs.UntiedReverseFisherGradient
open LongTails.Proofs.UntiedReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherScalar

noncomputable def gdMap {p : Params} (μ : Means p) (θ : Means p) : Means p :=
  θ - step • gradient (loss μ) θ

lemma algorithm_constantStepGD (p : Params) : constantStepGD p (algorithm p) := by
  refine ⟨id, step, by unfold step; norm_num, ?_, ?_, ?_⟩
  all_goals intros; rfl

lemma output_eq_iterate (p : Params) (μ : Means p) (oracle : Oracle (Means p) (Means p))
    (h : ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2)
    (K : ℕ) (seed : Fin p.dimension → ℝ) (ξ : (k : ℕ) → oracle.Seed k) :
    output p oracle K seed ξ = (gdMap μ)^[K] (initial p seed) := by
  unfold output
  erw [OracleTemplate.execute_eq_of_answer_eq oracle (gradient (loss μ))
    (fun k x seed => h k (0, x) seed), OracleTemplate.execute_iterate]
  rfl

lemma step_eq_stepSize : step = stepSize := by unfold step stepSize; rfl

lemma coordinates_iterate {p : Params} (μ θ : Means p) (k : ℕ) :
    coordinates μ ((gdMap μ)^[k] θ) =
      (pairStep (q := LongTails.Proofs.UntiedReverseFisherGradient.tiedParams p) (half μ))^[k]
        (coordinates μ θ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    unfold gdMap
    rw [step_eq_stepSize]
    exact coordinates_step μ _

noncomputable def swapMeans {p : Params} (μ : Means p) : Means p := toLp 2 ![μ 1, μ 0]

lemma swap_zero {p : Params} (μ : Means p) : swapMeans μ 0 = μ 1 := rfl

lemma swap_one {p : Params} (μ : Means p) : swapMeans μ 1 = μ 0 := rfl

lemma score_swap {p : Params} (μ : Means p) (x : Space p) : score (swapMeans μ) x = score μ x := by
  unfold score weight
  simp only [Fin.sum_univ_two, swap_zero, swap_one]
  rw [add_comm (Real.exp (-‖x - μ 1‖ ^ 2 / 2))]
  abel

lemma loss_swap {p : Params} (μ : Means p) : loss (swapMeans μ) = loss μ := by
  funext θ
  unfold loss
  simp only [score_swap]

lemma centre_swap {p : Params} (μ : Means p) : centre (swapMeans μ) = centre μ := by
  unfold centre; rw [swap_zero, swap_one, add_comm]

lemma half_swap {p : Params} (μ : Means p) : half (swapMeans μ) = -half μ := by
  unfold half; rw [swap_zero, swap_one, ← smul_neg, neg_sub]

lemma matchingError_swap {p : Params} (μ θ : Means p) :
    matchingError (swapMeans μ) θ = matchingError μ θ := by
  unfold matchingError; rw [swap_zero, swap_one, min_comm]

lemma gdMap_swap {p : Params} (μ : Means p) : gdMap (swapMeans μ) = gdMap μ := by
  unfold gdMap; rw [loss_swap]

lemma direction_norm (p : Params) (seed : Fin p.dimension → ℝ) : ‖direction p seed‖ = 1 :=
  LongTails.Proofs.SymmetricReverseFisherExecution.initial_norm
    (LongTails.Algorithms.UntiedReverseFisherGD.tiedParams p) seed

lemma initial_coordinates {p : Params} (μ : Means p) (seed : Fin p.dimension → ℝ) :
    coordinates μ (initial p seed) = (-centre μ, direction p seed) := by
  have h0 : initial p seed 0 = direction p seed := rfl
  have h1 : initial p seed 1 = -direction p seed := rfl
  have hc : centre (initial p seed) = 0 := by
    unfold centre; rw [h0, h1, add_neg_cancel, smul_zero]
  have hh : half (initial p seed) = direction p seed := by
    unfold half; rw [h0, h1, sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
  unfold coordinates
  rw [hc, hh, zero_sub]
  rfl

lemma lossGradient_continuous {p : Params} (μ : Means p) : Continuous (lossGradient μ) := by
  have hR : Continuous (ridgeForce ‖half μ‖) :=
    continuous_iff_continuousAt.mpr (fun c =>
      (LongTails.Proofs.SymmetricReverseFisherRidge.hasDerivAt_ridgeForce ‖half μ‖ c).continuousAt)
  have hA : Continuous (fun x : Space p => alpha ‖x‖ • x) := by
    have h : LipschitzWith 48 (fun x : Space p => alpha ‖x‖ • x) :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        rw [dist_eq_norm, dist_eq_norm]
        exact_mod_cast LongTails.Proofs.SymmetricReverseFisherGradient.radial_gradient_lipschitz x y)
    exact h.continuous
  have hc : Continuous (fun θ : Means p => centre θ) := by unfold centre; fun_prop
  have hh : Continuous (fun θ : Means p => half θ) := by unfold half; fun_prop
  have hcomp (i : Fin 2) : Continuous (fun θ : Means p => component μ θ i) := by
    unfold component
    have h1 : Continuous (fun θ : Means p => alpha ‖half θ‖ • half θ) := hA.comp hh
    have h2 : Continuous (fun θ : Means p =>
        ((if i = 0 then (1 : ℝ) else -1) * alpha ‖half θ‖ / 2) • half θ) := by
      have : (fun θ : Means p => ((if i = 0 then (1 : ℝ) else -1) * alpha ‖half θ‖ / 2) • half θ) =
          fun θ => ((if i = 0 then (1 : ℝ) else -1) / 2) • (alpha ‖half θ‖ • half θ) := by
        funext θ; rw [smul_smul]; ring_nf
      rw [this]; exact h1.const_smul (((if i = 0 then (1 : ℝ) else -1) / 2))
    have h3a : Continuous (fun θ : Means p => ridgeForce ‖half μ‖ ⟪θ i - centre μ, half μ⟫ / 2) :=
      (hR.comp (by fun_prop)).div_const 2
    have h3 : Continuous (fun θ : Means p =>
        (ridgeForce ‖half μ‖ ⟪θ i - centre μ, half μ⟫ / 2) • half μ) :=
      h3a.smul continuous_const
    exact ((hc.sub continuous_const).add h2).sub h3
  unfold lossGradient
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hcomp)

lemma gdMap_continuous {p : Params} (μ : Means p) : Continuous (gdMap μ) := by
  unfold gdMap
  have : gradient (loss μ) = lossGradient μ := funext (gradient_loss μ)
  rw [this]
  exact continuous_id.sub ((lossGradient_continuous μ).const_smul step)

lemma initial_measurable (p : Params) : Measurable (initial p) := by
  have h := LongTails.Proofs.SymmetricReverseFisherExecution.initial_measurable
    (LongTails.Algorithms.UntiedReverseFisherGD.tiedParams p)
  unfold initial direction
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr (fun i => by fin_cases i <;> simp <;> fun_prop))

lemma output_measurable (p : Params) (μ : Means p) (oracle : Oracle (Means p) (Means p))
    (h : ∀ k query seed, oracle.answer k query seed = gradient (loss μ) query.2) (K : ℕ) :
    Measurable (fun z : (Fin p.dimension → ℝ) × ((k : ℕ) → oracle.Seed k) =>
      output p oracle K z.1 z.2) := by
  simp_rw [output_eq_iterate p μ oracle h K]
  exact ((gdMap_continuous μ).iterate K).measurable.comp ((initial_measurable p).comp measurable_fst)

end LongTails.Proofs.UntiedReverseFisherExecution
