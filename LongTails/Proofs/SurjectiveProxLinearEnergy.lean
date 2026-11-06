import LongTails.Proofs.SurjectiveProxLinearExpectation
import LongTails.Proofs.ProxLinearVarianceLyapunov

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearEnergy

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.SurjectiveProxLinearOracle
open LongTails.Proofs.SurjectiveProxLinearTrajectory
open LongTails.Proofs.SurjectiveProxLinearProcess
open LongTails.Proofs.SurjectiveProxLinearExpectation
open LongTails.Proofs.SurjectiveProxLinearIntegrability
open LongTails.Proofs.SurjectiveProxLinearExactModel
open LongTails.Proofs.SurjectiveProxLinearMoreau

variable (p : Params) (I : Problem p) (hp : spec.valid p) (H : Regularity p I)
    (g : p.E → p.Ω → p.E) (v : p.E → p.Ω → Constraint p)
    (D : p.E → p.Ω → Jacobian p) (μ : ProbabilityMeasure p.Ω)
    (O : OracleConditions p I g v D μ)

local notation "Z" => jointOracle p g v D
local notation "Q" => (Measure.infinitePi fun _ : ℕ => (μ : Measure p.Ω))

include hp H O

lemma estimator_error_integrable : ∀ k,
    Integrable (fun ξ => ‖estimatorError p I Z ξ k‖ ^ 2) Q
  | 0 => (initial_error_moment p I hp H g v D μ O).1
  | k + 1 => (recursive_error_moment p I hp H g v D μ O k
      (estimator_error_integrable k)).1

lemma envelope_integrable (k : ℕ) :
    Integrable (fun ξ => envelope p I (trajectory p Z ξ k).1) Q :=
  trajectory_function_integrable p hp Z (jointOracle_measurable p I g v D μ O) Q k
    (envelope p I) (continuous_envelope p I hp H)

lemma exact_step_square_integrable (k : ℕ) :
    Integrable (fun ξ => ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2) Q :=
  trajectory_function_integrable p hp Z (jointOracle_measurable p I g v D μ O) Q k
    (fun x => ‖exactModelStep p I x‖ ^ 2) ((continuous_exactModelStep p I hp H).norm.pow 2)

lemma expected_envelope_descent (k : ℕ) :
    (∫ ξ, envelope p I (trajectory p Z ξ (k + 1)).1 ∂Q) ≤
      (∫ ξ, envelope p I (trajectory p Z ξ k).1 ∂Q) -
      gamma p * relaxation p * (∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q) +
      6 * gamma p * relaxation p * sensitivity p *
        ((∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q) + ridge p ^ 2) := by
  let a := gamma p * relaxation p
  let c := 6 * gamma p * relaxation p * sensitivity p
  have hφ := envelope_integrable p I hp H g v D μ O k
  have hφnext := envelope_integrable p I hp H g v D μ O (k + 1)
  have hb := exact_step_square_integrable p I hp H g v D μ O k
  have hE := estimator_error_integrable p I hp H g v D μ O k
  have hR1 : Integrable (fun ξ => envelope p I (trajectory p Z ξ k).1 -
      a * ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2) Q := hφ.sub (hb.const_mul a)
  have hR2 : Integrable (fun ξ => c * (‖estimatorError p I Z ξ k‖ ^ 2 + ridge p ^ 2)) Q :=
    (hE.add (integrable_const _)).const_mul c
  have h := integral_mono hφnext (hR1.add hR2)
    (fun ξ => trajectory_envelope_descent p I hp H Z ξ k)
  simp only [Pi.add_apply] at h
  rw [integral_add hR1 hR2, integral_sub hφ (hb.const_mul a), integral_const_mul,
    integral_const_mul, integral_add hE (integrable_const _), integral_const] at h
  simpa only [probReal_univ, one_smul, a, c] using h

lemma expected_estimated_step_bound (k : ℕ) :
    (∫ ξ, ‖estimatedStep p Z ξ k‖ ^ 2 ∂Q) ≤
      2 * (∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q) +
      2 * sensitivity p * ((∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q) + ridge p ^ 2) := by
  have hs := estimated_step_square_integrable p hp Z (jointOracle_measurable p I g v D μ O) Q k
  have hb := exact_step_square_integrable p I hp H g v D μ O k
  have hE := estimator_error_integrable p I hp H g v D μ O k
  have hR2 : Integrable (fun ξ => 2 * sensitivity p *
      (‖estimatorError p I Z ξ k‖ ^ 2 + ridge p ^ 2)) Q :=
    (hE.add (integrable_const _)).const_mul (2 * sensitivity p)
  have h := integral_mono hs ((hb.const_mul 2).add hR2)
    (fun ξ => estimated_step_square p I hp H Z ξ k)
  simp only [Pi.add_apply] at h
  rw [integral_add (hb.const_mul 2) hR2, integral_const_mul, integral_const_mul,
    integral_add hE (integrable_const _), integral_const] at h
  simpa only [probReal_univ, one_smul] using h

lemma expected_variance_descent (k : ℕ) :
    (∫ ξ, ‖estimatorError p I Z ξ (k + 1)‖ ^ 2 ∂Q) ≤
      (1 - beta p) * (∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q) +
      2 * beta p ^ 2 * p.σ ^ 2 + 4 * p.H ^ 2 * relaxation p ^ 2 *
        ((∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q) +
          sensitivity p * ((∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q) + ridge p ^ 2)) := by
  have h := (recursive_error_moment p I hp H g v D μ O k
    (estimator_error_integrable p I hp H g v D μ O k)).2
  have hs := expected_estimated_step_bound p I hp H g v D μ O k
  have hb := (LongTails.Proofs.SurjectiveProxLinearTuning.variance_scales_positive p hp).2.2.2
  have hc : (1 - beta p) ^ 2 ≤ 1 - beta p := by nlinarith [hb.1, hb.2.1]
  have hE : 0 ≤ (∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have he := mul_le_mul_of_nonneg_right hc hE
  have hss := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * p.H ^ 2 * relaxation p ^ 2 by positivity)
  nlinarith

lemma expected_envelope_lower (k : ℕ) :
    envelope p I p.x0 - p.Δ ≤ (∫ ξ, envelope p I (trajectory p Z ξ k).1 ∂Q) := by
  have h := integral_mono (integrable_const (envelope p I p.x0 - p.Δ))
    (envelope_integrable p I hp H g v D μ O k)
    (fun ξ => by linarith [envelope_gap p I hp H (trajectory p Z ξ k).1])
  simpa only [integral_const, probReal_univ, one_smul] using h

lemma expected_average_bound (T : ℕ) (hT : 0 < T) :
    (∑ k ∈ Finset.range T, (∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q)) / T ≤
      2 * p.Δ / (gamma p * relaxation p * T) +
      24 * sensitivity p * (p.σ ^ 2 / initialBatch p) / (beta p * T) +
      48 * sensitivity p * beta p * p.σ ^ 2 + 14 * sensitivity p * ridge p ^ 2 := by
  let φ := fun k => ∫ ξ, envelope p I (trajectory p Z ξ k).1 ∂Q
  let V := fun k => ∫ ξ, ‖estimatorError p I Z ξ k‖ ^ 2 ∂Q
  let b := fun k => ∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q
  let a := gamma p * relaxation p
  let w := 12 * a * sensitivity p / beta p
  let L := fun k => φ k + w * V k
  let lower := envelope p I p.x0 - p.Δ
  have hpos := LongTails.Proofs.SurjectiveProxLinearTuning.variance_scales_positive p hp
  have hC := hpos.1
  have hβ := hpos.2.2.2.1
  have hθ := hpos.2.2.2.2.2
  have hγ := (LongTails.Proofs.SurjectiveProxLinearModel.valid_tuning_positive p hp).2.1
  have ha : 0 < a := mul_pos hγ hθ
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hweight : w * beta p = 12 * a * sensitivity p := by
    dsimp [w]
    exact div_mul_cancel₀ _ hβ.ne'
  have hsmall : w * (4 * p.H ^ 2 * relaxation p ^ 2) ≤ 3 * a / 16 := by
    have hh := mul_le_mul_of_nonneg_left
      (LongTails.Proofs.SurjectiveProxLinearTuning.variance_absorption p hp)
      (show 0 ≤ 48 * a by positivity)
    calc
      w * (4 * p.H ^ 2 * relaxation p ^ 2) =
          48 * a * (relaxation p ^ 2 * sensitivity p * p.H ^ 2 / beta p) := by
            dsimp [w]; ring
      _ ≤ 48 * a * (1 / 256) := hh
      _ = 3 * a / 16 := by ring
  have hstep : ∀ k, L (k + 1) ≤ L k - a / 2 * b k +
      (7 * a * sensitivity p * ridge p ^ 2 + 2 * w * beta p ^ 2 * p.σ ^ 2) := by
    intro k
    have hh := LongTails.Proofs.ProxLinearVarianceLyapunov.coupled_step
      ha.le hC.le (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg (ridge p)) hw hweight hsmall
      (by simpa only [a, mul_assoc] using expected_envelope_descent p I hp H g v D μ O k)
      (expected_variance_descent p I hp H g v D μ O k)
    dsimp [L, φ, V, b, a] at *
    linarith
  have hinit : L 0 - lower ≤ p.Δ + w * (p.σ ^ 2 / initialBatch p) := by
    have hV := mul_le_mul_of_nonneg_left (initial_error_moment p I hp H g v D μ O).2 hw
    have hφ : φ 0 = envelope p I p.x0 := by
      simp only [φ, trajectory, integral_const, probReal_univ, one_smul]
    dsimp [L, lower]
    rw [hφ]
    dsimp [V] at *
    linarith
  have hlower : lower ≤ L T := by
    have hφ := expected_envelope_lower p I hp H g v D μ O T
    have hV : 0 ≤ w * V T := mul_nonneg hw (integral_nonneg (fun _ => sq_nonneg _))
    dsimp [lower, L, φ] at *
    linarith
  exact LongTails.Proofs.ProxLinearVarianceLyapunov.average_bound
    ha hβ hweight hstep hinit T hT hlower
lemma expected_average_small :
    (∑ k ∈ Finset.range (iterations p + 1),
      (∫ ξ, ‖exactModelStep p I (trajectory p Z ξ k).1‖ ^ 2 ∂Q)) /
        (iterations p + 1 : ℕ) ≤ radius p ^ 2 / 128 := by
  have hpos := LongTails.Proofs.SurjectiveProxLinearTuning.variance_scales_positive p hp
  have hβ := hpos.2.2.2.1
  have hθ := hpos.2.2.2.2.2
  have hr := hpos.2.1
  have hγ := (LongTails.Proofs.SurjectiveProxLinearModel.valid_tuning_positive p hp).2.1
  have ha : 0 < gamma p * relaxation p := mul_pos hγ hθ
  have hT : (0 : ℝ) < (iterations p + 1 : ℕ) := by positivity
  have hhor := LongTails.Proofs.SurjectiveProxLinearTuning.iteration_horizon p
  have hgapnon : 0 ≤ 1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) := by
    have hΔ := hp.2.2.2.1
    positivity
  have hβnon : 0 ≤ 64 / beta p := by positivity
  have hgap : 1024 * p.Δ ≤
      (gamma p * relaxation p) * (iterations p + 1 : ℕ) * radius p ^ 2 := by
    have h := (div_le_iff₀ (mul_pos ha (sq_pos_of_pos hr))).mp
      (show 1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) ≤
        (iterations p + 1 : ℕ) by linarith)
    nlinarith
  have hhorizon : 64 ≤ beta p * (iterations p + 1 : ℕ) := by
    have h := (div_le_iff₀ hβ).mp
      (show 64 / beta p ≤ (iterations p + 1 : ℕ) by linarith)
    nlinarith
  exact (expected_average_bound p I hp H g v D μ O (iterations p + 1) (by omega)).trans
    (LongTails.Proofs.ProxLinearVarianceLyapunov.tuned_average_small ha hβ hT hgap
      (LongTails.Proofs.SurjectiveProxLinearTuning.initial_variance_scale p hp) hhorizon
      (LongTails.Proofs.SurjectiveProxLinearTuning.variance_noise_bound p hp)
      (LongTails.Proofs.SurjectiveProxLinearTuning.ridge_scale_identity p hp))

end LongTails.Proofs.SurjectiveProxLinearEnergy
