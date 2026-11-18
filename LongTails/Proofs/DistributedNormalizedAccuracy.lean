import LongTails.Proofs.DistributedNormalizedEstimatorProcess
import LongTails.Proofs.DistributedNormalizedTuning
import LongTails.Proofs.DistributedNormalizedConvergence

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedAccuracy

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning
open DistributedNormalizedBlocks
open DistributedNormalizedAdaptive

lemma configured_consensus (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (k : ℕ) (hk : k ≤ iterations p) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p)))
    let S := fun ξ => pairTrajectory p (config p) g ξ k
    (∀ i, Integrable (fun ξ => ‖workerError p i (S ξ)‖ ^ 2) P ∧
      (∫ ξ, ‖workerError p i (S ξ)‖ ^ 2 ∂P) ≤ stepSize p ^ 2 * DistributedNormalizedTuning.consensusFactor p) ∧
    Integrable (fun ξ => ‖meanError p (S ξ)‖ ^ 2) P ∧
      (∫ ξ, ‖meanError p (S ξ)‖ ^ 2 ∂P) ≤
        stepSize p ^ 2 * DistributedNormalizedTuning.consensusFactor p / p.n := by
  intro P S
  have hη := (DistributedNormalizedPrecision.stepSize_pos p hL hε).le
  obtain ⟨hsi, hsr, _, hvr, hcapi, hcapr⟩ := DistributedNormalizedPrecision.downlink_precision p hd hL hΔ hε
  have hvi : (config p).incrementSpacing ^ 2 ≤ p.d * (config p).stepSize ^ 2 := by
    change (stepSize p * Real.sqrt p.d) ^ 2 ≤ p.d * stepSize p ^ 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p.d)]
    nlinarith
  have hw (i : Fin p.n) := worker_error_energy p (config p) g hg μ (iterations p) i hη hsr hsi
    hcapi hcapr hvr hvi k hk
  have hm := mean_error_energy p (config p) g hg μ (iterations p) hη hsr hsi
    hcapi hcapr hvr hvi k hk
  have hp := DistributedNormalizedTuning.periodic_consensus_bound p k (η := stepSize p)
  refine ⟨fun i => ⟨(hw i).1, (hw i).2.trans hp⟩, hm.1, ?_⟩
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  have hℓ : (downlinkCount p : ℝ) ≠ 0 := by exact_mod_cast (downlinkCount p).ne_zero
  have he : (config p).stepSize ^ 2 / (64 * p.n) +
      ((k % ((config p).refreshPeriod : ℕ) : ℕ) : ℝ) *
        (2 * p.d * (config p).stepSize ^ 2 / (((config p).downlinkCount : ℝ) * p.n)) =
      (stepSize p ^ 2 / 64 + ((k % (refreshPeriod p : ℕ) : ℕ) : ℝ) *
        (2 * p.d * stepSize p ^ 2 / downlinkCount p)) / p.n := by
    change stepSize p ^ 2 / (64 * p.n) + ((k % (refreshPeriod p : ℕ) : ℕ) : ℝ) *
      (2 * p.d * stepSize p ^ 2 / ((downlinkCount p : ℝ) * p.n)) = _
    field_simp
  exact hm.2.trans (he.le.trans (div_le_div_of_nonneg_right hp (by positivity)))

lemma configured_root_gradient (p : Params) (hd : 0 < p.d) (hL : 0 < p.L)
    (hε : 0 < p.ε) (f : Point p → ℝ)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p (config p))
    (k : ℕ) (hk : k ≤ iterations p) :
    ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ≤ gradientRadius p := by
  have hη := (DistributedNormalizedPrecision.stepSize_pos p hL hε).le
  have hp := DistributedNormalizedPath.root_path p (config p) hη
    (assembledDraws p (config p) ξ) g (assembledSamples p (config p) ξ) k
  have hd' : (1 : ℝ) ≤ p.d := by exact_mod_cast Nat.succ_le_of_lt hd
  have hk' : (k : ℝ) ≤ (iterations p : ℝ) := by exact_mod_cast hk
  have hR : ‖(pairTrajectory p (config p) g ξ k).1 - p.x0‖ ≤
      4 * p.d * ((iterations p : ℕ) + 1 : ℕ) * stepSize p := by
    apply hp.trans
    change (k : ℝ) * stepSize p ≤ _
    have hnonneg : (0 : ℝ) ≤ (iterations p : ℕ) := Nat.cast_nonneg _
    have hcount : (k : ℝ) ≤ 4 * p.d * ((iterations p : ℕ) + 1 : ℕ) := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hd' (show 0 ≤ (iterations p : ℝ) + 1 by positivity)]
    exact mul_le_mul_of_nonneg_right hcount hη
  have hb := DistributedNormalizedPath.gradient_at_bounded_point p f hL hf hlip lower hlower hgap _ _ hR
  unfold gradientRadius
  convert hb using 1
  ring

set_option maxHeartbeats 800000 in
lemma configured_expected_error (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hQ : 0 ≤ p.Q)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (k : ℕ) (hk : k ≤ iterations p) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p)))
    let S := fun ξ => pairTrajectory p (config p) g ξ k
    let V := stepSize p ^ 2 * DistributedNormalizedTuning.consensusFactor p
    let β := Real.sqrt (2 * compressionVariance p / p.n)
    Integrable (fun ξ => ‖DistributedNormalizedEstimator.roundEstimator p (config p) g (S ξ).2 (ξ k) -
      gradient f (S ξ).1‖) P ∧
      (∫ ξ, ‖DistributedNormalizedEstimator.roundEstimator p (config p) g (S ξ).2 (ξ k) - gradient f (S ξ).1‖ ∂P) ≤
        β * (∫ ξ, ‖gradient f (S ξ).1‖ ∂P) + p.L * β * Real.sqrt V +
        min (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V) +
        (Real.sqrt ((1 + compressionVariance p) * (p.σ ^ 2 / batch p) / p.n) +
          Real.sqrt (DistributedNormalizedEstimator.gridVariance p (config p) / p.n) +
          (p.σ ^ 2 / batch p) / (4 * clipMargin p)) := by
  intro P S V β
  have hgm (i : Fin p.n) := (hg i).measurable
  have hS : Measurable S := measurable_pairTrajectory p (config p) g hgm k
  obtain ⟨hwi, hmi, hmv⟩ := configured_consensus p hd hL hΔ hε g hgm μ k hk
  have hTaylor := DistributedNormalizedDrift.expected_disagreement_taylor P p (gradient f) S hS
    hL.le hQ hdiff hlip hH hmi hmv (fun i => (hwi i).1) (fun i => (hwi i).2)
  have hLip := DistributedNormalizedDrift.expected_disagreement_lipschitz P p (gradient f) S hS
    hL.le hlip (fun i => (hwi i).1) (fun i => (hwi i).2)
  have hD := le_min hTaylor.2 hLip.2
  have hroot (ξ : ℕ → RoundBlock p (config p)) : ‖gradient f (S ξ).1‖ ≤ gradientRadius p :=
    configured_root_gradient p hd hL hε f hf hlip lower hlower hgap g ξ k hk
  have hworkers (ξ : ℕ → RoundBlock p (config p)) (i : Fin p.n) : ‖gradient f ((S ξ).2 i)‖ ≤ gradientRadius p :=
    DistributedNormalizedPrecision.configured_worker_gradient p hd hL hΔ hε f hf hlip lower hlower hgap
      (assembledDraws p (config p) ξ) g (assembledSamples p (config p) ξ) k hk i
  have ht := DistributedNormalizedEstimatorProcess.expected_estimator_error p (config p) μ f g hg k S hS
    (fun ξ ζ h => pairTrajectory_prefix p (config p) g ξ ζ k h)
    (gradientRadius p) (clipMargin p) p.L V
    (min (p.L * Real.sqrt (V / p.n) + p.Q * V) (p.L * Real.sqrt V))
    (DistributedNormalizedPrecision.gradientRadius_nonneg p hL hε)
    (DistributedNormalizedPrecision.clipMargin_pos p hε) hL.le hroot hworkers hlip rfl
    (DistributedNormalizedPrecision.uplink_spacing_pos p hd hε)
    (DistributedNormalizedPrecision.uplink_capacity p hd hL hΔ hε)
    (fun i => (hwi i).1) (fun i => (hwi i).2) hTaylor.1 hD
  exact ht

set_option maxHeartbeats 800000 in
lemma configured_error_small (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hQ : 0 ≤ p.Q) (hh : ∀ i, 0 < p.h i)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (k : ℕ) (hk : k ≤ iterations p) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p)))
    let S := fun ξ => pairTrajectory p (config p) g ξ k
    Integrable (fun ξ => ‖DistributedNormalizedEstimator.roundEstimator p (config p) g (S ξ).2 (ξ k) -
      gradient f (S ξ).1‖) P ∧
      (∫ ξ, ‖DistributedNormalizedEstimator.roundEstimator p (config p) g (S ξ).2 (ξ k) - gradient f (S ξ).1‖ ∂P) ≤
        (∫ ξ, ‖gradient f (S ξ).1‖ ∂P) / 8 + p.ε / 32 := by
  intro P S
  obtain ⟨hi, hb⟩ := configured_expected_error p hd hL hΔ hε hQ f hf hlip hdiff hH lower hlower hgap g μ hg k hk
  have hconst := DistributedNormalizedTuning.total_additive_error_small p hd hL hQ hε hh
  have hcoef := DistributedNormalizedTuning.compression_coefficient_small p hd hh
  have hG : 0 ≤ (∫ ξ, ‖gradient f (S ξ).1‖ ∂P) := integral_nonneg fun _ => norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hcoef hG
  refine ⟨hi, ?_⟩
  linarith

lemma assembled_estimator_eq (p : Params) (cfg : LongTails.Algorithms.DistributedNormalizedDownlink.Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) :
    LongTails.Algorithms.DistributedNormalizedDownlink.estimator p cfg (assembledDraws p cfg ξ) g
      (assembledSamples p cfg ξ) k (LongTails.Algorithms.DistributedNormalizedDownlink.trajectory p cfg
        (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k) =
      DistributedNormalizedEstimator.roundEstimator p cfg g (pairTrajectory p cfg g ξ k).2 (ξ k) := by
  rw [DistributedNormalizedEstimator.estimator_from_workerReplies]
  rfl

set_option maxHeartbeats 800000 in
lemma master_gradient_average (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hQ : 0 ≤ p.Q) (hh : ∀ i, 0 < p.h i)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p)))
    (∑ k ∈ Finset.range (iterations p), (∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P)) /
      (iterations p : ℝ) ≤ 49 * p.ε / 192 := by
  intro P
  have hη := DistributedNormalizedPrecision.stepSize_pos p hL hε
  have hgm (i : Fin p.n) := (hg i).measurable
  have hi (k : ℕ) : Integrable (fun ξ => ‖gradient f (pairTrajectory p (config p) g ξ k).1‖) P :=
    DistributedNormalizedConvergence.root_gradient_integrable P p (config p) hη.le
      (measurable_assembledDraws p (config p)) (measurable_assembledSamples p (config p))
      g hgm f hL.le hlip k
  have herr (k : ℕ) (hk : k < iterations p) := configured_error_small p hd hL hΔ hε hQ hh
    f hf hlip hdiff hH lower hlower hgap g μ hg k hk.le
  have he (k : ℕ) (hk : k < iterations p) : Integrable (fun ξ =>
      ‖LongTails.Algorithms.DistributedNormalizedDownlink.estimator p (config p)
        (assembledDraws p (config p) ξ) g (assembledSamples p (config p) ξ) k
        (LongTails.Algorithms.DistributedNormalizedDownlink.trajectory p (config p)
          (assembledDraws p (config p) ξ) g (assembledSamples p (config p) ξ) k) -
        gradient f (pairTrajectory p (config p) g ξ k).1‖) P := by
    simp_rw [assembled_estimator_eq]
    exact (herr k hk).1
  have hgap' (x : Point p) : f p.x0 - f x ≤ p.Δ := by linarith [hlower x]
  have hdesc := DistributedNormalizedConvergence.integrated_descent P p (config p) hη.le
    (assembledDraws p (config p)) (assembledSamples p (config p)) g f hf hlip hL.le
    (iterations p) hgap' (fun k _ => hi k) he
  simp_rw [assembled_estimator_eq] at hdesc
  have hsum : (∑ k ∈ Finset.range (iterations p), (∫ ξ,
      ‖DistributedNormalizedEstimator.roundEstimator p (config p) g (pairTrajectory p (config p) g ξ k).2 (ξ k) -
        gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P)) ≤
      (∑ k ∈ Finset.range (iterations p), (∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P)) / 8 +
        (iterations p : ℝ) * p.ε / 32 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (iterations p),
          ((∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P) / 8 + p.ε / 32) :=
        Finset.sum_le_sum fun k hk => (herr k (Finset.mem_range.mp hk)).2
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  exact DistributedNormalizedConvergence.normalized_sum_absorption hη
    (show 0 < (iterations p : ℝ) by exact_mod_cast (iterations p).pos) hdesc hsum
    (DistributedNormalizedTuning.iteration_gap p hL hε)
    (DistributedNormalizedTuning.step_scale p hL).le

set_option maxHeartbeats 800000 in
lemma master_output_accuracy (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hQ : 0 ≤ p.Q) (hh : ∀ i, 0 < p.h i)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p)))
    let U := (PMF.uniformOfFintype (Fin (iterations p))).toMeasure.prod P
    let F := fun z : Fin (iterations p) × (ℕ → RoundBlock p (config p)) =>
      ‖gradient f (pairTrajectory p (config p) g z.2 z.1.val).1‖
    Integrable F U ∧ (∫ z, F z ∂U) ≤ p.ε := by
  intro P U F
  have hη := DistributedNormalizedPrecision.stepSize_pos p hL hε
  have hgm (i : Fin p.n) := (hg i).measurable
  have hgc : LipschitzWith ⟨p.L, hL.le⟩ (gradient f) := lipschitzWith_iff_norm_sub_le.mpr hlip
  have hm (i : Fin (iterations p)) : Measurable (fun ξ => ‖gradient f (pairTrajectory p (config p) g ξ i.val).1‖) :=
    (hgc.continuous.measurable.comp (measurable_fst.comp (measurable_pairTrajectory p (config p) g hgm i.val))).norm
  have hi (i : Fin (iterations p)) : Integrable (fun ξ => ‖gradient f (pairTrajectory p (config p) g ξ i.val).1‖) P :=
    DistributedNormalizedConvergence.root_gradient_integrable P p (config p) hη.le
      (measurable_assembledDraws p (config p)) (measurable_assembledSamples p (config p))
      g hgm f hL.le hlip i.val
  obtain ⟨hFi, hF⟩ := DistributedNormalizedConvergence.uniform_output_integral P (iterations p)
    (fun i ξ => ‖gradient f (pairTrajectory p (config p) g ξ i.val).1‖) hm hi
  have hsum : (∑ i : Fin (iterations p), ∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ i.val).1‖ ∂P) =
      ∑ k ∈ Finset.range (iterations p), (∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P) :=
    Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P) (iterations p)
  rw [hsum] at hF
  have hrate := master_gradient_average p hd hL hΔ hε hQ hh f hf hlip hdiff hH lower hlower hgap g μ hg
  refine ⟨hFi, ?_⟩
  calc
    _ = (∑ k ∈ Finset.range (iterations p), (∫ ξ, ‖gradient f (pairTrajectory p (config p) g ξ k).1‖ ∂P)) /
        (iterations p : ℝ) := by rw [hF]; ring
    _ ≤ 49 * p.ε / 192 := hrate
    _ ≤ p.ε := by linarith

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedDownlink.output
  LongTails.Algorithms.DistributedNormalizedDownlink.trajectory pairTrajectory extractedMaster

set_option maxHeartbeats 800000 in
lemma output_accuracy (p : Params) [Nonempty (Fin p.d)] (hd : 0 < p.d)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hQ : 0 ≤ p.Q) (hh : ∀ i, 0 < p.h i)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.Q * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (g : Fin p.n → Point p → p.Ω → Point p) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (P : ProbabilityMeasure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    (hworkers : ProbabilityTheory.iIndepFun
      (fun i (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i) (P : Measure _))
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) => ξ i k)
      (μ i : Measure p.Ω) (P : Measure _)) :
    let U := (LongTails.Algorithms.DistributedNormalizedDownlink.seedLaw p (config p) :
      Measure (LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p))).prod (P : Measure _)
    let Y := fun z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
        LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams =>
      LongTails.Algorithms.DistributedNormalizedDownlink.output p (config p) z.1.2 g z.2 z.1.1
    Measurable Y ∧ Integrable (fun z => ‖gradient f (Y z)‖) U ∧ (∫ z, ‖gradient f (Y z)‖ ∂U) ≤ p.ε := by
  intro U Y
  have hmap := @seed_master_preserving p (config p) (inferInstance : Nonempty (Fin p.d))
    (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))
    (inferInstance : IsProbabilityMeasure (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)))
    μ hworkers hIID
  have hl : ProbabilityTheory.HasLaw
      (fun z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
        LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams =>
          (z.1.1, extractedMaster p (config p) (z.1.2, z.2)))
      ((PMF.uniformOfFintype (Fin (iterations p))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => (roundLaw p (config p) μ : Measure (RoundBlock p (config p))))) U :=
    ⟨hmap.measurable.aemeasurable, hmap.map_eq⟩
  obtain ⟨hi, hb⟩ := master_output_accuracy p hd hL hΔ hε hQ hh f hf hlip hdiff hH lower hlower hgap g μ hg
  have hD : Measurable (fun z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
      LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hS : Measurable (fun z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
      LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams => z.2) := measurable_snd
  have hI : Measurable (fun z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
      LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hY : Measurable Y := DistributedNormalizedMeasurability.measurable_output p (config p) g
    (fun i => (hg i).measurable) hD hS hI
  have he (z : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
      LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) :
      ‖gradient f (pairTrajectory p (config p) g (extractedMaster p (config p) (z.1.2, z.2)) z.1.1.val).1‖ =
        ‖gradient f (Y z)‖ := by
    simp only [pairTrajectory, assembled_extracted_draws, assembled_extracted_samples,
      Y, LongTails.Algorithms.DistributedNormalizedDownlink.output]
  have hpi := hl.integrable_comp hi
  have hpb := (hl.integral_comp hi.aestronglyMeasurable).trans_le hb
  refine ⟨hY, hpi.congr (Filter.Eventually.of_forall he), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall he)).symm.trans_le hpb

end LongTails.Proofs.DistributedNormalizedAccuracy
