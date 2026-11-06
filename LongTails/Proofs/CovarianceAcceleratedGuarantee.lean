import LongTails.Proofs.CovarianceAcceleratedRate
import LongTails.Proofs.CovarianceAcceleratedBudget

open MeasureTheory ProbabilityTheory Convexity
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Proofs.CovarianceAcceleratedBudget

namespace LongTails.Proofs.CovarianceAcceleratedGuarantee

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma calibrated_failure_probability {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    {f : E → ℝ} {g : E → Ω → E} {σ s L R ε δ : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 < L) (hσ : 0 ≤ σ) (hs : 0 ≤ s) (hsσ : s ≤ σ) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x0 xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R) :
    let ell := Real.log (3 / δ)
    let J := Real.log ((2 : ℝ) ^ 56 * (1 + L * R ^ 2 / ε + R ^ 2 * σ ^ 2 / ε ^ 2) / δ ^ 2)
    let N := ⌈(2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt (L * R ^ 2 / ε) * J + R ^ 2 * (σ ^ 2 + s ^ 2 * ell) / ε ^ 2)⌉₊
    let j := Real.log (54 * (N : ℝ) / δ)
    let k := ⌈16 * j⌉₊
    let T := N - k
    let cfg := LongTails.Algorithms.CovarianceAcceleratedTuned.config x0 L R σ s j ell k T
    P {ω | ε < f (output cfg g (fun i => ξ i ω) N) - f xstar} ≤ ENNReal.ofReal δ := by
  intro ell J N j k T cfg
  let A := L * R ^ 2 / ε
  let S := R ^ 2 * σ ^ 2 / ε ^ 2
  let Q := R ^ 2 * (σ ^ 2 + s ^ 2 * ell) / ε ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hell1 : 1 ≤ ell := confidence_log_one hδ hδ1
  have hell : 0 < ell := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQS : Q ≤ S * (1 + Real.log (3 / δ)) := by
    have hsq : s ^ 2 ≤ σ ^ 2 := by gcongr
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hell.le)
      (show 0 ≤ R ^ 2 / ε ^ 2 by positivity)
    dsimp [Q, S]
    change _ ≤ R ^ 2 * σ ^ 2 / ε ^ 2 * (1 + ell)
    ring_nf at hh ⊢
    linarith
  have hcal := budget_calibration hA hS hQ hδ hδ1 hQS
  change 1 ≤ j ∧ Real.log (3 / δ) ≤ j ∧ j ≤ k ∧ 1 ≤ k ∧ 1 ≤ T ∧
    (k : ℝ) ^ 2 ≤ T ∧ (2 : ℝ) ^ 39 * (J ^ 2 + Real.sqrt A * J + Q) ≤ T ∧
    (k : ℝ) ≤ 51 * J ∧ k + T = N at hcal
  obtain ⟨hj, hej, hjk, hk, hT, hkT, hTscale, hkJ, htotal⟩ := hcal
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hJ : 1 ≤ J := (confidence_log_bounds hA hS hδ hδ1).1
  have haccuracy := horizon_accuracy_conditions hA hQ hJ (Nat.cast_nonneg k) hkJ hTscale
  have hstat : 34359738368 * R ^ 2 * (σ ^ 2 + s ^ 2 * ell) / ε ^ 2 ≤ (T : ℝ) := by
    simpa only [Q, mul_div_assoc, mul_assoc] using haccuracy.2
  have hrate := accuracy_from_horizon hR.le hσ hs hTr hell.le hε haccuracy.1 hstat
  have hN : 0 < N := by omega
  have htail := tail_allocation hδ hδ1 hN (show T ≤ N by exact Nat.sub_le _ _)
    (show 16 * Real.log (54 * (N : ℝ) / δ) ≤ k from Nat.le_ceil _)
  have hp := CovarianceAcceleratedRate.tuned_failure_probability hsamples ho hc hg hlip hL hσ hs hR
    x0 xstar hmin hdist k T hk hT hj hell hej hjk hkT htail.2
  change P {ω | 65536 * (L * R ^ 2 * (k : ℝ) ^ 2 / (T : ℝ) ^ 2 +
      R * (σ + s * Real.sqrt ell) / Real.sqrt T) <
      f (output cfg g (fun i => ξ i ω) (k + T)) - f xstar} ≤ _ at hp
  rw [htotal] at hp
  apply (measure_mono (show {ω | ε < f (output cfg g (fun i => ξ i ω) N) - f xstar} ⊆
    {ω | 65536 * (L * R ^ 2 * (k : ℝ) ^ 2 / (T : ℝ) ^ 2 +
      R * (σ + s * Real.sqrt ell) / Real.sqrt T) <
      f (output cfg g (fun i => ξ i ω) N) - f xstar} from
        fun ω hbad => lt_of_le_of_lt hrate hbad)).trans (hp.trans ?_)
  have he : Real.exp (-ell) = δ / 3 := exponential_confidence hδ
  have hreal : (T : ℝ) * Real.exp (-7 * k / 32) + 2 * Real.exp (-ell) ≤ δ := by
    rw [he]
    linarith [htail.1]
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)] at hh
  norm_num at hh ⊢
  exact hh

end LongTails.Proofs.CovarianceAcceleratedGuarantee
