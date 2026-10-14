import LongTails.Proofs.ClippedExtragradientIteration
import LongTails.Proofs.ClippedExtragradientTuning
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.Clipping

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

open ContinuizedSimilarQuasar (iterateSamples)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma iterate_distance_integrable {advance : E → Ω → E}
    (ha : Measurable (Function.uncurry advance)) {d : ℝ} (hd : 0 ≤ d) (c p : E)
    (hball : ∀ x ω, ‖advance x ω - c‖ ≤ 2 * d)
    (hp : ‖p - c‖ ≤ d) (n : ℕ) :
    Integrable (fun ξ : Fin n → Ω => ‖iterateSamples advance n c ξ - p‖ ^ 2)
      (Measure.pi fun _ : Fin n => P) := by
  have hm : Measurable (fun ξ : Fin n → Ω => iterateSamples advance n c ξ) :=
    (measurable_iterateSamples ha n).comp measurable_prodMk_left
  apply Integrable.of_bound ((hm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    ((3 * d) ^ 2)
  apply Filter.Eventually.of_forall
  intro ξ
  have hi := iterateSamples_invariant (Inv := fun x => ‖x - c‖ ≤ 2 * d)
    (fun x _ ω => hball x ω) n c (by simpa using (show 0 ≤ 2 * d by positivity)) ξ
  have hh := norm_sub_le_norm_sub_add_norm_sub (iterateSamples advance n c ξ) c p
  rw [norm_sub_rev c p] at hh
  change ‖‖iterateSamples advance n c ξ - p‖ ^ 2‖ ≤ (3 * d) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma iterate_distance_bound {advance : E → Ω → E}
    (ha : Measurable (Function.uncurry advance)) {μ S d v : ℝ}
    (hμ : 0 < μ) (hμS : μ ≤ S) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hnoise : v ≤ μ * S * d ^ 2 / 2 ^ 20) (c p : E)
    (hball : ∀ x ω, ‖advance x ω - c‖ ≤ 2 * d) (hp : ‖p - c‖ ≤ d)
    (hstep : ∀ x, ‖x - c‖ ≤ 2 * d →
      (∫ ω, ‖advance x ω - p‖ ^ 2 ∂P) ≤
        (1 - μ / (4608 * S)) * ‖x - p‖ ^ 2 + v / (64 * S ^ 2))
    {n : ℕ} (hn : 2 ^ 16 * S / μ ≤ (n : ℝ)) :
    (∫ ξ : Fin n → Ω, ‖iterateSamples advance n c ξ - p‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) ≤ d ^ 2 / 4096 := by
  have hS : 0 < S := hμ.trans_le hμS
  have hq : 0 ≤ 1 - μ / (4608 * S) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hbound (x : E) (hx : ‖x - c‖ ≤ 2 * d) : ‖‖x - p‖ ^ 2‖ ≤ (3 * d) ^ 2 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub x c p
    rw [norm_sub_rev c p] at hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hh := bounded_iterate_integral ha P (fun x => ‖x - p‖ ^ 2)
    (by fun_prop) (Inv := fun x => ‖x - c‖ ≤ 2 * d)
    (fun x _ ω => hball x ω) hbound hq hstep n c
    (by simpa using (show 0 ≤ 2 * d by positivity))
  have hi : ‖c - p‖ ^ 2 ≤ d ^ 2 := by
    rw [norm_sub_rev]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hmul := mul_le_mul_of_nonneg_left hi (pow_nonneg hq n)
  have hfinal := stage_moment_bound hμ hμS hv hnoise hn
  linarith

omit [CompleteSpace E] in
lemma projected_pilot_failure {V : Ω → E} (hV : Measurable V)
    {d : ℝ} (hd : 0 < d) (c p : E) (hp : ‖p - c‖ ≤ d)
    (hvi : Integrable (fun ω => ‖V ω - p‖ ^ 2) P)
    (hv : (∫ ω, ‖V ω - p‖ ^ 2 ∂P) ≤ d ^ 2 / 4096) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | d / 2 < ‖RobustGradient.centeredClip (2 * d) c
        (RobustGradient.pilotCenter d (fun i => V (ξ i))) - p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have ht := RobustGradient.norm_tail_le_second_moment hvi
    (show 0 < d / 6 by positivity) hv
  have ht' : P.real {ω | d / 6 < ‖V ω - p‖} ≤ 1 / 16 := by
    apply ht.trans
    rw [div_le_iff₀ (by positivity : 0 < (d / 6) ^ 2)]
    nlinarith [sq_nonneg d]
  apply (measure_mono ?_).trans (RobustGradient.pilotCenter_failure_probability hV p d ht' k)
  intro ξ hξ
  have hn := norm_clip_sub_le (show 0 ≤ 2 * d by positivity)
    (show ‖p - c‖ ≤ 2 * d by linarith)
    (RobustGradient.pilotCenter d (fun i => V (ξ i)) - c)
  have he : RobustGradient.centeredClip (2 * d) c
      (RobustGradient.pilotCenter d (fun i => V (ξ i))) - p =
      clip (2 * d) (RobustGradient.pilotCenter d (fun i => V (ξ i)) - c) - (p - c) := by
    unfold RobustGradient.centeredClip
    abel
  have he' : (RobustGradient.pilotCenter d (fun i => V (ξ i)) - c) - (p - c) =
      RobustGradient.pilotCenter d (fun i => V (ξ i)) - p := by abel
  rw [he'] at hn
  change d / 2 < ‖RobustGradient.centeredClip (2 * d) c
    (RobustGradient.pilotCenter d (fun i => V (ξ i))) - p‖ at hξ
  rw [he] at hξ
  exact lt_of_lt_of_le hξ hn

end OracleTemplate.ClippedExtragradient
