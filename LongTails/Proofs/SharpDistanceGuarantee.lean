import LongTails.Proofs.SharpDistanceConvergence
import LongTails.Proofs.SharpDistanceBudget

namespace LongTails.Proofs.SharpDistanceGuarantee

open OracleTemplate LongTails.Algorithms.SharpDistanceEnvelope
open LongTails.Algorithms.SharpEnvelope (smoothness ratio precision recoveryCalls)
open SharpDistanceParameters (iterations)
open RecursiveEnvelopeGeometry RecursiveEnvelopeExecution SharpDistanceConvergence SharpEnvelopeBudget

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma execute_accuracy {L R ε α : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hε : 0 < ε)
    (hα : α ≤ 1 / (100 * (33 * (1 + Real.log (2 + L * R ^ 2 / ε))) ^ 12))
    {xs x0 : E} (hm : ∀ x, f xs ≤ f x) (hdist : ‖x0 - xs‖ ≤ R)
    (O : Oracle E E) (herr : ∀ k x seed, ‖O.answer k (0, x) seed - g x‖ ≤ α * ‖g x‖)
    (K : ℕ) (hK : ⌈32768 * (33 * (1 + Real.log (2 + L * R ^ 2 / ε))) ^ 16 * (1 + Real.log (33 * (1 + Real.log (2 + L * R ^ 2 / ε)))) *
      (2 + L * R ^ 2 / ε) ^ (1 / 2 + Real.log (16384 * (1 + Real.log (33 * (1 + Real.log (2 + L * R ^ 2 / ε))))) / (32 * Real.log (32 * (1 + Real.log (2 + L * R ^ 2 / ε)))))⌉₊ ≤ K)
    (seed : Unit) (ξ : (n : ℕ) → O.Seed n) :
    f (execute O (distanceEnvelopeOutput L (base (L * R ^ 2 / ε)) (depth (L * R ^ 2 / ε))
      (iterations (base (L * R ^ 2 / ε))) x0) (fun _ => K) seed ξ) - f xs ≤ ε := by
  let T := L * R ^ 2 / ε
  let b := base T
  let d := depth T
  have hL := h.pos
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hb := base_bounds hT
  have hd := depth_bounds hT
  have hb1 : 1 ≤ b := by dsimp [b]; omega
  have hc : recoveryCalls (iterations b) d ≤ K := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (SharpDistanceBudget.oracle_cost hT).trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
  have hscale : smoothness L b d * R ^ 2 ≤ ε := by
    have hs := (depth_scale hT).1
    have hp : 0 < ratio b ^ d := pow_pos (SharpEnvelopeParameters.ratio_pos hb1) d
    change L / ratio b ^ d * R ^ 2 ≤ ε
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    have ht : L * R ^ 2 / ε ≤ ratio b ^ d := by change 2 + T ≤ _ at hs; dsimp [T] at hs; linarith
    rw [div_le_iff₀ hε] at ht
    nlinarith
  have he := public_noise hT hα
  let A := distanceEnvelopeOutput L b d (iterations b) x0
  let reply := fun n x => executeAnswerAt O A seed ξ n (0, x)
  have hre : ∀ k x, ‖reply k x - g x‖ ≤ precision b d 0 * ‖g x‖ := by
    intro k x
    exact (herr _ x (ξ _)).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hh := plan_accuracy h hm hdist (by dsimp [b]; omega : 16 ≤ b) hd.2.2 hd.1 hscale reply hre
  change f (execute O A (fun _ => K) seed ξ) - f xs ≤ ε
  have hex := execute_plan_indexed
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    x0 x0 (fun _ => recoveryPlan L b d (iterations b) d x0) O seed ξ hc
  exact (congrArg (fun z => f z - f xs) hex).le.trans hh

end LongTails.Proofs.SharpDistanceGuarantee
