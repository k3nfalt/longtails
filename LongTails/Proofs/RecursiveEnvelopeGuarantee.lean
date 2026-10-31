import LongTails.Proofs.RecursiveEnvelopeConvergence
import LongTails.Proofs.RecursiveEnvelopeBudget

namespace LongTails.Proofs.RecursiveEnvelopeGuarantee

open OracleTemplate LongTails.Algorithms.RecursiveEnvelope
open RecursiveEnvelopeGeometry RecursiveEnvelopeExecution RecursiveEnvelopeConvergence RecursiveEnvelopeBudget

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma execute_accuracy {L R ε α : ℝ} {f : E → ℝ} {g : E → E}
    (h : Model L f g) (hε : 0 < ε)
    (hα : α ≤ Real.exp (-8 * (1 + Real.sqrt (Real.log (2 + L * R ^ 2 / ε)))) / 100)
    {xs x0 : E} (hm : ∀ x, f xs ≤ f x) (hdist : ‖x0 - xs‖ ≤ R)
    (O : Oracle E E) (herr : ∀ k x seed, ‖O.answer k (0, x) seed - g x‖ ≤ α * ‖g x‖)
    (K : ℕ) (hK : ⌈4 * Real.sqrt (2 + L * R ^ 2 / ε) *
      Real.exp (32 * (1 + Real.sqrt (Real.log (2 + L * R ^ 2 / ε))) *
        Real.log (32 + Real.log (2 + L * R ^ 2 / ε)))⌉₊ ≤ K)
    (seed : Unit) (ξ : (n : ℕ) → O.Seed n) :
    f (execute O (recursiveEnvelopeOutput L (depth (L * R ^ 2 / ε))
      (2048 * depth (L * R ^ 2 / ε) * 2 ^ depth (L * R ^ 2 / ε)) x0)
      (fun _ => K) seed ξ) - f xs ≤ ε := by
  let T := L * R ^ 2 / ε
  let d := depth T
  let m := 2048 * d * 2 ^ d
  have hT : 0 ≤ T := by dsimp [T]; exact div_nonneg (mul_nonneg h.pos.le (sq_nonneg R)) hε.le
  have hd : 1 ≤ d := (depth_bounds hT).1
  have hc : calls m d ≤ K := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (oracle_cost hT).trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
  have hscale : levelSmoothness L d d * R ^ 2 ≤ ε := by
    have hs := depth_scale hT
    have hp : 0 < ((4 : ℝ) ^ d) ^ d := by positivity
    change L / ((4 : ℝ) ^ d) ^ d * R ^ 2 ≤ ε
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    change L * R ^ 2 / ε ≤ ((4 : ℝ) ^ d) ^ d at hs
    rw [div_le_iff₀ hε] at hs
    nlinarith
  have he := public_noise hT hα
  let A := recursiveEnvelopeOutput L d m x0
  let reply := fun n x => executeAnswerAt O A seed ξ n (0, x)
  have hre : ∀ k x, ‖reply k x - g x‖ ≤ levelError d 0 * ‖g x‖ := by
    intro k x
    exact (herr _ x (ξ _)).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hh := plan_accuracy h hm hdist hd hscale reply hre
  change f (execute O A (fun _ => K) seed ξ) - f xs ≤ ε
  have hex := execute_plan_indexed
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    x0 x0 (fun _ => recoveryPlan L d m d x0) O seed ξ hc
  exact (congrArg (fun z => f z - f xs) hex).le.trans hh

end LongTails.Proofs.RecursiveEnvelopeGuarantee
