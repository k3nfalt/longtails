import LongTails.Algorithms.SharpDistanceEnvelope
import LongTails.Proofs.RecursiveEnvelopeExecution

namespace LongTails.Proofs.SharpDistanceExecution

open OracleTemplate RecursiveEnvelopeExecution
open LongTails.Algorithms.SharpDistanceEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma evalAt_lastPlan {cost : ℕ} (reply : ℕ → E → E)
    (oraclePlan : E → QueryPlan E E E cost) (L μ θ : ℝ) (center : E)
    (N offset call : ℕ) (state : E × E) :
    evalAt reply (lastPlan oraclePlan L μ θ center N state) (offset + cost * call) =
      (StochasticGradient.advance
        (fun k s => LongTails.Algorithms.SharpEnvelope.step L μ θ s
          (evalAt reply (oraclePlan (InexactGradient.query θ s)) (offset + cost * k) +
            μ • (InexactGradient.query θ s - center))) N call state).1 := by
  induction N generalizing call state with
  | zero => rfl
  | succ N ih =>
      simp only [lastPlan, evalAt_bind, StochasticGradient.advance]
      rw [show offset + cost * call + cost = offset + cost * (call + 1) by ring]
      exact ih (call + 1) _

lemma evalAt_gradientPlan (reply : ℕ → E → E) (L : ℝ) (b d n i : ℕ)
    (x : E) (call : ℕ) :
    evalAt reply (gradientPlan L b d n (i + 1) x) call =
      LongTails.Algorithms.SharpEnvelope.smoothness L b (i + 1) •
        (x - evalAt reply (proxPlan L b d n i x) call) := by
  exact evalAt_map reply _ _ call

lemma evalAt_recoveryPlan (reply : ℕ → E → E) (L : ℝ) (b d n i : ℕ)
    (x : E) (call : ℕ) :
    evalAt reply (recoveryPlan L b d n (i + 1) x) call =
      evalAt reply (recoveryPlan L b d n i (evalAt reply (proxPlan L b d n i x) call))
        (call + LongTails.Algorithms.SharpEnvelope.gradientCalls n (i + 1)) := by
  exact evalAt_bind reply _ _ call

end LongTails.Proofs.SharpDistanceExecution
