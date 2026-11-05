import LongTails.Algorithms.SharpEnvelope

namespace LongTails.Algorithms.SharpDistanceEnvelope

open OracleTemplate
open SharpEnvelope (smoothness precision momentum gradientCalls recoveryCalls)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def lastPlan {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost)
    (L μ θ : ℝ) (center : E) : (n : ℕ) → E × E → QueryPlan E E E (cost * n)
  | 0, s => .done s.1
  | n + 1, s =>
      let y := InexactGradient.query θ s
      (oraclePlan y).bind fun reply =>
        lastPlan oraclePlan L μ θ center n
          (SharpEnvelope.step L μ θ s (reply + μ • (y - center)))

noncomputable def innerPlan {cost : ℕ} (oraclePlan : E → QueryPlan E E E cost)
    (L μ β θ : ℝ) (center : E) (warm refine : ℕ) :
    QueryPlan E E E (cost * refine + cost * warm) :=
  (RecursiveEnvelope.innerPlan oraclePlan L μ (2 * β) center warm (center, center)).bind fun x =>
    lastPlan oraclePlan L μ θ center refine (x, x)

noncomputable def gradientPlan (L : ℝ) (b d n : ℕ) :
    (i : ℕ) → E → QueryPlan E E E (gradientCalls n i)
  | 0, y => .ask y (fun reply => .done reply)
  | i + 1, y =>
      let μ := smoothness L b (i + 1)
      (innerPlan (gradientPlan L b d n i) (smoothness L b i + μ) μ
        (precision b d i) (momentum b) y n n).map fun x => μ • (y - x)

noncomputable def proxPlan (L : ℝ) (b d n i : ℕ) (y : E) :
    QueryPlan E E E (gradientCalls n (i + 1)) :=
  let μ := smoothness L b (i + 1)
  innerPlan (gradientPlan L b d n i) (smoothness L b i + μ) μ
    (precision b d i) (momentum b) y n n

noncomputable def recoveryPlan (L : ℝ) (b d n : ℕ) :
    (i : ℕ) → E → QueryPlan E E E (recoveryCalls n i)
  | 0, y => .done y
  | i + 1, y => (proxPlan L b d n i y).bind (recoveryPlan L b d n i)

noncomputable def distanceEnvelopeOutput (L : ℝ) (b d n : ℕ) (x0 : E) : Algorithm E E E :=
  QueryPlan.algorithm (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
    MeasureTheory.ProbabilityMeasure Unit) x0 x0 (recoveryCalls n d)
    (fun _ => recoveryPlan L b d n d x0)

end LongTails.Algorithms.SharpDistanceEnvelope
