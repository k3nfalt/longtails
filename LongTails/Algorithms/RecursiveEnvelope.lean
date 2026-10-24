import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.InexactAccelerated

namespace LongTails.Algorithms.RecursiveEnvelope

open OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def levelSmoothness (L : ℝ) (d i : ℕ) : ℝ := L / ((4 : ℝ) ^ d) ^ i

noncomputable def levelError (d i : ℕ) : ℝ := (16 : ℝ) ^ i / ((100 : ℝ) * 64 ^ d)

noncomputable def innerPlan {c : ℕ} (oraclePlan : E → QueryPlan E E E c)
    (L μ α : ℝ) (center : E) : (n : ℕ) → E × E → QueryPlan E E E (c * n)
  | 0, state => .done state.1
  | n + 1, state =>
      let θ := InexactGradient.momentum L μ α
      let y := InexactGradient.query θ state
      (oraclePlan y).bind fun reply =>
        innerPlan oraclePlan L μ α center n
          (InexactGradient.step L μ θ state (reply + μ • (y - center)))

noncomputable def gradientPlan (L : ℝ) (d m : ℕ) :
    (i : ℕ) → E → QueryPlan E E E (m ^ i)
  | 0, y => .ask y (fun reply => .done reply)
  | i + 1, y =>
      let μ := levelSmoothness L d (i + 1)
      let plan := innerPlan (gradientPlan L d m i)
        (levelSmoothness L d i + μ) μ (2 * levelError d i) y m (y, y)
      plan.map fun x => μ • (y - x)

noncomputable def proxPlan (L : ℝ) (d m i : ℕ) (y : E) :
    QueryPlan E E E (m ^ (i + 1)) :=
  let μ := levelSmoothness L d (i + 1)
  innerPlan (gradientPlan L d m i)
    (levelSmoothness L d i + μ) μ (2 * levelError d i) y m (y, y)

def calls (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => calls m i + m ^ (i + 1)

noncomputable def recoveryPlan (L : ℝ) (d m : ℕ) :
    (i : ℕ) → E → QueryPlan E E E (calls m i)
  | 0, y => .done y
  | i + 1, y => (proxPlan L d m i y).bind (recoveryPlan L d m i)

noncomputable def recursiveEnvelopeOutput (L : ℝ) (d m : ℕ) (x0 : E) : Algorithm E E E :=
  QueryPlan.algorithm (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
    MeasureTheory.ProbabilityMeasure Unit) x0 x0 (calls m d) (fun _ => recoveryPlan L d m d x0)

end LongTails.Algorithms.RecursiveEnvelope
