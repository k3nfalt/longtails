import LongTails.Algorithms.RecursiveEnvelope

namespace LongTails.Algorithms.SharpEnvelope

open OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def step (L μ θ : ℝ) (s : E × E) (g : E) : E × E :=
  let y := InexactGradient.query θ s
  (y - (1 / L) • g, (1 - θ) • s.2 + θ • y - (θ / μ) • g)

noncomputable def sumPlan {c : ℕ} (oraclePlan : E → QueryPlan E E E c)
    (L μ θ : ℝ) (center : E) : (n : ℕ) → E × E → QueryPlan E E E (c * n)
  | 0, _ => .done 0
  | n + 1, s =>
      let y := InexactGradient.query θ s
      (oraclePlan y).bind fun reply =>
        (sumPlan oraclePlan L μ θ center n
          (step L μ θ s (reply + μ • (y - center)))).map (s.1 + ·)

noncomputable def innerPlan {c : ℕ} (oraclePlan : E → QueryPlan E E E c)
    (L μ β θ : ℝ) (center : E) (warm average : ℕ) :
    QueryPlan E E E (c * average + c * warm) :=
  (RecursiveEnvelope.innerPlan oraclePlan L μ (2 * β) center warm (center, center)).bind fun x =>
    (sumPlan oraclePlan L μ θ center average (x, x)).map fun total =>
      (1 / (average : ℝ)) • total


noncomputable def ratio (b : ℕ) : ℝ := 4 * (b : ℝ) ^ 32 - 1

noncomputable def smoothness (L : ℝ) (b i : ℕ) : ℝ := L / ratio b ^ i

noncomputable def precision (b d i : ℕ) : ℝ :=
  (1 + (i : ℝ) / (d + 1)) / (100 * (b : ℝ) ^ 12)

noncomputable def momentum (b : ℕ) : ℝ := 1 / (4 * (b : ℝ) ^ 16)

def gradientCalls (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => gradientCalls n i * n + gradientCalls n i * n

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

def recoveryCalls (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => recoveryCalls n i + gradientCalls n (i + 1)

noncomputable def recoveryPlan (L : ℝ) (b d n : ℕ) :
    (i : ℕ) → E → QueryPlan E E E (recoveryCalls n i)
  | 0, y => .done y
  | i + 1, y => (proxPlan L b d n i y).bind (recoveryPlan L b d n i)

noncomputable def sharpEnvelopeOutput (L : ℝ) (b d n : ℕ) (x0 : E) : Algorithm E E E :=
  QueryPlan.algorithm (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
    MeasureTheory.ProbabilityMeasure Unit) x0 x0 (recoveryCalls n d)
    (fun _ => recoveryPlan L b d n d x0)

end LongTails.Algorithms.SharpEnvelope
