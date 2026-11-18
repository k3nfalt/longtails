import LongTails.Algorithms.SampledQueryPlan
import LongTails.Setups.SublevelPLBoundedVariance

namespace OracleTemplate.SublevelWeighted

open LongTails.Setups.SublevelPLBoundedVariance

def calls (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b k + calls b k

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def collect (x : E) : (n : ℕ) → QueryPlan E E E n
  | 0 => .done 0
  | n + 1 => .ask x fun v => (collect x n).map (v + ·)

noncomputable def outputPlan (L : ℝ) (x0 : E) (b : ℕ → ℕ) :
    (k : ℕ) → QueryPlan E E E (calls b k)
  | 0 => .done x0
  | k + 1 => (outputPlan L x0 b k).bind fun x =>
      (collect x (b k)).map fun v => x - (1 / L) • ((1 / (b k : ℝ)) • v)

noncomputable def steps (p : Public) : ℕ :=
  ⌈16 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) / (2 - p.α)⌉₊ + 1

noncomputable def scale (p : Public) : ℝ :=
  1 + 128 * p.σ ^ 2 * (steps p / (p.L * p.ε) + (p.τ / p.ε) ^ (2 / p.α))

noncomputable def batch (K : ℕ) (v : ℝ) (j : ℕ) : ℕ :=
  1 + ⌈v * Real.sqrt K / Real.sqrt (j + 1)⌉₊

noncomputable def horizon (p : Public) : ℕ :=
  if 2 * p.L * p.ε * (p.τ / p.ε) ^ (2 / p.α) < 1 then 0 else steps p

noncomputable def method (p : Public) : Algorithm p.E p.E p.E :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ p.x0 p.x0 _
    (fun _ => outputPlan p.L p.x0 (batch (steps p) (scale p)) (horizon p))

end OracleTemplate.SublevelWeighted
