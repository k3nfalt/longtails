import LongTails.Algorithms.RecursiveEnvelope
import LongTails.Algorithms.DampedAccelerated

namespace LongTails.Algorithms.TwoLevelRelativeErrorConvex

open OracleTemplate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def horizon (α T : ℝ) : ℕ :=
  ⌈Real.sqrt (12 * Real.exp 1 * α ^ 4 * T) + 1536 * Real.exp 1 * α ^ 6 * T⌉₊

noncomputable def innerCount (α : ℝ) : ℕ :=
  let s := 1 / α ^ 4
  let r := (1 + s) / (1 - 2 * α)
  ⌈(8 * Real.sqrt r + 128 * α ^ 2 * r) * Real.log ((1 + s) / (32 * α ^ 2))⌉₊

noncomputable def damp (α : ℝ) (K : ℕ) := 1 / (6 + 768 * α ^ 2 * K)

def physical (x : E) : QueryPlan E E E 1 := .ask x .done

noncomputable def solve (L α : ℝ) (m : ℕ) (y : E) :=
  let μ := L * α ^ 4
  RecursiveEnvelope.innerPlan physical (L + μ) μ (2 * α) y m (y, y)

noncomputable def center (k : ℕ) (x z : E) := RelativeErrorConvex.query (k, x, z)

noncomputable def outer (L α q : ℝ) (m : ℕ) : (n k : ℕ) → E → E →
    QueryPlan E E E ((1 * m) * n)
  | 0, _, x, _ => .done x
  | n+1, k, x, z =>
    let y := center k x z
    (solve L α m y).bind fun u =>
      outer L α q m n (k+1) u (z - (q * ((k : ℝ) + 1) / 2) • (y-u))

noncomputable def output (L α T : ℝ) (x0 : E) : Algorithm E E E :=
  let K := horizon α T
  QueryPlan.algorithm (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
    MeasureTheory.ProbabilityMeasure Unit) x0 x0 _ (fun _ =>
      outer L α (damp α K) (innerCount α) K 0 x0 x0)

end LongTails.Algorithms.TwoLevelRelativeErrorConvex
