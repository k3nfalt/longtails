import LongTails.Algorithms.ProjectedClippedExtragradient
import Mathlib.Data.Nat.Log

namespace OracleTemplate.StochasticQuasar

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def innerRadius (D : ℝ) (j : ℕ) : ℝ := D / (2 : ℝ) ^ (j + 1)

noncomputable def innerBatch (L σ D : ℝ) (j : ℕ) : ℕ :=
  max 1 ⌈σ ^ 2 / (L ^ 2 * innerRadius D j ^ 2)⌉₊

noncomputable def innerStepPlan (L : ℝ) (c x : E) (b : ℕ) :
    QueryPlan (Fin 2 × E) E E (1 + b) :=
  (ProjectedClippedExtragradient.meanPlan b x).bind fun raw =>
    .ask (1, x - (1 / (3 * L)) • (raw + (2 * L) • (x - c))) fun y => .done y

noncomputable def innerStageCalls (L σ D : ℝ) (j : ℕ) : ℕ :=
  (1 + innerBatch L σ D j) * 2

noncomputable def innerCalls (L σ D : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => innerStageCalls L σ D j + innerCalls L σ D j

noncomputable def innerPlan (L σ D : ℝ) (c x0 : E) :
    (j : ℕ) → QueryPlan (Fin 2 × E) E E (innerCalls L σ D j)
  | 0 => .done x0
  | j + 1 => (innerPlan L σ D c x0 j).bind fun x =>
      ProjectedClippedExtragradient.repeatPlan
        (fun y => innerStepPlan L c y (innerBatch L σ D j)) 2 x

noncomputable def innerStageCount (D r : ℝ) : ℕ := Nat.clog 2 ⌈D / r⌉₊

noncomputable def approximationPlan (L σ D r : ℝ) (c x0 : E) :
    QueryPlan (Fin 2 × E) E E (innerCalls L σ D (innerStageCount D r)) :=
  innerPlan L σ D c x0 (innerStageCount D r)

end OracleTemplate.StochasticQuasar
