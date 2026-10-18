import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def aNext (lam A : ℝ) : ℝ := (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2

noncomputable def mixPt (lam A : ℝ) (y z : E) : E :=
  (A / (A + aNext lam A)) • y + (aNext lam A / (A + aNext lam A)) • z

noncomputable def stormPlan (lam eta a : ℝ) (xt : E) (S : ℕ) :
    (m : ℕ) → E → E → E → ℕ → QueryPlan (E × E) (E × E) E m
  | 0, _, _, sel, _ => .done sel
  | m + 1, x, d, sel, t => .ask (x - eta • d, x) fun r =>
      stormPlan lam eta a xt S m (x - eta • d)
        (r.1 + (1 / lam) • (x - eta • d - xt) + (1 - a) • (d - (r.2 + (1 / lam) • (x - xt))))
        (if t + 1 = S then x - eta • d else sel) (t + 1)

noncomputable def innerPlan (lam eta a : ℝ) (L : ℕ) (xt : E) (S : ℕ) :
    QueryPlan (E × E) (E × E) E (L + 1) :=
  .ask (xt, xt) fun r => stormPlan lam eta a xt S L xt r.1 xt 0

noncomputable def batchPlan (y : E) : (m : ℕ) → E → QueryPlan (E × E) (E × E) E m
  | 0, acc => .done acc
  | m + 1, acc => .ask (y, y) fun r => batchPlan y m (acc + r.1)

noncomputable def blockPlan (lam eta a : ℝ) (L B : ℕ) (S : ℕ) (o : ℝ × E × E) :
    QueryPlan (E × E) (E × E) (ℝ × E × E) (B + (L + 1)) :=
  (innerPlan lam eta a L (mixPt lam o.1 o.2.1 o.2.2) S).bind fun y =>
    (batchPlan y B 0).map fun s => (o.1 + aNext lam o.1, y, o.2.2 - (aNext lam o.1 / B) • s)

noncomputable def fullPlan (lam eta a : ℝ) (L B T0 : ℕ) (τ : ℕ → ℕ) :
    (K : ℕ) → ℝ × E × E → ℕ → QueryPlan (E × E) (E × E) (ℝ × E × E) ((B + (L + 1)) * K)
  | 0, o, _ => .done o
  | K + 1, o, k => (blockPlan lam eta a L B (T0 + τ k) o).bind fun o' =>
      fullPlan lam eta a L B T0 τ K o' (k + 1)

noncomputable def seedIndex {K W : ℕ} (σ : Fin K → Fin W) (i : ℕ) : ℕ :=
  if h : i < K then (σ ⟨i, h⟩).val else 0

noncomputable def proximalStorm (lam eta a : ℝ) (T0 Wm B K : ℕ) (x0 : E) :
    Algorithm (E × E) (E × E) E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Fin K → Fin (Wm + 1))).toMeasure, inferInstance⟩
    (x0, x0) x0 ((B + (T0 + Wm + 1)) * K) fun σ =>
      (fullPlan lam eta a (T0 + Wm) B T0 (seedIndex σ) K (0, x0, x0) 0).map fun o => o.2.1

end OracleTemplate.ProximalStorm
