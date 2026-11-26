import LongTails.Algorithms.CompositeGapAccelerated
import LongTails.Algorithms.CompositeGeneralizedAccelerated

namespace OracleTemplate.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth

noncomputable def mass (M : ℝ) (n : ℕ) : ℝ := n * (n + 1 : ℝ) / (256 * M)

noncomputable def increment (M : ℝ) (n : ℕ) : ℝ := (n + 1 : ℝ) / (128 * M)

structure State (E : Type) where
  x : E
  z : E
  v : E

noncomputable def step (p : Params) (M : ℝ) (c : p.E) (n : ℕ) (q : State p.E) :
    QueryPlan (Query p) p.E (State p.E) 2 :=
  let A := mass M n
  let a := increment M n
  .ask (.gradient (CompositeGeneralized.mixPoint A a q.x q.z)) (fun g =>
    let v := q.v + a • g
    .ask (.prox (A + a) c ((1 / (A + a)) • v)) (fun z =>
      .done ⟨CompositeGeneralized.mixPoint A a q.x z, z, v⟩))

noncomputable def phase (p : Params) (M : ℝ) (c : p.E) :
    (n : ℕ) → QueryPlan (Query p) p.E (State p.E) (2 * n)
  | 0 => .done ⟨c, c, 0⟩
  | n + 1 => (show 2 + 2 * n = 2 * (n + 1) by omega) ▸ (phase p M c n).bind (step p M c n)

noncomputable def level (p : Params) (k : ℕ) : ℝ := p.Δ / 2 ^ k

noncomputable def curvature (p : Params) (d : ℝ) : ℝ :=
  p.H0 + p.H1 * d + d / (2 * p.R ^ 2)

noncomputable def scale (p : Params) (d : ℝ) : ℝ := curvature p d * p.R ^ 2 / d

noncomputable def iterations (p : Params) (k : ℕ) : ℕ :=
  ⌈16 * Real.sqrt (scale p (level p k))⌉₊

noncomputable def cost (p : Params) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * iterations p k + cost p k

noncomputable def stages (p : Params) : (k : ℕ) → QueryPlan (Query p) p.E p.E (cost p k)
  | 0 => .done p.x0
  | k + 1 => (stages p k).bind fun c =>
      (phase p (curvature p (level p k)) c (iterations p k)).map State.x

noncomputable def algorithm (p : Params) : Algorithm (Query p) p.E p.E :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ (.gradient p.x0) p.x0
    (cost p (CompositeGapAccelerated.phases p))
    (fun _ : Unit => stages p (CompositeGapAccelerated.phases p))

end OracleTemplate.CompositeGapQuadraticWeights
