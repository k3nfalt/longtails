import LongTails.Setups.CompositeGapSmooth
import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.CompositeGapAccelerated

open LongTails.Setups.CompositeGapSmooth

structure State (E : Type) where
  A : ℝ
  x : E
  z : E
  v : E

noncomputable def curvature (p : Params) (Δ : ℝ) : ℝ :=
  p.H0 + p.H1 * Δ + Δ / p.R ^ 2

noncomputable def scale (p : Params) (Δ : ℝ) : ℝ := curvature p Δ * p.R ^ 2 / Δ

noncomputable def fraction (p : Params) (Δ : ℝ) : ℝ :=
  1 / (128 * (1 + Real.sqrt (scale p Δ)))

noncomputable def target (p : Params) (Δ : ℝ) : ℝ := p.R ^ 2 / Δ

noncomputable def weight (p : Params) (Δ A : ℝ) : ℝ :=
  if A = 0 then 1 / (16 * curvature p Δ)
  else min (target p Δ - A) (A * fraction p Δ / (1 - fraction p Δ))

noncomputable def queryPoint (p : Params) (Δ : ℝ) (s : State p.E) : p.E :=
  (s.A / (s.A + weight p Δ s.A)) • s.x +
    (weight p Δ s.A / (s.A + weight p Δ s.A)) • s.z

noncomputable def initial {E : Type} [Zero E] (x : E) : State E := ⟨0, x, x, 0⟩

noncomputable def update (p : Params) (Δ : ℝ) (s : State p.E) (g z : p.E) : State p.E :=
  let a := weight p Δ s.A
  ⟨s.A + a, (s.A / (s.A + a)) • s.x + (a / (s.A + a)) • z,
    z, s.v + a • g⟩

noncomputable def stepPlan (p : Params) (Δ : ℝ) (x0 : p.E) (s : State p.E) :
    QueryPlan (Query p) p.E (State p.E) 2 :=
  if target p Δ ≤ s.A then
    .ask (.gradient s.x) (fun _ => .ask (.gradient s.x) (fun _ => .done s))
  else
    .ask (.gradient (queryPoint p Δ s)) (fun g =>
      let a := weight p Δ s.A
      .ask (.prox (s.A + a) x0 ((1 / (s.A + a)) • (s.v + a • g)))
        (fun z => .done (update p Δ s g z)))

noncomputable def phasePlan (p : Params) (Δ : ℝ) (x0 : p.E) :
    (N : ℕ) → State p.E → QueryPlan (Query p) p.E (State p.E) (2 * N)
  | 0, s => .done s
  | N + 1, s => (stepPlan p Δ x0 s).bind (phasePlan p Δ x0 N)

noncomputable def phasesPlan (p : Params) (N : ℕ) :
    (S : ℕ) → ℕ → p.E → QueryPlan (Query p) p.E p.E (2 * N * S)
  | 0, _, x => .done x
  | S + 1, k, x => (phasePlan p (p.Δ / 2 ^ k) x N (initial x)).bind
      (fun s => phasesPlan p N S (k + 1) s.x)

noncomputable def phaseIterations (p : Params) : ℕ :=
  ⌈256 * (1 + Real.sqrt (1 + 2 * p.H0 * p.R ^ 2 / p.ε + p.H1 * p.R ^ 2)) *
    Real.log (32 * (1 + 2 * p.H0 * p.R ^ 2 / p.ε + p.H1 * p.R ^ 2))⌉₊

noncomputable def phases (p : Params) : ℕ := ⌈Real.log (p.Δ / p.ε) / Real.log 2⌉₊

noncomputable def calls (p : Params) : ℕ := 2 * phaseIterations p * phases p

noncomputable def algorithm (p : Params) : Algorithm (Query p) p.E p.E :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ (.gradient p.x0) p.x0
    (calls p) (fun _ : Unit => phasesPlan p (phaseIterations p) (phases p) 0 p.x0)

noncomputable def output (p : Params) (O : Oracle (Query p) p.E)
    (ξ : (k : ℕ) → O.Seed k) : p.E :=
  execute O (algorithm p) (fun _ => calls p) () ξ

end OracleTemplate.CompositeGapAccelerated
