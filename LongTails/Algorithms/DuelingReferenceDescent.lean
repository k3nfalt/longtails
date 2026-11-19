import LongTails.Algorithms.AcceleratedTwoPointZerothOrderConvex
import LongTails.Algorithms.HeavyTailedFreshTape
import LongTails.Proofs.Clipping
import LongTails.Setups.StronglyConvexDueling
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory
open OracleTemplate
open LongTails.Setups.StronglyConvexDueling

namespace LongTails.Algorithms.DuelingReferenceDescent

abbrev Direction (d : ℕ) := Metric.sphere (0 : Point d) 1
abbrev Draw (d : ℕ) := Direction d × Fin 3
abbrev State (d : ℕ) := ℕ × Ball d × Ball d

noncomputable def retract {d : ℕ} (x : Point d) : Ball d :=
  ⟨clip 1 x, by simpa [Ball, Metric.mem_closedBall] using norm_clip_le (by norm_num : (0 : ℝ) ≤ 1) x⟩

noncomputable def axis (d : ℕ) [NeZero d] : Point d :=
  (EuclideanSpace.basisFun (Fin d) ℝ) 0

noncomputable def spacing (p : Params) : ℝ := 1 / max 1 (8 * p.G / p.r)

noncomputable def slope (p : Params) : ℝ :=
  p.c * (p.μ * spacing p ^ 2 / 4) ^ p.k / 3

noncomputable def radius (p : Params) : ℝ :=
  min (spacing p) (slope p * Real.sqrt (p.μ * p.ε) / (4 * p.M * p.L))

noncomputable def anchor (p : Params) (x : Point p.d) (j : Fin 3) : Point p.d :=
  let z := (1 - spacing p) • x
  if j = 0 then z else if j = 1 then z + spacing p • axis p.d else z - spacing p • axis p.d

noncomputable def query (p : Params) (s : State p.d) (a : Draw p.d) : Ball p.d × Ball p.d :=
  (retract ((1 - radius p) • (s.2.1 : Point p.d) + radius p • (a.1 : Point p.d)),
    retract (anchor p s.2.1 a.2))

noncomputable def estimate (p : Params) (a : Draw p.d) (b : Bool) : Point p.d :=
  ((p.d : ℝ) / radius p * score b) • (a.1 : Point p.d)

noncomputable def update (p : Params) (s : State p.d) (a : Draw p.d) (b : Bool) : State p.d :=
  let t := (s.1 : ℝ)
  let η := 4 / (slope p * p.μ * (t + 2))
  let x := (s.2.1 : Point p.d)
  let z := (s.2.2 : Point p.d)
  (s.1 + 1, retract (x - η • estimate p a b),
    retract ((t / (t + 2)) • z + (2 / (t + 2)) • x))

noncomputable def drawLaw (p : Params) : ProbabilityMeasure (Draw p.d) :=
  ⟨(ZerothOrder.sphereLaw (Point p.d) : Measure (Direction p.d)).prod
    (PMF.uniformOfFintype (Fin 3)).toMeasure, inferInstance⟩

noncomputable def algorithm (p : Params) :
    Algorithm (Ball p.d × Ball p.d) Bool (Ball p.d) :=
  HeavyTailedFreshTape.algorithm (⟨Measure.dirac (), inferInstance⟩ : ProbabilityMeasure Unit)
    (drawLaw p) (fun _ => (0, retract 0, retract 0)) (query p) (update p) (fun s => s.2.2)

noncomputable def output (p : Params) (O : Oracle (Ball p.d × Ball p.d) Bool) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) : Ball p.d :=
  execute O (algorithm p) (fun _ => K) seed ξ

end LongTails.Algorithms.DuelingReferenceDescent
