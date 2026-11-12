import LongTails.Setups.RadiusCompositeGeneralizedSmooth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.RadiusCompositeAccelerated

open OracleTemplate
open LongTails.Setups.RadiusCompositeGeneralizedSmooth

structure Iterate (E : Type u) where
  weight : ℝ
  point : E
  momentum : E

structure Trial (E : Type u) where
  weight : ℝ
  gradient : E
  proximalPoint : E

inductive SearchPhase where
  | growing
  | refining (remaining : ℕ)

structure Search (E : Type u) where
  weight : ℝ
  lower : Option (Trial E)
  upper : ℝ
  phase : SearchPhase

inductive State (E : Type u) where
  | initial
  | initializeProx (gradient : E) (step weight : ℝ)
  | gradient (iterate : Iterate E) (search : Search E)
  | proximal (iterate : Iterate E) (search : Search E) (gradient : E)
  | finished (point : E)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def mix (A a : ℝ) (x v : E) : E :=
  (A / (A + a)) • x + (a / (A + a)) • v

noncomputable def targetWeight (p : Public) : ℝ := 4 * p.R ^ 2 / p.ε

noncomputable def restartFactor (p : Public) : ℝ := 128 * (1 + 4 * p.L1 * p.R)

noncomputable def refinementSteps (p : Public) : ℕ :=
  1 + ⌈Real.log (1000 * (1 + 4 * p.L1 * p.R)) / Real.log 2⌉₊

noncomputable def initialStep (p : Public) (g : p.E) : ℝ :=
  1 / ((p.L0 + p.L1 * ‖g‖) * Real.exp (p.L1 * p.R) + p.L0)

noncomputable def initialWeight (p : Public) (g : p.E) : ℝ :=
  1 / (8 * (p.L0 + p.L1 * ‖g‖) * Real.exp (4 * p.L1 * p.R))

noncomputable def beginSearch (s : Iterate E) (a : ℝ) : State E :=
  .gradient s ⟨a, none, 0, .growing⟩

noncomputable def accepts (p : Public) (s : Iterate p.E) (t : Trial p.E) : Prop :=
  t.weight ^ 2 * (p.L0 + p.L1 * ‖t.gradient‖) / (s.weight + t.weight) ≤ 1 / 32 ∧
    p.L1 * (t.weight / (s.weight + t.weight)) * ‖t.proximalPoint - s.momentum‖ ≤ 1 / 32

noncomputable def advance (s : Iterate E) (t : Trial E) : Iterate E :=
  ⟨s.weight + t.weight, mix s.weight t.weight s.point t.proximalPoint, t.proximalPoint⟩

noncomputable def commit (p : Public) (s : Iterate p.E) (t : Trial p.E) : State p.E := by
  classical
  let next := advance s t
  exact if targetWeight p ≤ next.weight then .finished next.point
    else beginSearch next (t.weight / restartFactor p)

noncomputable def refine (p : Public) (s : Iterate p.E) (lo : Trial p.E)
    (hi : ℝ) (remaining : ℕ) : State p.E :=
  .gradient s ⟨(lo.weight + hi) / 2, some lo, hi, .refining remaining⟩

noncomputable def finishTrial (p : Public) (s : Iterate p.E) (search : Search p.E)
    (g z : p.E) : State p.E := by
  classical
  let t : Trial p.E := ⟨search.weight, g, z⟩
  exact match search.phase with
  | .growing =>
      if accepts p s t then
        if s.weight ≤ t.weight then commit p s t
        else .gradient s ⟨min (2 * t.weight) s.weight, some t, 0, .growing⟩
      else match search.lower with
        | none => beginSearch s (t.weight / 2)
        | some lo => refine p s lo t.weight (refinementSteps p)
  | .refining remaining =>
      match search.lower with
      | none => beginSearch s (t.weight / 2)
      | some lo =>
          let nextLo := if accepts p s t then t else lo
          let nextHi := if accepts p s t then search.upper else t.weight
          if remaining ≤ 1 then commit p s nextLo
          else refine p s nextLo nextHi (remaining - 1)

noncomputable def query (p : Public) : State p.E → Query p
  | .initial => .gradient p.x0
  | .initializeProx g a _ => .prox a p.x0 g
  | .gradient s search => .gradient (mix s.weight search.weight s.point s.momentum)
  | .proximal s search g => .prox search.weight s.momentum g
  | .finished x => .gradient x

noncomputable def update (p : Public) : State p.E → p.E → State p.E := by
  classical
  exact fun state reply => match state with
  | .initial => .initializeProx reply (initialStep p reply) (initialWeight p reply)
  | .initializeProx _ _ A =>
      if targetWeight p ≤ A then .finished reply
      else beginSearch ⟨A, reply, reply⟩ (A / 16)
  | .gradient s search => .proximal s search reply
  | .proximal s search g => finishTrial p s search g reply
  | .finished x => .finished x

def output (p : Public) : State p.E → p.E
  | .initial => p.x0
  | .initializeProx _ _ _ => p.x0
  | .gradient s _ => s.point
  | .proximal s _ _ => s.point
  | .finished x => x

noncomputable def algorithm (p : Public) : Algorithm (Query p) p.E p.E 1 where
  State := State p.E
  initial := fun _ => .initial
  query := fun s => (0, query p s)
  update := update p
  output := output p

end LongTails.Algorithms.RadiusCompositeAccelerated
