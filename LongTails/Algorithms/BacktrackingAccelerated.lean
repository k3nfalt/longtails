import LongTails.Setups.GeneralizedSmoothParameterFree
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.ParameterFreeGeneralized

open LongTails.Setups.GeneralizedSmoothParameterFree

structure Core (E : Type*) where
  A : ℝ
  x : E
  v : E
  h : ℝ

inductive State (E : Type*) where
  | ready (s : Core E)
  | probing (s : Core E) (y g : E)

noncomputable def stepWeight {E : Type*} (s : Core E) : ℝ :=
  (s.h + Real.sqrt (s.h ^ 2 + 4 * s.h * s.A)) / 2

noncomputable def trialPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Core E) : E :=
  (s.A / (s.A + stepWeight s)) • s.x + (stepWeight s / (s.A + stepWeight s)) • s.v

noncomputable def resolve {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Core E) (y g g' : E) : Core E := by
  classical
  exact
    if ‖g‖ ^ 2 / 2 ≤ ⟪g', g⟫ then
      ⟨s.A + stepWeight s, y - s.h • g, s.v - stepWeight s • g, 2 * s.h⟩
    else ⟨s.A, s.x, s.v, s.h / 2⟩

noncomputable def trial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (s : Core E) : Core E :=
  resolve s (trialPoint s) (g (trialPoint s)) (g (trialPoint s - s.h • g (trialPoint s)))

noncomputable def algorithm (p : Public) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := .ready ⟨0, p.x0, p.x0, p.h0⟩
  query := fun state => (0, match state with
    | .ready s => trialPoint s
    | .probing s y g => y - s.h • g)
  update
    | .ready s, g => .probing s (trialPoint s) g
    | .probing s y g, g' => .ready (resolve s y g g')
  output
    | .ready s => s.x
    | .probing s _ _ => s.x

end OracleTemplate.ParameterFreeGeneralized
