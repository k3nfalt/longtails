import LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex
import LongTails.Algorithms.BacktrackingAccelerated

open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

open LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex

noncomputable def localCurvature (L0 L1 : ℝ) (g : ℝ) : ℝ := L0 + L1 * g

noncomputable def phiRatio (L0 L1 : ℝ) (G : ℝ) : ℝ :=
  L0 / L1 ^ 2 * ((1 + L1 * G / L0) * Real.log (1 + L1 * G / L0) - L1 * G / L0) / G ^ 2

noncomputable def weight (L0 L1 : ℝ) (A : ℝ) (G : ℝ) : ℝ :=
  let b := 1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G
  (b + Real.sqrt (b ^ 2 + 4 * A / (7 * localCurvature L0 L1 G))) / 2

structure Core (E : Type*) where
  A : ℝ
  x : E
  v : E

inductive Phase (E : Type*) where
  | queryX (c : Core E)
  | queryV (c : Core E) (gx : E)
  | probe (c : Core E) (gx gv : E) (tm tp : ℝ)

inductive State (E : Type*) where
  | first (s : Phase E)
  | second (s : ParameterFreeGeneralized.State E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def threshold (L0 L1 : ℝ) : ℝ := L0 / (4 * L1)

noncomputable def accept (L0 L1 : ℝ) (c : Core E) (y gy : E) : Phase E :=
  let L := localCurvature L0 L1 ‖gy‖
  let a := weight L0 L1 c.A ‖gy‖
  .queryX ⟨c.A + a, y - (1 / (4 * L)) • gy, c.v - a • gy⟩

noncomputable def exitState (L0 : ℝ) (z : E) : State E :=
  .second (.ready ⟨0, z, z, 1 / L0⟩)

noncomputable def probePoint (c : Core E) (tm tp : ℝ) : E :=
  c.v + ((tm + tp) / 2) • (c.x - c.v)

noncomputable def stepX (L0 L1 : ℝ) (c : Core E) (gx : E) : State E := by
  classical
  exact if ‖gx‖ ≤ threshold L0 L1 then exitState L0 c.x else .first (.queryV c gx)

noncomputable def stepV (L0 L1 : ℝ) (c : Core E) (gx gv : E) : State E := by
  classical
  exact
    if ‖gv‖ ≤ threshold L0 L1 then exitState L0 c.v
    else if 0 ≤ ⟪gv, c.x - c.v⟫ then .first (accept L0 L1 c c.v gv)
    else if ⟪gx, c.x - c.v⟫ ≤ ‖gx‖ ^ 2 / (16 * localCurvature L0 L1 ‖gx‖) then
      .first (accept L0 L1 c c.x gx)
    else .first (.probe c gx gv 0 1)

noncomputable def stepProbe (L0 L1 : ℝ) (c : Core E) (gx gv : E) (tm tp : ℝ) (gz : E) :
    State E := by
  classical
  exact
    let t := (tm + tp) / 2
    if ‖gz‖ ≤ threshold L0 L1 then exitState L0 (probePoint c tm tp)
    else if ⟪gz, c.x - c.v⟫ < 0 then .first (.probe c gx gv t tp)
    else if t * ⟪gz, c.x - c.v⟫ ≤ ‖gz‖ ^ 2 / (16 * localCurvature L0 L1 ‖gz‖) then
      .first (accept L0 L1 c (probePoint c tm tp) gz)
    else .first (.probe c gx gv tm t)

noncomputable def phaseQuery (s : Phase E) : E :=
  match s with
  | .queryX c => c.x
  | .queryV c _ => c.v
  | .probe c _ _ tm tp => probePoint c tm tp

noncomputable def phaseUpdate (L0 L1 : ℝ) (s : Phase E) (g : E) : State E :=
  match s with
  | .queryX c => stepX L0 L1 c g
  | .queryV c gx => stepV L0 L1 c gx g
  | .probe c gx gv tm tp => stepProbe L0 L1 c gx gv tm tp g

noncomputable def secondQuery (s : ParameterFreeGeneralized.State E) : E :=
  match s with
  | .ready s => ParameterFreeGeneralized.trialPoint s
  | .probing s y g => y - s.h • g

noncomputable def secondUpdate (s : ParameterFreeGeneralized.State E) (g : E) :
    ParameterFreeGeneralized.State E :=
  match s with
  | .ready s => .probing s (ParameterFreeGeneralized.trialPoint s) g
  | .probing s y g₀ => .ready (ParameterFreeGeneralized.resolve s y g₀ g)

noncomputable def stateQuery (s : State E) : E :=
  match s with
  | .first s => phaseQuery s
  | .second s => secondQuery s

noncomputable def stateUpdate (L0 L1 : ℝ) (s : State E) (g : E) : State E :=
  match s with
  | .first s => phaseUpdate L0 L1 s g
  | .second s => .second (secondUpdate s g)

noncomputable def stateOutput (s : State E) : E :=
  match s with
  | .first (.queryX c) => c.x
  | .first (.queryV c _) => c.x
  | .first (.probe c _ _ _ _) => c.x
  | .second (.ready s) => s.x
  | .second (.probing s _ _) => s.x

noncomputable def algorithm (p : Public) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := .first (.queryX ⟨0, p.x0, p.x0⟩)
  query := fun s => (0, stateQuery s)
  update := stateUpdate p.L0 p.L1
  output := stateOutput

end OracleTemplate.RadiusFreeSherpa
