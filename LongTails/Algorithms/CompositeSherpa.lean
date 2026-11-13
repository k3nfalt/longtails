import LongTails.Setups.LipschitzCompositeGeneralizedSmooth
import LongTails.Algorithms.BacktrackingComposite

open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeSherpa

open LongTails.Setups.LipschitzCompositeGeneralizedSmooth

noncomputable def curv (L0 L1 M G : ℝ) : ℝ := L0 + 2 * L1 * M + L1 * G

noncomputable def phiFun (L0 L1 G : ℝ) : ℝ :=
  L0 / L1 ^ 2 * ((1 + L1 * G / L0) * Real.log (1 + L1 * G / L0) - L1 * G / L0)

noncomputable def cweight (L0 L1 M A G : ℝ) : ℝ :=
  let b := 1 / (12 * curv L0 L1 M G) + phiFun (L0 + L1 * M) L1 (G - M) / (2 * G ^ 2)
  (b + Real.sqrt (b ^ 2 + 4 * A / (12 * curv L0 L1 M G))) / 2

noncomputable def tol (L0 L1 M G : ℝ) : ℝ := G ^ 2 / (200 * curv L0 L1 M G)

noncomputable def gthr (L0 L1 M : ℝ) : ℝ := 5 * M + L0 / L1

structure Core (E : Type*) where
  A : ℝ
  x : E
  v : E

inductive Phase (E : Type*) where
  | queryPx (c : Core E)
  | queryGv (c : Core E) (px : ℝ)
  | queryPv (c : Core E) (px : ℝ) (gv : E)
  | probeG (c : Core E) (px tm tp pm : ℝ)
  | probeP (c : Core E) (px tm tp pm : ℝ) (gz : E)
  | proxX (c : Core E) (y gy : E)
  | proxV (c : Core E) (y gy xn : E)

inductive State (E : Type*) where
  | first (s : Phase E)
  | second (s : CompositeParameterFree.BtState E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def seg (c : Core E) (t : ℝ) : E := c.v + t • (c.x - c.v)

noncomputable def exitState (L0 L1 M : ℝ) (z : E) : State E :=
  .second ⟨0, z, z, 1 / (L0 + L1 * M), 0, 0, z⟩

noncomputable def acceptCore (L0 L1 M : ℝ) (c : Core E) (gy xn vn : E) : Core E :=
  ⟨c.A + cweight L0 L1 M c.A ‖gy‖, xn, vn⟩

noncomputable def stepGv (L0 L1 M : ℝ) (c : Core E) (px : ℝ) (gv : E) : State E := by
  classical
  exact if ‖gv‖ ≤ gthr L0 L1 M then exitState L0 L1 M c.v else .first (.queryPv c px gv)

noncomputable def stepPv (L0 L1 M : ℝ) (c : Core E) (px : ℝ) (gv : E) (pv : ℝ) : State E := by
  classical
  exact if -tol L0 L1 M ‖gv‖ ≤ ⟪gv, c.x - c.v⟫ + px - pv then .first (.proxX c c.v gv)
    else .first (.probeG c px 0 1 pv)

noncomputable def stepProbeG (L0 L1 M : ℝ) (c : Core E) (px tm tp pm : ℝ) (gz : E) :
    State E := by
  classical
  exact if ‖gz‖ ≤ gthr L0 L1 M then exitState L0 L1 M (seg c ((tm + tp) / 2))
    else .first (.probeP c px tm tp pm gz)

noncomputable def stepProbeP (L0 L1 M : ℝ) (c : Core E) (px tm tp pm : ℝ) (gz : E) (pz : ℝ) :
    State E := by
  classical
  exact
    let t := (tm + tp) / 2
    if (1 - t) * ⟪gz, c.x - c.v⟫ + px - pz < -tol L0 L1 M ‖gz‖ then
      .first (.probeG c px t tp pz)
    else if tol L0 L1 M ‖gz‖ < t * (⟪gz, c.x - c.v⟫ + (pz - pm) / (t - tm)) then
      .first (.probeG c px tm t pm)
    else .first (.proxX c (seg c t) gz)

noncomputable def phaseQuery (p : Public) (s : Phase p.E) : Query p :=
  match s with
  | .queryPx c => .value c.x
  | .queryGv c _ => .gradient c.v
  | .queryPv c _ _ => .value c.v
  | .probeG c _ tm tp _ => .gradient (seg c ((tm + tp) / 2))
  | .probeP c _ tm tp _ _ => .value (seg c ((tm + tp) / 2))
  | .proxX _ y gy => .prox (1 / (4 * curv p.L0 p.L1 p.M ‖gy‖)) y gy
  | .proxV c _ gy _ => .prox (cweight p.L0 p.L1 p.M c.A ‖gy‖) c.v gy

noncomputable def phaseUpdate (p : Public) (s : Phase p.E) (r : Reply p) : State p.E :=
  match s, r with
  | .queryPx c, .scalar px => .first (.queryGv c px)
  | .queryGv c px, .vector gv => stepGv p.L0 p.L1 p.M c px gv
  | .queryPv c px gv, .scalar pv => stepPv p.L0 p.L1 p.M c px gv pv
  | .probeG c px tm tp pm, .vector gz => stepProbeG p.L0 p.L1 p.M c px tm tp pm gz
  | .probeP c px tm tp pm gz, .scalar pz => stepProbeP p.L0 p.L1 p.M c px tm tp pm gz pz
  | .proxX c y gy, .vector xn => .first (.proxV c y gy xn)
  | .proxV c _ gy xn, .vector vn => .first (.queryPx (acceptCore p.L0 p.L1 p.M c gy xn vn))
  | s, _ => .first s

noncomputable def secondQuery (p : Public) (s : CompositeParameterFree.BtState p.E) : Query p :=
  if s.phase = 0 then
    .gradient (CompositeGeneralized.mixPoint s.A (CompositeParameterFree.stepWeight s.h s.A) s.x s.z)
  else if s.phase = 1 then .prox (CompositeParameterFree.stepWeight s.h s.A) s.z s.gy
  else .gradient (CompositeGeneralized.mixPoint s.A (CompositeParameterFree.stepWeight s.h s.A) s.x s.p)

noncomputable def secondUpdate (p : Public) (s : CompositeParameterFree.BtState p.E) (r : Reply p) :
    CompositeParameterFree.BtState p.E :=
  match r with
  | .scalar _ => s
  | .vector r =>
    if s.phase = 0 then { s with phase := 1, gy := r }
    else if s.phase = 1 then { s with phase := 2, p := r }
    else
      let a := CompositeParameterFree.stepWeight s.h s.A
      let y := CompositeGeneralized.mixPoint s.A a s.x s.z
      let x' := CompositeGeneralized.mixPoint s.A a s.x s.p
      if 2 * s.h * ⟪r - s.gy, x' - y⟫ ≤ ‖x' - y‖ ^ 2 then
        ⟨s.A + a, x', s.p, 2 * s.h, 0, s.gy, s.p⟩
      else ⟨s.A, s.x, s.z, s.h / 2, 0, s.gy, s.p⟩

noncomputable def stateQuery (p : Public) (s : State p.E) : Query p :=
  match s with
  | .first s => phaseQuery p s
  | .second s => secondQuery p s

noncomputable def stateUpdate (p : Public) (s : State p.E) (r : Reply p) : State p.E :=
  match s with
  | .first s => phaseUpdate p s r
  | .second s => .second (secondUpdate p s r)

noncomputable def stateOutput (s : State E) : E :=
  match s with
  | .first (.queryPx c) => c.x
  | .first (.queryGv c _) => c.x
  | .first (.queryPv c _ _) => c.x
  | .first (.probeG c _ _ _ _) => c.x
  | .first (.probeP c _ _ _ _ _) => c.x
  | .first (.proxX c _ _) => c.x
  | .first (.proxV c _ _ _) => c.x
  | .second s => s.x

noncomputable def algorithm (p : Public) : Algorithm (Query p) (Reply p) p.E where
  State := State p.E
  initial _ := .first (.queryPx ⟨0, p.x0, p.x0⟩)
  query := fun s => (0, stateQuery p s)
  update := stateUpdate p
  output := stateOutput

end OracleTemplate.CompositeSherpa
