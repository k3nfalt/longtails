import LongTails.Algorithms.GuardedMetricAcceleration
import LongTails.Algorithms.QueryPlan

namespace LongTails.Algorithms.QuarticMetricStage

open OracleTemplate GuardedMetricAcceleration
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

abbrev Reply (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  (ℝ × E) ⊕ (E →L[ℝ] E)

abbrev Plan (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Type) (n : ℕ) :=
  QueryPlan (Fin 2 × E) (Reply E) U n

structure Point (E : Type) where
  x : E
  value : ℝ
  gradient : E

structure Parameters (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  S : E ≃L[ℝ] E
  center : Point E
  α : ℝ
  μ : ℝ
  L : ℝ
  a : ℝ
  r : ℝ
  q : ℝ
  η : ℝ
  ε : ℝ

structure Plane (E : Type) where
  point : Point E
  previous : Point E
  accepted : Point E

structure State (E : Type) where
  previous : Point E
  accepted : Point E
  z : E
  history : List (Plane E)

structure Witness (E : Type) where
  point : Point E
  plane : Plane E

inductive Status (E : Type)
  | running (state : State E)
  | finished (point : Point E)
  | witness (data : Witness E)

def readPoint (x : E) : Reply E → Point E
  | .inl (fx, gx) => ⟨x, fx, gx⟩
  | .inr _ => ⟨x, 0, 0⟩

def value (p : Parameters E) (x : Point E) : ℝ := regularizedValue p.α p.center.x x.x x.value

def gradient (p : Parameters E) (x : Point E) : E :=
  regularizedGradient p.α p.center.x x.x x.gradient

def successful (p : Parameters E) (x : Point E) : Prop :=
  x.value ≤ p.center.value - p.q ∨ ‖x.gradient‖ ≤ p.ε

def supports (p : Parameters E) (u v : Point E) : Prop :=
  value p v + ⟪gradient p v, u.x - v.x⟫ + p.μ / 2 * ‖p.S (u.x - v.x)‖ ^ 2 ≤ value p u

def trialPoint (p : Parameters E) (y : Point E) : E :=
  let g := transformedGradient p.S (gradient p y)
  let t := min p.L⁻¹ (p.r / (2 * ‖g‖))
  y.x - p.S.symm (t • g)

def stopAfter (p : Parameters E) (status : Status E) : Plan E (Status E) 1 :=
  .ask (0, p.center.x) fun _ => .done status

def step (p : Parameters E) : Status E → Plan E (Status E) 2 := by
  classical
  intro status
  exact match status with
  | .finished x => .ask (0, p.center.x) fun _ => stopAfter p (.finished x)
  | .witness w => .ask (0, p.center.x) fun _ => stopAfter p (.witness w)
  | .running st =>
    let y := p.S.symm (extrapolate p.a (p.S st.accepted.x) st.z)
    .ask (0, y) fun reply =>
      let yp := readPoint y reply
      let plane := Plane.mk yp st.previous st.accepted
      if successful p yp then stopAfter p (.finished yp)
      else if ¬supports p p.center yp then stopAfter p (.witness ⟨p.center, plane⟩)
      else if ¬supports p st.accepted yp then stopAfter p (.witness ⟨st.accepted, plane⟩)
      else
        let next := trialPoint p yp
        .ask (0, next) fun reply =>
          let xp := readPoint next reply
          if successful p xp then .done (.finished xp)
          else .done (.running ⟨st.accepted, xp,
            centerStep p.a p.μ (p.S yp.x) st.z (transformedGradient p.S (gradient p yp)),
            plane :: st.history⟩)

def loop (p : Parameters E) : (n : ℕ) → Status E → Plan E (Status E) (2 * n)
  | 0, status => .done status
  | n + 1, status => by
    simpa only [Nat.mul_succ] using (step p status).bind (loop p n)

def certificate (p : Parameters E) : Status E → Plan E (Status E) 1 := by
  classical
  intro status
  exact match status with
  | .finished x => stopAfter p (.finished x)
  | .witness w => stopAfter p (.witness w)
  | .running st =>
    let w := trialPoint p st.accepted
    .ask (0, w) fun reply =>
      let wp := readPoint w reply
      if successful p wp then .done (.finished wp)
      else match st.history.find? (fun plane => ¬supports p wp plane.point) with
        | some plane => .done (.witness ⟨wp, plane⟩)
        | none => .done (.finished st.accepted)

def candidates (p : Parameters E) (w : Witness E) : Fin 6 → E :=
  ![(1 / 2 : ℝ) • (w.plane.accepted.x + w.plane.previous.x),
    (-2 : ℝ) • w.plane.accepted.x + (3 : ℝ) • w.plane.previous.x,
    escapePoints p.η w.point.x w.plane.point.x 0,
    escapePoints p.η w.point.x w.plane.point.x 1,
    escapePoints p.η w.point.x w.plane.point.x 2,
    escapePoints p.η w.point.x w.plane.point.x 3]

def better (x y : Point E) : Point E := if x.value ≤ y.value then x else y

def finish (p : Parameters E) : Status E → Plan E (Point E) 6
  | .finished x => (QueryPlan.traverse 6 (fun _ =>
      QueryPlan.ask (0, p.center.x) fun _ => .done ())).map (fun _ => x)
  | .running st => (QueryPlan.traverse 6 (fun _ =>
      QueryPlan.ask (0, p.center.x) fun _ => .done ())).map (fun _ => st.accepted)
  | .witness w => (QueryPlan.traverse 6 (fun i =>
      QueryPlan.ask (0, candidates p w i) fun reply => .done (readPoint (candidates p w i) reply))).map
        (fun points => points.foldl better w.point)

def plan (p : Parameters E) (n : ℕ) : Plan E (Point E) (2 * n + 7) :=
  let initial := Status.running (State.mk p.center p.center (p.S p.center.x) [])
  (show 6 + 1 + 2 * n = 2 * n + 7 by omega) ▸
    (loop p n initial).bind (fun status => (certificate p status).bind (finish p))


end

end LongTails.Algorithms.QuarticMetricStage
