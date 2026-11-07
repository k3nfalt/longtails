import LongTails.Setups.ThirdDerivativeSmoothNonconvex
import LongTails.Algorithms.EnergyHessianReuse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace LongTails.Algorithms.LogFreeProxNewton

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open scoped RealInnerProductSpace

noncomputable section

abbrev Reply (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  (ℝ × E) ⊕ (E →L[ℝ] E)

abbrev Plan (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Type) (n : ℕ) :=
  QueryPlan (Fin 2 × E) (Reply E) U n

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scale (p : Params) : ℝ := (p.ε / p.L₃) ^ (1 / 3 : ℝ)
def unit (p : Params) : ℝ := p.ε * scale p
def weight (p : Params) : ℝ := 256 * p.L₃ * scale p ^ 2
def threshold (p : Params) : ℝ := unit p / 4096
def tailLevel (p : Params) : ℝ := unit p / 2 ^ 20
def tolerance (j : ℕ) : ℝ := 1 / 2 ^ (j + 4)

structure Data (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  x : E
  value : ℝ
  grad : E
  hess : E →L[ℝ] E

structure State (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  center : E
  centerValue : ℝ
  cur : Data E
  tail : Bool
  level : ℕ
  done : Bool
  out : E

def readValue : Reply E → ℝ × E
  | .inl a => a
  | .inr _ => (0, 0)

def readHessian : Reply E → (E →L[ℝ] E)
  | .inl _ => 0
  | .inr H => H

def system (γ : ℝ) (d : Data E) : E →L[ℝ] E := d.hess + γ • ContinuousLinearMap.id ℝ E

def residual (γ : ℝ) (c : E) (d : Data E) : E := d.grad + γ • (d.x - c)

def direction (γ : ℝ) (c : E) (d : Data E) : E := by
  classical
  exact if h : ∃ v, system γ d v = -residual γ c d then h.choose else 0

def decrement (γ : ℝ) (c : E) (d : Data E) : ℝ := -⟪residual γ c d, direction γ c d⟫

def regularized (γ : ℝ) (c x : E) (v : ℝ) : ℝ := v + γ / 2 * ‖x - c‖ ^ 2

def curvature (γ : ℝ) (d : Data E) : Option E := by
  classical
  exact if h : ∃ v, ‖v‖ = 1 ∧ ⟪d.hess v, v⟫ ≤ -(γ / 4) then some h.choose else none

def stable (γ ζ : ℝ) (d : Data E) (H : E →L[ℝ] E) : Prop :=
  ∀ v, |⟪(H - d.hess) v, v⟫| ≤ ζ * ⟪system γ d v, v⟫

def witness (γ ζ : ℝ) (d : Data E) (H : E →L[ℝ] E) : E := by
  classical
  exact if h : ∃ v, ⟪system γ d v, v⟫ = 1 ∧ ζ < |⟪(H - d.hess) v, v⟫| then h.choose else 0

def stepLength (p : Params) (c : E) (d : Data E) : ℝ :=
  min 1 (scale p / ‖direction (weight p) c d‖)

def grid : Fin 5 → ℝ := ![1, 1 / 2, 1 / 4, 1 / 8, -1]

inductive Mode
  | idle
  | stop
  | success
  | escape
  | enter
  | newton
  | advance
  | magnify

def mode (p : Params) (st : State E) (H : E →L[ℝ] E) : Mode := by
  classical
  exact if st.done then .idle
    else if ‖st.cur.grad‖ ≤ p.ε then .stop
    else if st.tail then
      (if stable (weight p) (tolerance st.level) st.cur H then .advance else .magnify)
    else if st.cur.value ≤ st.centerValue - threshold p then .success
    else if (curvature (weight p) st.cur).isSome then .escape
    else if decrement (weight p) st.center st.cur ≤ tailLevel p then .enter
    else .newton

def probe (p : Params) (st : State E) : E :=
  if st.tail then st.cur.x + direction (weight p) st.center st.cur else st.cur.x

def magnifier (p : Params) (st : State E) : ℝ :=
  8 * Real.sqrt (unit p / decrement (weight p) st.center st.cur)

def orientation (p : Params) (st : State E) (H : E →L[ℝ] E) : ℝ :=
  if 0 ≤ ⟪(H - st.cur.hess) (witness (weight p) (tolerance st.level) st.cur H),
    witness (weight p) (tolerance st.level) st.cur H⟫ then 1 else -1

def candidates (p : Params) (st : State E) (H : E →L[ℝ] E) : Fin 5 → E := by
  classical
  exact
    let y := st.cur.x
    let d := direction (weight p) st.center st.cur
    match mode p st H with
    | .escape =>
        let v := (curvature (weight p) st.cur).getD 0
        ![y + scale p • v, y - scale p • v, y + scale p • v, y + scale p • v, y + scale p • v]
    | .newton => fun i => y + (grid i * stepLength p st.center st.cur) • d
    | .magnify =>
        let w := witness (weight p) (tolerance st.level) st.cur H
        let σ := orientation p st H
        let s := magnifier p st
        let z := y - (σ * s) • d
        let e := ‖w‖⁻¹ • w
        ![z + scale p • e, z - scale p • e, y + (σ * s) • d, y + (σ * s) • d, y + (σ * s) • d]
    | _ => fun _ => y

def key (p : Params) (st : State E) (H : E →L[ℝ] E) (x : E) (v : ℝ) : ℝ :=
  match mode p st H with
  | .newton => regularized (weight p) st.center x v
  | _ => v

def pick (k : Fin 5 → ℝ) (a b : Fin 5) : Fin 5 := if k a ≤ k b then a else b

def choose (p : Params) (st : State E) (H : E →L[ℝ] E) (vals : Fin 5 → ℝ × E) : Fin 5 :=
  let k := fun i => key p st H (candidates p st H i) (vals i).1
  pick k (pick k (pick k (pick k 0 1) 2) 3) 4

def landing (p : Params) (st : State E) (H : E →L[ℝ] E) (vals : Fin 5 → ℝ × E) : E :=
  candidates p st H (choose p st H vals)

def next (p : Params) (st : State E) (probeValue : ℝ × E) (H : E →L[ℝ] E)
    (vals : Fin 5 → ℝ × E) (H' : E →L[ℝ] E) : State E :=
  let i := choose p st H vals
  let moved : Data E := ⟨candidates p st H i, (vals i).1, (vals i).2, H'⟩
  match mode p st H with
  | .idle => st
  | .stop => { st with done := true, out := st.cur.x }
  | .success => { st with center := st.cur.x, centerValue := st.cur.value }
  | .escape => { st with center := moved.x, centerValue := moved.value, cur := moved }
  | .enter => { st with tail := true, level := 0 }
  | .newton => { st with cur := moved }
  | .advance =>
      { st with
        cur := ⟨probe p st, probeValue.1, probeValue.2, H⟩
        level := st.level + 1 }
  | .magnify =>
      { st with
        center := moved.x
        centerValue := moved.value
        cur := moved
        tail := false
        level := 0 }

def step (p : Params) (st : State p.E) : Plan p.E (State p.E) 8 :=
  .ask (0, probe p st) fun a =>
  .ask (1, probe p st) fun b =>
  let H := readHessian b
  let cs := candidates p st H
  .ask (0, cs 0) fun c0 =>
  .ask (0, cs 1) fun c1 =>
  .ask (0, cs 2) fun c2 =>
  .ask (0, cs 3) fun c3 =>
  .ask (0, cs 4) fun c4 =>
  let vals : Fin 5 → ℝ × p.E := ![readValue c0, readValue c1, readValue c2, readValue c3,
    readValue c4]
  .ask (1, landing p st H vals) fun h =>
  .done (next p st (readValue a) H vals (readHessian h))

def loop (p : Params) : (n : ℕ) → State p.E → Plan p.E (State p.E) (8 * n)
  | 0, st => .done st
  | n + 1, st => by
    simpa only [Nat.mul_succ] using QueryPlan.bind (step p st) (loop p n)

def logArgument (p : Params) : ℝ := 2 + p.H₀ * p.Δ / p.ε ^ 2 + p.L₃ * p.Δ ^ 3 / p.ε ^ 4

def complexity (p : Params) : ℝ := p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ)

def steps (p : Params) : ℕ := ⌈2 ^ 27 * (1 + complexity p + Real.log (logArgument p))⌉₊

def initial (p : Params) (a : Reply p.E) (b : Reply p.E) : State p.E :=
  ⟨p.x0, (readValue a).1, ⟨p.x0, (readValue a).1, (readValue a).2, readHessian b⟩, false, 0,
    false, p.x0⟩

def finish (st : State E) : E := if st.done then st.out else st.cur.x

def plan (p : Params) : Plan p.E p.E (8 * steps p + 2) :=
  .ask (0, p.x0) fun a =>
  .ask (1, p.x0) fun b =>
  QueryPlan.map finish (loop p (steps p) (initial p a b))

def algorithm (p : Params) : Algorithm p.E (Reply p.E) p.E 2 :=
  EnergyHessianReuse.channelAlgorithm (0, p.x0) p.x0 (plan p)

end

end LongTails.Algorithms.LogFreeProxNewton
