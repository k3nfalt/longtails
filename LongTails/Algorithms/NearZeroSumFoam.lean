import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import LongTails.Setups.NearZeroSumGames

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

abbrev Joint (E F : Type*) := WithLp 2 (E × F)

structure FoamConfig where
  a : ℝ
  b : ℝ
  α : ℝ
  L : ℝ
  η : ℝ
  innerSteps : ℕ
  outerSteps : ℕ

structure FoamState (E F : Type*) where
  z : E
  y : F
  xf : E
  zf : E
  yf : F

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def eagAnchor (u0 u : E) (k : ℕ) : E :=
  u0 + ((k : ℝ) / (k + 1)) • (u - u0)

noncomputable def eagIterate (P A : E → E) (u0 : E) : ℕ → E
  | 0 => u0
  | k + 1 =>
    let u := eagIterate P A u0 k
    let b := eagAnchor u0 u k
    P (b - A (P (b - A u)))

noncomputable def eagNormal (P A : E → E) (u0 : E) : ℕ → E
  | 0 => 0
  | k + 1 =>
    let u := eagIterate P A u0 k
    let b := eagAnchor u0 u k
    b - A (P (b - A u)) - eagIterate P A u0 (k + 1)

def pair (x : E) (y : F) : Joint E F := WithLp.toLp 2 (x, y)

def repeatQueries {Q R S : Type*} {c : ℕ} (step : S → QueryPlan Q R S c) :
    (n : ℕ) → S → QueryPlan Q R S (c * n)
  | 0, s => .done s
  | n + 1, s => (step s).bind (repeatQueries step n)

noncomputable def fieldQuery (β : ℝ) (center u : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) 1 :=
  .ask (.inl u) (fun f => .done (f + β • (u - center)))

def projectionQuery (u : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) 1 :=
  .ask (.inr u) .done

noncomputable def innerFieldQuery (cfg : FoamConfig) (β : ℝ)
    (center : Joint E F) (zg : E) (yg : F) (u : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) 1 :=
  (fieldQuery β center u).map fun f =>
    pair (f.fst - (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • zg)
      (f.snd + (cfg.a / 8) • (u.snd - yg))

structure InnerState (E F : Type*) where
  index : ℕ
  point : Joint E F
  normal : Joint E F

noncomputable def innerEagStep (cfg : FoamConfig) (β : ℝ)
    (center : Joint E F) (zg : E) (yg : F) (u0 : Joint E F) (st : InnerState E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (InnerState E F) 4 :=
  let t := 1 / (st.index + 1 : ℝ)
  let anchor := t • u0 + (1 - t) • st.point
  (innerFieldQuery cfg β center zg yg st.point).bind fun au =>
    (projectionQuery (anchor - cfg.η • au)).bind fun v =>
      (innerFieldQuery cfg β center zg yg v).bind fun av =>
        (projectionQuery (anchor - cfg.η • av)).map fun unew =>
          { index := st.index + 1, point := unew,
            normal := (1 / cfg.η) • (anchor - unew) - av }

def foamStepCalls (cfg : FoamConfig) : ℕ := 1 + 4 * cfg.innerSteps + 1

noncomputable def foamStep (cfg : FoamConfig) (β : ℝ) (center : Joint E F)
    (s : FoamState E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (FoamState E F) (foamStepCalls cfg) :=
  let zg := cfg.α • s.z + (1 - cfg.α) • s.zf
  let yg := cfg.α • s.y + (1 - cfg.α) • s.yf
  (projectionQuery (pair ((-1 / cfg.a) • zg) yg)).bind fun u0 =>
    (repeatQueries (innerEagStep cfg β center zg yg u0) cfg.innerSteps ⟨0, u0, 0⟩).bind fun un =>
      (fieldQuery β center un.point).map fun f =>
        let xf := un.point.fst
        let yf := un.point.snd
        let zf := f.fst - cfg.a • xf + un.normal.fst
        let wf := f.snd - cfg.b • yf + un.normal.snd
        { z := (1 / 2 : ℝ) • s.z - (cfg.a / 2) • xf
          y := (1 - cfg.α / 2) • s.y - (cfg.α / (2 * cfg.b)) • wf
          xf := xf, zf := zf, yf := yf }

noncomputable def foamInitial (cfg : FoamConfig) (β : ℝ) (center u0 : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (FoamState E F) 3 :=
  (fieldQuery β center u0).bind fun f0 =>
    (projectionQuery (u0 - (1 / cfg.L) • f0)).bind fun u1 =>
      (fieldQuery β center u1).map fun f1 =>
        let w := f1 + cfg.L • (u0 - u1) - f0
        let z := w.fst - cfg.a • u1.fst
        { z := z, y := u1.snd, xf := u1.fst, zf := z, yf := u1.snd }

def foamCalls (cfg : FoamConfig) : ℕ := 1 + foamStepCalls cfg * cfg.outerSteps + 3

noncomputable def foamPlan (cfg : FoamConfig) (β : ℝ) (center u0 : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) (foamCalls cfg) :=
  (foamInitial cfg β center u0).bind fun s0 =>
    (repeatQueries (foamStep cfg β center) cfg.outerSteps s0).bind fun s =>
      projectionQuery (pair ((-1 / cfg.a) • s.z) s.y)

noncomputable def proximalFoamPlan (cfg : FoamConfig) (β : ℝ) (N : ℕ) (u0 : Joint E F) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) (foamCalls cfg * N) :=
  repeatQueries (fun u => foamPlan cfg β u u) N u0

noncomputable def proximalFoam (cfg : FoamConfig) (β : ℝ) (N : ℕ) (u0 : Joint E F) :
    Algorithm (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (.inl u0) u0 (foamCalls cfg * N) (fun _ => proximalFoamPlan cfg β N u0)


def transportPlan {Q R U Q' R' U' : Type*} (query : Q' → Q) (reply : R → R')
    (output : U' → U) : {k : ℕ} → QueryPlan Q' R' U' k → QueryPlan Q R U k
  | _, .done u => .done (output u)
  | _, .ask q next => .ask (query q) (fun r => transportPlan query reply output (next (reply r)))

def swapPoint (u : Joint E F) : Joint F E := WithLp.toLp 2 (u.snd, u.fst)

noncomputable def orientedProximalFoamPlan (cfg : FoamConfig) (β : ℝ) (N : ℕ)
    (u0 : Joint E F) (swap : Bool) :
    QueryPlan (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) (foamCalls cfg * N) :=
  if swap then
    transportPlan (Sum.map swapPoint swapPoint) swapPoint swapPoint
      (proximalFoamPlan cfg β N (swapPoint u0))
  else proximalFoamPlan cfg β N u0

noncomputable def orientedProximalFoam (cfg : FoamConfig) (β : ℝ) (N : ℕ)
    (u0 : Joint E F) (swap : Bool) :
    Algorithm (Joint E F ⊕ Joint E F) (Joint E F) (Joint E F) :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (.inl u0) u0 (foamCalls cfg * N) (fun _ => orientedProximalFoamPlan cfg β N u0 swap)


noncomputable def tunedFoamConfig (L M m δ D ε : ℝ) : FoamConfig :=
  let β := m + 16 * δ
  let Mr := M + β
  let mr := m + β
  let LF := 2 * L + β
  { a := Mr / 2
    b := mr / 2
    α := Real.sqrt (mr / Mr)
    L := LF
    η := 1 / (8 * LF)
    innerSteps := ⌈2048 * LF / Mr⌉₊
    outerSteps := ⌈2 / Real.sqrt (mr / Mr) * Real.log (2 + 1024 * LF ^ 2 * D ^ 2 * mr / (Mr * m ^ 2 * ε))⌉₊ }

noncomputable def nearZeroSumGameOutput (p : Public) :
    Algorithm (Space p ⊕ Space p) (Space p) (Space p) :=
  let m := min p.μ p.ν
  let M := max p.μ p.ν
  let β := m + 16 * p.δ
  let cfg := tunedFoamConfig p.L M m p.δ p.D p.ε
  let N := ⌈2 * (m + β) / m * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
  orientedProximalFoam cfg β N (initialPoint p) (decide (p.μ < p.ν))

end OracleTemplate.NearZeroSum
