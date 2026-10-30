import LongTails.Proofs.QueryPlan
import LongTails.Proofs.ComparisonTernary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

namespace OracleTemplate.ComparisonOrth

open QueryPlan

abbrev Pt (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev CPlan (n : ℕ) (U : Type) (k : ℕ) := QueryPlan (Pt n × Pt n) Bool U k

def iteratePlan {Q R U : Type} (c : ℕ) : (m : ℕ) → (U → QueryPlan Q R U c) → U →
    QueryPlan Q R U (c * m)
  | 0, _, u => .done u
  | m + 1, step, u => bind (step u) (fun v => iteratePlan c m step v)

def comparePlan {n : ℕ} (x y : Pt n) : CPlan n Bool 1 := .ask (x, y) .done

noncomputable def ternaryRoundPlan {n c : ℕ} (inner : ℝ → CPlan n (Pt n) c) (I : ℝ × ℝ) :
    CPlan n (ℝ × ℝ) ((1 + c) + c) :=
  bind (inner (trisectLeft I.1 I.2)) fun p1 =>
    bind (inner (trisectRight I.1 I.2)) fun p2 =>
      .ask (p1, p2) fun b => .done (ternaryStep b I.1 I.2)

noncomputable def searchPlan {n c : ℕ} (m : ℕ) (inner : ℝ → CPlan n (Pt n) c) (w : ℝ) :
    CPlan n (Pt n) (c + ((1 + c) + c) * m) :=
  bind (iteratePlan _ m (ternaryRoundPlan inner) (-w, w)) fun I => inner I.1

noncomputable def boxPlan {n : ℕ} (m : ℕ) (Φ : ℝ → ℝ → ℝ → Pt n) (w1 w2 w3 : ℝ) :=
  searchPlan m (fun a => searchPlan m (fun b => searchPlan m
    (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) w2) w1

noncomputable def nrm {n : ℕ} (v : Pt n) : Pt n := ‖v‖⁻¹ • v

noncomputable def unitVec (n : ℕ) (i : ℕ) : Pt n :=
  if hi : i < n then EuclideanSpace.single ⟨i, hi⟩ 1 else 0

def sgn (b : Bool) : ℝ := if b then 1 else -1

noncomputable def probePlan {n : ℕ} (x : Pt n) (h : ℝ) (z : Pt n) : CPlan n Bool 1 :=
  comparePlan (x - h • z) (x + h • z)

noncomputable def signPlan {n : ℕ} (x : Pt n) (h : ℝ) : CPlan n (List Bool) (1 * n) :=
  traverse n (fun i => probePlan x h (unitVec n i))

def listSign (L : List Bool) (i : ℕ) : ℝ := sgn (L.getD i true)

noncomputable def championStep {n : ℕ} (x : Pt n) (h : ℝ) (L : List Bool) (s : ℕ × ℕ) :
    CPlan n (ℕ × ℕ) 1 :=
  map (fun b => if b then (s.2, s.2 + 1) else (s.1, s.2 + 1))
    (probePlan x h (listSign L s.2 • unitVec n s.2 - listSign L s.1 • unitVec n s.1))

noncomputable def championPlan {n : ℕ} (x : Pt n) (h : ℝ) (L : List Bool) :
    CPlan n (ℕ × ℕ) (1 * n) :=
  iteratePlan 1 n (championStep x h L) (0, 0)

noncomputable def bisectStep {n : ℕ} (x : Pt n) (h σ : ℝ) (c i : ℕ) (I : ℝ × ℝ) :
    CPlan n (ℝ × ℝ) 1 :=
  map (fun b => if b then ((I.1 + I.2) / 2, I.2) else (I.1, (I.1 + I.2) / 2))
    (probePlan x h (σ • (unitVec n i - ((I.1 + I.2) / 2) • unitVec n c)))

noncomputable def ratioPlan {n : ℕ} (x : Pt n) (h σ : ℝ) (c i m : ℕ) : CPlan n ℝ (1 * m) :=
  map (fun I => (I.1 + I.2) / 2) (iteratePlan 1 m (bisectStep x h σ c i) (-2, 2))

noncomputable def listVec (n : ℕ) (W : List ℝ) : Pt n :=
  WithLp.toLp 2 (fun i : Fin n => W.getD i.1 0)

noncomputable def dirPlan {n : ℕ} (x : Pt n) (h : ℝ) (m : ℕ) :=
  bind (signPlan x h) fun L =>
    bind (championPlan x h L) fun s =>
      map (fun W => listSign L s.1 • nrm (listVec n W))
        (traverse n (fun i => ratioPlan x h (listSign L s.1) s.1 i.1 m))

structure OrthState (n : ℕ) where
  x : Pt n
  d : Pt n
  u1 : Pt n
  u2 : Pt n
  u3 : Pt n

noncomputable def projOut {n : ℕ} (s : OrthState n) (v : Pt n) : Pt n :=
  v - (inner ℝ v s.u1 • s.u1 + inner ℝ v s.u2 • s.u2 + inner ℝ v s.u3 • s.u3)

noncomputable def newState {n : ℕ} (x0 : Pt n) (s : OrthState n) (ghat xnew : Pt n) :
    OrthState n :=
  let G := nrm (projOut s ghat)
  let u1 := nrm (s.x - x0)
  { x := xnew
    d := s.d + G
    u1 := u1
    u2 := nrm (s.d - inner ℝ s.d u1 • u1)
    u3 := G }

noncomputable def boxPoint {n : ℕ} (x0 : Pt n) (s : OrthState n) (ghat : Pt n)
    (a b c : ℝ) : Pt n :=
  let t := newState x0 s ghat s.x
  x0 + a • t.u1 + b • t.u2 + c • t.u3

noncomputable def orthStepPlan {n : ℕ} (x0 : Pt n) (R h : ℝ) (m : ℕ) (s : OrthState n) :=
  bind (dirPlan s.x h m) fun ghat =>
    bind (boxPlan m (boxPoint x0 s ghat) (max R ‖s.x - x0‖) R R) fun xt =>
      (.ask (xt, s.x) fun b => .done (newState x0 s ghat (if b then xt else s.x)) :
        CPlan n (OrthState n) 1)

noncomputable def initState {n : ℕ} (x0 : Pt n) : OrthState n := ⟨x0, 0, 0, 0, 0⟩

noncomputable def orthPlan {n : ℕ} (x0 : Pt n) (R h : ℝ) (m K : ℕ) :=
  map (fun s : OrthState n => s.x) (iteratePlan _ K (orthStepPlan x0 R h m) (initState x0))

noncomputable def comparisonOrth {n : ℕ} (x0 : Pt n) (R h : ℝ) (m K : ℕ) :
    Algorithm (Pt n × Pt n) Bool (Pt n) :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ (x0, x0) x0 _
    (fun _ : Unit => orthPlan x0 R h m K)

end OracleTemplate.ComparisonOrth
