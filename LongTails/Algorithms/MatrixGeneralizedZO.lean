import LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth
import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

def sgnR (b : Bool) : ℝ := if b then 1 else -1

noncomputable def signVec {d : ℕ} (s : Fin d → Bool) : Point d := WithLp.toLp 2 (fun i => sgnR (s i))

noncomputable def clip (c t : ℝ) : ℝ := max (-c) (min c t)

noncomputable def Lp (p : Params) : ℝ := max p.L1 (1 / (p.R * Real.sqrt p.d))

noncomputable def rp (p : Params) : ℝ := 48 * p.r + 16

noncomputable def thetaCap (p : Params) : ℝ := min (1 / 4) (2 / (p.r + 2))

noncomputable def gapLevel (p : Params) (A : ℝ) : ℝ := 8 * p.R ^ 2 / A

noncomputable def gradBound (p : Params) (F : ℝ) : ℝ := 4 * Lp p * F + 2 * Real.sqrt (p.L0 * F)

noncomputable def curvBound (p : Params) (F : ℝ) : ℝ := p.L0 + Lp p * gradBound p F

noncomputable def stepSize (p : Params) (A : ℝ) : ℝ := 1 / (8 * curvBound p (gapLevel p A) * rp p)

noncomputable def weight (p : Params) (A : ℝ) : ℝ :=
  min (Real.sqrt (A * stepSize p A / (8 * p.d))) (thetaCap p * A)

noncomputable def clipLevel (p : Params) (A : ℝ) : ℝ :=
  1 / (2 * Lp p * stepSize p A * Real.sqrt (48 * p.r))

noncomputable def sched (p : Params) : ℕ → ℝ
  | 0 => p.R ^ 2 / (2 * p.Δ)
  | k + 1 => sched p k + weight p (sched p k)

noncomputable def errWeight (p : Params) (k : ℕ) : ℝ :=
  1 + sched p (k + 1) * stepSize p (sched p k) + weight p (sched p k) * Real.sqrt p.d +
    weight p (sched p k) ^ 2 * p.d

noncomputable def fdStep (p : Params) (k : ℕ) : ℝ :=
  min (1 / (2 * Lp p * Real.sqrt p.d))
    (min (32 * p.L0 / (Lp p * curvBound p (gapLevel p (sched p k)) * p.d))
      (2 * (p.R / (32 * 2 ^ k * errWeight p k)) /
        (curvBound p (gapLevel p (sched p k)) * p.d)))

noncomputable def extrapolate (p : Params) (k : ℕ) (x z : Point p.d) : Point p.d :=
  (sched p k / (sched p k + weight p (sched p k))) • x +
    (weight p (sched p k) / (sched p k + weight p (sched p k))) • z

noncomputable def candidate (p : Params) (k : ℕ) (y : Point p.d) (s : Fin p.d → Bool)
    (v1 v2 : ℝ) : Point p.d :=
  y - (stepSize p (sched p k) *
    clip (clipLevel p (sched p k)) ((v1 - v2) / (2 * fdStep p k))) • signVec s

noncomputable def nextDual (p : Params) (k : ℕ) (z : Point p.d) (s : Fin p.d → Bool)
    (v1 v2 : ℝ) : Point p.d :=
  z - (weight p (sched p k) * ((v1 - v2) / (2 * fdStep p k))) • signVec s

noncomputable def stepPlan (p : Params) (k : ℕ) (xz : Point p.d × Point p.d)
    (s : Fin p.d → Bool) : QueryPlan (Point p.d) ℝ (Point p.d × Point p.d) 4 :=
  let y := extrapolate p k xz.1 xz.2
  .ask (y + fdStep p k • signVec s) fun v1 =>
  .ask (y - fdStep p k • signVec s) fun v2 =>
  .ask y fun v3 =>
  .ask (candidate p k y s v1 v2) fun v4 =>
  .done (if v4 ≤ v3 then candidate p k y s v1 v2 else y, nextDual p k xz.2 s v1 v2)

def runLength : ℕ → ℕ
  | 0 => 1
  | n + 1 => runLength n + 4

noncomputable def runPlan (p : Params) : (n : ℕ) → ℕ → Point p.d × Point p.d →
    (Fin n → Fin p.d → Bool) → QueryPlan (Point p.d) ℝ (Point p.d × ℝ) (runLength n)
  | 0, _, xz, _ => .ask xz.1 fun v => .done (xz.1, v)
  | n + 1, k, xz, seeds =>
      QueryPlan.bind (stepPlan p k xz (seeds 0))
        (fun next => runPlan p n (k + 1) next (fun j => seeds j.succ))

noncomputable def bestPair {α : Type*} : List (α × ℝ) → α × ℝ → α × ℝ
  | [], b => b
  | c :: l, b => bestPair l (if c.2 < b.2 then c else b)

noncomputable def selectBest {α : Type*} (x0 : α) : List (α × ℝ) → α
  | [] => x0
  | c :: rest => (bestPair rest c).1

noncomputable def numRuns (p : Params) : ℕ := ⌈Real.logb 2 (1 / p.δ)⌉₊

noncomputable def iterations (p : Params) : ℕ :=
  ⌈510 * Real.sqrt (p.d * (p.r + 1) * p.L0 * p.R ^ 2 / p.ε) +
    1300 * (p.r + 1 + p.L1 * p.R * Real.sqrt (p.d * (p.r + 1))) *
      Real.log (Real.exp 1 + 8 * p.Δ / p.ε)⌉₊

def Seeds (p : Params) := Fin (numRuns p) → Fin (iterations p) → Fin p.d → Bool

noncomputable instance (p : Params) : Fintype (Seeds p) :=
  inferInstanceAs (Fintype (Fin (numRuns p) → Fin (iterations p) → Fin p.d → Bool))

instance (p : Params) : Nonempty (Seeds p) :=
  inferInstanceAs (Nonempty (Fin (numRuns p) → Fin (iterations p) → Fin p.d → Bool))

instance (p : Params) : MeasurableSpace (Seeds p) := ⊤

instance (p : Params) : MeasurableSingletonClass (Seeds p) := ⟨fun _ => trivial⟩

noncomputable def fullPlan (p : Params) (seed : Seeds p) :
    QueryPlan (Point p.d) ℝ (Point p.d) (runLength (iterations p) * numRuns p) :=
  QueryPlan.map (selectBest p.x0)
    (QueryPlan.traverse (numRuns p)
      (fun j => runPlan p (iterations p) 0 (p.x0, p.x0) (seed j)))

noncomputable def algorithm (p : Params) : Algorithm (Point p.d) ℝ (Point p.d) :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩
    p.x0 p.x0 (runLength (iterations p) * numRuns p) (fullPlan p)

end OracleTemplate.MatrixGeneralizedZO
