import LongTails.Setups.CoupledStronglyConcaveMinimax
import LongTails.Algorithms.CoupledMinimaxInner
import LongTails.Algorithms.Extragradient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

namespace LongTails.Algorithms.CoupledMinimax

open OracleTemplate
open LongTails.Setups.CoupledStronglyConcaveMinimax

abbrev MinSpace (p : Params) := WithLp 2 (XSpace p × Weights p)

noncomputable def cap (p : Params) : ℝ := 1 + 2 * p.Z * (p.Gy + 1) / p.δ
noncomputable def smoothness (p : Params) : ℝ := 1 + p.μ + p.Lf + cap p * p.LJ + 2 * p.J
noncomputable def valueSmoothness (p : Params) : ℝ := smoothness p * (1 + smoothness p / p.μ)
noncomputable def gapBound (p : Params) : ℝ := p.Gx * p.DX + p.Gy * p.DY + cap p * p.C
noncomputable def tolerance (p : Params) : ℝ :=
  p.ε / (2 * (1 + p.ε) * (1 + Real.sqrt p.constraints + cap p))
noncomputable def innerIterations (p : Params) : ℕ := ⌈4 * Real.sqrt (smoothness p / p.μ)⌉₊
noncomputable def innerRestarts (p : Params) : ℕ :=
  ⌈Real.log (2 + 12 * smoothness p * p.DY / tolerance p) / Real.log 2⌉₊
noncomputable def outerIterations (p : Params) : ℕ :=
  1 + ⌈72 * valueSmoothness p * gapBound p / tolerance p ^ 2⌉₊
noncomputable def stepCalls (p : Params) : ℕ := 2 + innerIterations p * innerRestarts p
noncomputable def calls (p : Params) : ℕ := stepCalls p * outerIterations p

noncomputable def minDomain (p : Params) : Set (MinSpace p) :=
  {q | q.fst ∈ p.X ∧ (∀ i, 0 ≤ q.snd i) ∧ (∑ i, q.snd i) ≤ cap p}

noncomputable def start (p : Params) : MinSpace p := WithLp.toLp 2 (p.x0, 0)

noncomputable def query (p : Params) (q : MinSpace p) (y : YSpace p) : Joint p :=
  WithLp.toLp 2 (q.fst, y)

noncomputable def lagrangianGradient (p : Params) (r : Reply p) (w : Weights p) : Joint p :=
  r.gradient - r.jacobian.adjoint w

noncomputable def minGradient (p : Params) (r : Reply p) (w : Weights p) : MinSpace p :=
  WithLp.toLp 2 ((lagrangianGradient p r w).fst, -r.constraints)

structure Candidate (p : Params) where
  point : Output p
  displacement : ℝ

noncomputable def step (p : Params) (q : MinSpace p) :
    QueryPlan (Joint p) (Reply p) (MinSpace p × Candidate p) (stepCalls p) :=
  (CoupledMinimaxInner.restart (query p q)
    (fun r => -(lagrangianGradient p r q.snd).snd)
    (SaddlePoint.project p.Y) (smoothness p)
    (innerIterations p) (innerRestarts p) p.y0).bind fun y =>
      .ask (query p q y) fun r =>
        let b := SaddlePoint.project p.Y (y + (1 / smoothness p) •
          (lagrangianGradient p r q.snd).snd)
        .ask (query p q b) fun r' =>
          let q' := SaddlePoint.project (minDomain p)
            (q - (1 / (2 * valueSmoothness p)) • minGradient p r' q.snd)
          .done (q', ⟨⟨q'.fst, b, q'.snd⟩, ‖q' - q‖⟩)

noncomputable def outer (p : Params) : (N : ℕ) → MinSpace p →
    QueryPlan (Joint p) (Reply p) (List (Candidate p)) (stepCalls p * N)
  | 0, _ => .done []
  | N + 1, q => (step p q).bind fun v => (outer p N v.1).map (v.2 :: ·)

noncomputable def select (p : Params) : List (Candidate p) → Output p
  | [] => ⟨p.x0, p.y0, 0⟩
  | c :: cs => (cs.foldl (fun a b => if b.displacement ≤ a.displacement then b else a) c).point

noncomputable def algorithm (p : Params) : Algorithm (Joint p) (Reply p) (Output p) :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (query p (start p) p.y0) ⟨p.x0, p.y0, 0⟩ (calls p)
    (fun _ : Unit => (outer p (outerIterations p) (start p)).map (select p))

noncomputable def output (p : Params) (O : Oracle (Joint p) (Reply p))
    (ξ : (k : ℕ) → O.Seed k) : Output p :=
  execute O (algorithm p) (fun _ => calls p) () ξ

end LongTails.Algorithms.CoupledMinimax
