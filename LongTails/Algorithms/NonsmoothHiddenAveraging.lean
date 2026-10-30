import LongTails.Algorithms.SafeguardedSimilarTriangles
import LongTails.Setups.NonsmoothHiddenConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

namespace OracleTemplate.NonsmoothHidden

open LocalHiddenConvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def averageQuery (k : ℕ) (x z : E) : E :=
  ((k : ℝ) / ((k : ℝ) + 1)) • x + (1 / ((k : ℝ) + 1)) • z

noncomputable def restartOutside (R : ℝ) (x : E) : E :=
  if R ≤ ‖x‖ then 0 else x

noncomputable def localRun (oracle : E → Ω → E) (r D : ℝ) (b : E) :
    (N : ℕ) → ℕ → E → E → (Fin N → Ω) → E × E
  | 0, _, x, z, _ => (x, z)
  | N + 1, k, x, z, ξ =>
      let y := averageQuery k x z
      let z' := ballProj b (2 * r) (z - D⁻¹ • oracle y (ξ 0))
      localRun oracle r D b N (k + 1) y z' (fun i => ξ i.succ)

noncomputable def localOutput (oracle : E → Ω → E) (r D : ℝ) (N : ℕ) (b : E)
    (ξ : Fin N → Ω) : E := (localRun oracle r D b N 0 b b ξ).1

noncomputable def epochRun (oracle : E → Ω → E) (r D R : ℝ) (N : ℕ) :
    ℕ → E → (ℕ → Ω) → E
  | 0, b, _ => b
  | K + 1, b, ξ => epochRun oracle r D R N K
      (restartOutside R (localOutput oracle r D N b (fun i => ξ i))) (fun i => ξ (N + i))

structure State (E : Type*) where
  epoch : ℕ
  step : ℕ
  center : E
  average : E
  dual : E

noncomputable def advance (r D R : ℝ) (N K : ℕ) (s : State E) (g : E) : State E :=
  if s.epoch < K then
    let y := averageQuery s.step s.average s.dual
    if s.step + 1 = N then
      let b := restartOutside R y
      ⟨s.epoch + 1, 0, b, b, b⟩
    else
      ⟨s.epoch, s.step + 1, s.center, y,
        ballProj s.center (2 * r) (s.dual - D⁻¹ • g)⟩
  else s

noncomputable def hiddenAveraging (r D R : ℝ) (N K : ℕ) : Algorithm E E E where
  State := State E
  initial _ := ⟨0, 0, 0, 0, 0⟩
  query s := (0, averageQuery s.step s.average s.dual)
  update := advance r D R N K
  output s := s.center

noncomputable def shape (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  1 + 64 * p.LJ * p.R / p.μ

noncomputable def conditioning (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  p.Lc / p.μ

noncomputable def radius (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  p.R / shape p

noncomputable def epochFraction (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  1 / (2 * conditioning p * shape p)

noncomputable def signal (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  2 * p.G * p.Lc * p.R / (p.μ * p.ε)

noncomputable def initialBound (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  p.G * p.R * (1 + p.LJ * p.R / p.μ)

noncomputable def localIterations (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℕ :=
  ⌈4194304 * (1 + signal p) ^ 2 * (Real.log (16 * (1 + signal p))) ^ 2⌉₊

noncomputable def outerIterations (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℕ :=
  ⌈2 * conditioning p * shape p * Real.log (2 + 2 * initialBound p / p.ε)⌉₊

noncomputable def dualScale (p : LongTails.Setups.NonsmoothHiddenConvex.Params) : ℝ :=
  p.G * Real.sqrt (localIterations p : ℝ) / radius p

noncomputable def tunedAlgorithm (p : LongTails.Setups.NonsmoothHiddenConvex.Params) :
    Algorithm p.E p.E p.E :=
  hiddenAveraging (radius p) (dualScale p) p.R (localIterations p) (outerIterations p)

end OracleTemplate.NonsmoothHidden
