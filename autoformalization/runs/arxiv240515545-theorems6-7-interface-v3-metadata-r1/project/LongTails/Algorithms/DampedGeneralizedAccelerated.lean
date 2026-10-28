import LongTails.Setups.GeneralizedSmoothAndConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

structure Iterate (E : Type*) where
  A : ℝ
  x : E
  z : E
  guess : ℝ

structure Pending (E : Type*) where
  previous : Iterate E
  weight : ℝ
  y : E
  curvature : ℝ
  point : E

inductive State (E : Type*) where
  | start (A : ℝ) (x : E)
  | ready (s : Iterate E)
  | pending (p : Pending E)

noncomputable def tentativeWeight {E : Type*} (s : Iterate E) : ℝ :=
  (1 + Real.sqrt (1 + 4 * s.guess * s.A)) / (2 * s.guess)

noncomputable def coupling {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Iterate E) : E :=
  let a := tentativeWeight s
  (s.A / (s.A + a)) • s.x + (a / (s.A + a)) • s.z

noncomputable def localCurvature {E : Type*} [NormedAddCommGroup E]
    (L0 L1 : ℝ) (g : E) : ℝ :=
  4 * (L0 + L1 * ‖g‖)

noncomputable def prepare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (s : Iterate E) (y g : E) : Pending E :=
  let M := localCurvature L0 L1 g
  ⟨s, tentativeWeight s, y, M, y - (1 / M) • g⟩

noncomputable def finish {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Pending E) (g : E) : Iterate E := by
  classical
  exact
    if p.curvature ≤ p.previous.guess then
      ⟨p.previous.A + p.weight, p.point, p.previous.z - p.weight • g,
        p.previous.guess / 16⟩
    else
      let γ := p.previous.guess / p.curvature
      let a := γ * p.weight
      let A := p.previous.A + a
      ⟨A, ((1 - γ) * p.previous.A / A) • p.previous.x +
          (γ * (p.previous.A + p.weight) / A) • p.point,
        p.previous.z - a • g, 16 * p.previous.guess⟩

noncomputable def step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (g : E → E) (s : Iterate E) : Iterate E :=
  let p := prepare L0 L1 s (coupling s) (g (coupling s))
  finish p (g p.point)

noncomputable def initialIterate {E : Type*} [NormedAddCommGroup E]
    (L0 L1 R Δ : ℝ) (x0 : E) (g : E → E) : Iterate E :=
  ⟨R ^ 2 / (2 * Δ), x0, x0, localCurvature L0 L1 (g x0)⟩

noncomputable def run {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L0 L1 : ℝ) (g : E → E) (s : Iterate E) : ℕ → Iterate E
  | 0 => s
  | n + 1 => step L0 L1 g (run L0 L1 g s n)

noncomputable def algorithm (p : Public) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := .start (p.R ^ 2 / (2 * p.Δ)) p.x0
  query := fun state => (0, match state with
    | .start _ x => x
    | .ready s => coupling s
    | .pending s => s.point)
  update
    | .start A x, g =>
      let s : Iterate p.E := ⟨A, x, x, localCurvature p.L0 p.L1 g⟩
      .pending (prepare p.L0 p.L1 s x g)
    | .ready s, g => .pending (prepare p.L0 p.L1 s (coupling s) g)
    | .pending s, g => .ready (finish s g)
  output
    | .start _ x => x
    | .ready s => s.x
    | .pending s => s.previous.x

end OracleTemplate.GeneralizedAccelerated
