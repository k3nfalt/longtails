import LongTails.Algorithms.PLMinimaxCubic
import LongTails.Setups.NonconvexPLSecondOrder
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open LongTails.Setups.NonconvexPLSecondOrder

namespace OracleTemplate.PLMinimax

structure Tuning where
  smoothness : ℝ
  curvature : ℝ
  mesh : ℝ
  accuracy : ℝ
  threshold : ℝ
  gradientTolerance : ℝ
  hessianTolerance : ℝ
  regularization : ℝ
  distanceTolerance : ℝ
  residualTolerance : ℝ
  primalSteps : ℕ
  dualSteps : ℕ
  refinementSteps : ℕ

noncomputable def tuning (p : Params) : Tuning :=
  let κ := p.L / p.μ
  let C := 4 + 32 * κ
  let A := 1 + 2 * κ
  let M := 6 * ((2 * p.L) * (p.ρ * C / (2 * Real.sqrt (p.L * p.μ))))
  let η := Real.sqrt (100 * p.ρ * Real.sqrt κ * (4 + κ) * p.ε)
  let mesh := p.μ / (128 * p.ρ * Real.sqrt C)
  let εbar := min p.ε (min (η ^ 2 / (4 * M)) (16 * M * mesh ^ 2))
  let s := Real.sqrt (εbar / (16 * M))
  let a := M * s ^ 2 / 24
  let b := M * s / 12
  let θ := b ^ 4 / (64 * p.L ^ 2 * C ^ 2)
  let e := min (p.μ / (128 * p.ρ)) (min (a / (2 * p.L))
    (min (b / (8 * p.L ^ 2 * p.ρ * (θ⁻¹ + 18 * p.L ^ 2 * θ⁻¹ ^ 2)))
      (min (p.ε / (8 * p.L * κ)) (η / (2 * M * A ^ 3)))))
  let τ := p.μ * e / 8
  let S := 32 * κ * (p.Δ + p.D)
  { smoothness := M, curvature := η, mesh := mesh, accuracy := εbar, threshold := s,
    gradientTolerance := a, hessianTolerance := b, regularization := θ,
    distanceTolerance := e, residualTolerance := τ,
    primalSteps := ⌈18 * Real.log (12 * Real.sqrt κ)⌉₊,
    dualSteps := ⌈4 * κ * Real.log (1 + 64 * p.L * S / τ ^ 2)⌉₊,
    refinementSteps := ⌈Real.log (1 + p.ρ * (p.μ / (64 * p.ρ)) ^ 2 / τ) / Real.log 2⌉₊ + 1 }

inductive Phase (p : Params) where
  | initialize (stage iteration : ℕ)
  | track (origin displacement : p.E) (segments segment iteration : ℕ) (terminal : Bool)
  | finished

structure State (p : Params) where
  center : p.E
  point : Space p
  phase : Phase p

noncomputable def cubicAdvance (p : Params) (s : State p) (reply : spec.Reply p) : State p := by
  classical
  let c := tuning p
  let g := (2 * p.L) • (s.center - s.point.fst)
  let B := envelopeHessianApprox p.L (regularizedHessian reply.2.2 p.L) c.regularization
  let d := envelopeCubicStep g B c.smoothness
  let m := max 1 ⌈‖d‖ / c.mesh⌉₊
  exact { center := s.center + (1 / (m : ℝ)) • d, point := s.point, phase := .track s.center d m 1 0 (decide (‖d‖ ≤ c.threshold)) }

noncomputable def methodUpdate (p : Params) (s : State p) (reply : spec.Reply p) : State p := by
  classical
  let c := tuning p
  match s.phase with
  | .initialize j i =>
      if i < c.primalSteps then
        let g := reply.2.1.fst + (2 * p.L) • (s.point.fst - s.center)
        exact { s with point := WithLp.toLp 2 (s.point.fst - (1 / (9 * p.L)) • g, s.point.snd), phase := .initialize j (i + 1) }
      else if j < c.dualSteps then
        exact { s with point := WithLp.toLp 2 (s.point.fst, s.point.snd + (1 / (2 * p.L)) • reply.2.1.snd), phase := .initialize (j + 1) 0 }
      else
        exact cubicAdvance p s reply
  | .track origin displacement m j i terminal =>
      if i < c.refinementSteps then
        let r := reply.2.1 + WithLp.toLp 2 ((2 * p.L) • (s.point.fst - s.center), 0)
        let K := regularizedHessian reply.2.2 p.L
        exact { s with point := s.point + residualNewtonStep r K p.ρ, phase := .track origin displacement m j (i + 1) terminal }
      else if j < m then
        exact { s with center := origin + ((j + 1 : ℕ) / (m : ℝ)) • displacement, phase := .track origin displacement m (j + 1) 0 terminal }
      else if terminal then
        exact { s with phase := .finished }
      else
        exact cubicAdvance p s reply
  | .finished => exact s

noncomputable def method (p : Params) : Algorithm (spec.Query p) (spec.Reply p) (spec.Output p) where
  State := State p
  initial := fun _ => { center := p.x0, point := WithLp.toLp 2 (p.x0, p.y0), phase := .initialize 0 0 }
  query := fun s => (0, s.point)
  update := methodUpdate p
  output := fun s => s.point.fst

noncomputable def output (p : Params) (oracle : Oracle (spec.Query p) (spec.Reply p)) (K : ℕ)
    (seed : (k : ℕ) → oracle.Seed k) : p.E := execute oracle (method p) (fun _ => K) () seed

end OracleTemplate.PLMinimax
