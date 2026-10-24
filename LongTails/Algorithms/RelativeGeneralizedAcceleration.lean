import LongTails.Setups.RelativeGeneralizedSmoothConvex
import LongTails.Proofs.Clipping

namespace OracleTemplate.RelativeGeneralized

open LongTails.Setups.RelativeGeneralizedSmoothConvex

structure State (E : Type*) where
  A : ℝ
  x : E
  z : E

noncomputable def noiseBudget (p : Public) (N : ℕ) : ℝ := 2 + p.α ^ 2 * N

noncomputable def weight (p : Public) (N : ℕ) (s : State p.E) : ℝ :=
  s.A / (4096 * (1 + p.L1 * p.R * Real.sqrt (noiseBudget p N) + Real.sqrt (p.L0 * s.A)))

noncomputable def stepSize (p : Public) (N : ℕ) (s : State p.E) : ℝ :=
  1 / (1024 * (p.L0 + p.L1 ^ 2 * (noiseBudget p N * p.R ^ 2 / s.A)))

noncomputable def queryPoint (p : Public) (N : ℕ) (s : State p.E) : p.E :=
  (s.A / (s.A + weight p N s)) • s.x + (weight p N s / (s.A + weight p N s)) • s.z

noncomputable def projectBall (p : Public) (x : p.E) : p.E :=
  p.x0 + clip (2 * p.R) (x - p.x0)

noncomputable def advance (p : Public) (N : ℕ) (s : State p.E) (reply : p.E) : State p.E :=
  ⟨s.A + weight p N s, projectBall p (queryPoint p N s - stepSize p N s • reply),
    projectBall p (s.z - weight p N s • reply)⟩

noncomputable def initialState (p : Public) : State p.E := ⟨p.R ^ 2 / p.Δ, p.x0, p.x0⟩

noncomputable def acceleration (p : Public) (N : ℕ) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := initialState p
  query s := (0, queryPoint p N s)
  update := advance p N
  output s := s.x

noncomputable def output (p : Public) (N : ℕ) (oracle : Oracle p.E p.E)
    (seed : (k : ℕ) → oracle.Seed k) : p.E :=
  execute oracle (acceleration p N) (fun _ => N) () seed

end OracleTemplate.RelativeGeneralized
