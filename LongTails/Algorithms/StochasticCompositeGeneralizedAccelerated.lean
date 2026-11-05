import LongTails.Setups.StochasticCompositeGeneralizedSmooth
import LongTails.Algorithms.CompositeGeneralizedAccelerated
import LongTails.Algorithms.RobustGradientEstimator

namespace OracleTemplate.StochasticCompositeGeneralized

open LongTails.Setups.StochasticCompositeGeneralizedSmooth
open CompositeGeneralized (weight mixPoint)
open RobustGradient (pilotCenter centeredClip)

noncomputable def confidence (p : Public) (k : ℕ) : ℝ :=
  Real.log (64 * Real.exp 1 * ((k : ℝ) + 1) ^ 2 / p.δ)

noncomputable def pilotSize (p : Public) (k : ℕ) : ℕ :=
  max 1 ⌈16 * confidence p k⌉₊

noncomputable def clipRadius (p : Public) (k : ℕ) : ℝ :=
  max (384 * p.σ)
    (2 * (1048576 * p.σ ^ p.α * p.R * confidence p k / p.ε) ^ (1 / (p.α - 1)))

noncomputable def varianceBound (p : Public) (k : ℕ) : ℝ :=
  (2 * clipRadius p k) ^ (2 - p.α) * p.σ ^ p.α

noncomputable def batchSize (p : Public) (k : ℕ) (a : ℝ) : ℕ :=
  max 1 ⌈1099511627776 * (varianceBound p k * a * confidence p k ^ 2 / p.ε +
    clipRadius p k * a * confidence p k ^ 2 / p.R)⌉₊

structure State (E : Type u) where
  stage : ℕ
  iteration : ℕ
  A : ℝ
  x : E
  z : E
  M : ℝ
  center : E
  total : E
  received : ℕ
  replies : ℕ → E

noncomputable def stepWeight (p : Public) (s : State p.E) : ℝ :=
  weight p.L1 (2 * p.R) s.A s.M

noncomputable def queryPoint (p : Public) (s : State p.E) : p.E :=
  mixPoint s.A (stepWeight p s) s.x s.z

noncomputable def samplePilot (p : Public) (k : ℕ) (v : ℕ → p.E) : p.E :=
  pilotCenter (192 * p.σ) (fun i : Fin (pilotSize p k) => v i)

noncomputable def initialState (p : Public) : State p.E := by
  classical
  exact ⟨if p.Δ ≤ p.ε then 4 else 0, 0, p.R ^ 2 / (4 * p.Δ),
    p.x0, p.x0, 0, 0, 0, 0, fun _ => 0⟩

noncomputable def update (p : Public) (s : State p.E) (reply : p.E) : State p.E := by
  classical
  exact if s.stage = 0 then
    let v := Function.update s.replies s.received reply
    if s.received + 1 < pilotSize p s.iteration then
      { s with received := s.received + 1, replies := v }
    else
      { s with
        stage := 1, M := p.L0 + p.L1 * (‖samplePilot p s.iteration v‖ + 96 * p.σ),
        received := 0, replies := fun _ => 0 }
  else if s.stage = 1 then
    let v := Function.update s.replies s.received reply
    if s.received + 1 < pilotSize p s.iteration then
      { s with received := s.received + 1, replies := v }
    else
      { s with
        stage := 2, center := samplePilot p s.iteration v,
        total := 0, received := 0, replies := fun _ => 0 }
  else if s.stage = 2 then
    let total := s.total + centeredClip (clipRadius p s.iteration) s.center reply
    if s.received + 1 < batchSize p s.iteration (stepWeight p s) then
      { s with received := s.received + 1, total := total }
    else
      { s with stage := 3, total := total }
  else if s.stage = 3 then
    let a := stepWeight p s
    let A := s.A + a
    { s with
      stage := if 4 * p.R ^ 2 / p.ε ≤ A then 4 else 0,
      iteration := s.iteration + 1, A := A, x := mixPoint s.A a s.x reply, z := reply,
      M := 0, center := 0, total := 0, received := 0, replies := fun _ => 0 }
  else s

noncomputable def algorithm (p : Public) : Algorithm (Query p) p.E p.E where
  State := State p.E
  initial _ := initialState p
  query s := (0,
    if s.stage = 0 then .gradient s.x
    else if s.stage = 1 ∨ s.stage = 2 then .gradient (queryPoint p s)
    else if s.stage = 3 then .prox (stepWeight p s) s.z
      ((1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total)
    else .gradient s.x)
  update := update p
  output s := s.x

end OracleTemplate.StochasticCompositeGeneralized
