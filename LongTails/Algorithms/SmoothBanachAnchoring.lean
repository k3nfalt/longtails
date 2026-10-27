import LongTails.Setups.StochasticSmoothBanachFixedPoint
import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.SmoothBanachAnchoring

open OracleTemplate
open LongTails.Setups.StochasticSmoothBanachFixedPoint

noncomputable def levels (q : Params) : ℕ := Nat.clog 2 (⌈16 * q.R / q.ε⌉₊ + 1)

noncomputable def strength (q : Params) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j / (2 : ℝ) ^ levels q

noncomputable def relaxation (q : Params) : ℝ :=
  1 / (1 + (2 : ℝ) ^ levels q +
    1024 * q.C * q.σ ^ 2 * (levels q + 1 : ℝ) ^ 2 / q.ε ^ 2)

noncomputable def innerSteps (q : Params) : ℕ :=
  ⌈8 * (levels q + 1 : ℝ) / relaxation q⌉₊

structure State (q : Params) where
  stage : ℕ
  step : ℕ
  anchor : q.E
  point : q.E

noncomputable def initial (q : Params) : State q :=
  ⟨0, 0, strength q 0 • q.x0, q.x0⟩

def picardStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a η : ℝ) (b x reply : E) : E :=
  (1 - η * (1 + a)) • x + η • reply + η • b

noncomputable def update (q : Params) (s : State q) (reply : q.E) : State q :=
  if s.stage ≤ levels q then
    let η := relaxation q / strength q s.stage
    let x := picardStep (strength q s.stage) η s.anchor s.point reply
    if s.step + 1 < innerSteps q then
      { s with step := s.step + 1, point := x }
    else
      ⟨s.stage + 1, 0, s.anchor + strength q s.stage • x, x⟩
  else s

noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E where
  State := State q
  initial := fun _ => initial q
  query := fun s => (0, s.point)
  update := update q
  output := State.point

noncomputable def output (q : Params) (O : Oracle q.E q.E)
    (budget : Fin 1 → ℕ) (ξ : (k : ℕ) → O.Seed k) : q.E :=
  execute O (algorithm q) budget () ξ

noncomputable def epochAdvance (q : Params) (g : q.E → q.Ω → q.E)
    (s : ℕ × q.E × q.E) (ξ : Fin (innerSteps q) → q.Ω) : ℕ × q.E × q.E :=
  let a := strength q s.1
  let η := relaxation q / a
  let z := OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (fun x ω => picardStep a η s.2.1 x (g x ω)) (innerSteps q) s.2.2 ξ
  (s.1 + 1, s.2.1 + a • z, z)

noncomputable def epochState (q : Params) (g : q.E → q.Ω → q.E)
    (n : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) : ℕ × q.E × q.E :=
  OracleTemplate.ContinuizedSimilarQuasar.iterateSamples (epochAdvance q g) n
    (0, strength q 0 • q.x0, q.x0) (fun i => ξ i)

end LongTails.Algorithms.SmoothBanachAnchoring
