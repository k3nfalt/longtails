import LongTails.Setups.TailObliviousMonotoneRootFinding
import LongTails.Algorithms.ContinuizedQuasar

namespace LongTails.Algorithms.TailObliviousExtragradient

open OracleTemplate
open LongTails.Setups.TailObliviousMonotoneRootFinding

noncomputable def strength (d : Public) (k j : ℕ) : ℝ := d.L * 2 ^ j / 2 ^ k

noncomputable def relaxation (k : ℕ) : ℝ := 1 / (16 * 2 ^ k)

noncomputable def stepSize (d : Public) (k j : ℕ) : ℝ := relaxation k / strength d k j

def innerSteps (k : ℕ) : ℕ := 96 * 2 ^ k

structure State (d : Public) where
  epoch : ℕ
  stage : ℕ
  step : ℕ
  half : Bool
  anchor : d.E
  point : d.E
  extra : d.E
  best : d.E

noncomputable def initial (d : Public) : State d :=
  ⟨0, 0, 0, false, strength d 0 0 • d.x0, d.x0, d.x0, d.x0⟩

noncomputable def update (d : Public) (s : State d) (r : d.E) : State d :=
  if s.half then
    let x := s.point - stepSize d s.epoch s.stage •
      (r + strength d s.epoch s.stage • s.extra - s.anchor)
    if s.step + 1 < innerSteps s.epoch then
      ⟨s.epoch, s.stage, s.step + 1, false, s.anchor, x, x, s.best⟩
    else if s.stage < s.epoch then
      ⟨s.epoch, s.stage + 1, 0, false, s.anchor + strength d s.epoch s.stage • x, x, x, s.best⟩
    else
      ⟨s.epoch + 1, 0, 0, false, strength d (s.epoch + 1) 0 • d.x0, d.x0, d.x0, x⟩
  else
    ⟨s.epoch, s.stage, s.step, true, s.anchor, s.point,
      s.point - stepSize d s.epoch s.stage •
        (r + strength d s.epoch s.stage • s.point - s.anchor), s.best⟩

noncomputable def algorithm (d : Public) : Algorithm d.E d.E d.E where
  State := State d
  initial := fun _ => initial d
  query := fun s => (0, if s.half then s.extra else s.point)
  update := update d
  output := State.best

noncomputable def output (d : Public) (O : Oracle d.E d.E)
    (budget : Fin 1 → ℕ) (ξ : (k : ℕ) → O.Seed k) : d.E :=
  execute O (algorithm d) budget () ξ

noncomputable def egStep {Ω : Type*} (d : Public) (g : d.E → Ω → d.E) (k j : ℕ)
    (b x : d.E) (ω : Fin 2 → Ω) : d.E :=
  let y := x - stepSize d k j • (g x (ω 0) + strength d k j • x - b)
  x - stepSize d k j • (g y (ω 1) + strength d k j • y - b)

noncomputable def stageRun {Ω : Type*} (d : Public) (g : d.E → Ω → d.E) (k j : ℕ)
    (b x : d.E) (ξ : Fin (innerSteps k) → Fin 2 → Ω) : d.E :=
  OracleTemplate.ContinuizedSimilarQuasar.iterateSamples
    (fun y ω => egStep d g k j b y ω) (innerSteps k) x ξ

noncomputable def epochAdvance {Ω : Type*} (d : Public) (g : d.E → Ω → d.E) (k : ℕ)
    (s : ℕ × d.E × d.E) (ξ : Fin (innerSteps k) → Fin 2 → Ω) : ℕ × d.E × d.E :=
  let z := stageRun d g k s.1 s.2.1 s.2.2 ξ
  (s.1 + 1, s.2.1 + strength d k s.1 • z, z)

noncomputable def epochState {Ω : Type*} (d : Public) (g : d.E → Ω → d.E) (k n : ℕ)
    (ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω) : ℕ × d.E × d.E :=
  OracleTemplate.ContinuizedSimilarQuasar.iterateSamples (epochAdvance d g k) n
    (0, strength d k 0 • d.x0, d.x0) (fun i => ξ i)

noncomputable def epochOutput {Ω : Type*} (d : Public) (g : d.E → Ω → d.E) (k : ℕ)
    (ξ : ℕ → Fin (innerSteps k) → Fin 2 → Ω) : d.E :=
  (epochState d g k (k + 1) ξ).2.2

end LongTails.Algorithms.TailObliviousExtragradient
