import LongTails.Setups.CohypomonotoneNewton
import LongTails.Algorithms.ComponentEnvelope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.CohypomonotoneNewton

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def linearSolve (D : E →L[ℝ] E) (b : E) : E := by
  classical
  exact if h : ∃ v, D v = b then h.choose else 0

noncomputable def trustRegion (D : E →L[ℝ] E) (r : E) (R : ℝ) : E := by
  classical
  exact if h : ∃ v, ‖v‖ ≤ R ∧ ∀ d, ‖d‖ ≤ R → ‖r + D v‖ ≤ ‖r + D d‖
    then h.choose else 0

noncomputable def inverseUpdate (M γ : ℝ) (target x : E)
    (reply : E × (E →L[ℝ] E)) : E :=
  let r := x + γ • reply.1 - target
  let D := ContinuousLinearMap.id ℝ E + γ • reply.2
  let v := linearSolve D (-r)
  let t := 1 / max 1 (2 * M * ‖r‖)
  x + t • v

noncomputable def inverseLength (M B ε : ℝ) : ℕ :=
  ⌈2 * max 1 (2 * M * B) * Real.log (1 + B / ε)⌉₊ + 1

open OracleTemplate.ComponentEnvelope (Program)

noncomputable def inverseTail (M γ : ℝ) (target : E) :
    ℕ → (E × (E × (E →L[ℝ] E))) → Program E (E × (E →L[ℝ] E)) (E × (E × (E →L[ℝ] E)))
  | 0, state => .done state
  | n + 1, state =>
      let x := inverseUpdate M γ target state.1 state.2
      .ask x (fun reply => inverseTail M γ target n (x, reply))

noncomputable def inversePlan (M γ ε : ℝ) (target start : E) :
    Program E (E × (E →L[ℝ] E)) (E × (E × (E →L[ℝ] E))) :=
  .ask start (fun reply => inverseTail M γ target
    (inverseLength M ‖start + γ • reply.1 - target‖ ε) (start, reply))

noncomputable def linearInverse [FiniteDimensional ℝ E] (D : E →L[ℝ] E) : E →L[ℝ] E := by
  classical
  exact if h : Function.Bijective D then
    ((LinearEquiv.ofBijective D.toLinearMap h).toContinuousLinearEquiv.symm : E →L[ℝ] E)
  else 0

noncomputable def graphJacobian [FiniteDimensional ℝ E] (γ : ℝ) (J : E →L[ℝ] E) : E →L[ℝ] E :=
  J.comp (linearInverse (ContinuousLinearMap.id ℝ E + γ • J))

noncomputable def affinePoint (a : ℝ) (c n f : E) (D : E →L[ℝ] E) : E :=
  n + linearSolve (ContinuousLinearMap.id ℝ E + a • D) (c - n - a • f)

noncomputable def modelPoint [FiniteDimensional ℝ E] (γ a : ℝ) (c n f : E)
    (J : E →L[ℝ] E) : E :=
  affinePoint a c n f (graphJacobian γ J)

structure OuterState (E : Type*) where
  k : ℕ
  mass : ℝ
  previous : ℝ
  point : E
  value : E

structure Trial (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  step : ℝ
  sample : E × (E × (E →L[ℝ] E))
  model : E

open LongTails.Setups.CohypomonotoneNewton (Public)

noncomputable def shift (p : Public.{u}) : ℝ := 2 * p.ρ + 1 / (p.H * p.R)

noncomputable def baseStep (p : Public.{u}) : ℝ := 1 / (128 * p.H * p.R)

noncomputable def maxStep (p : Public.{u}) : ℝ :=
  16 * p.R / p.ε + 2 / Real.sqrt (p.H * p.ε) + baseStep p

noncomputable def horizon (p : Public.{u}) : ℕ := ⌈64 * (1 + p.H * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ)⌉₊

noncomputable def searchFuel (p : Public.{u}) : ℕ :=
  ⌈200 * (1 + Real.log (2 + shift p * p.H * p.R + p.H * p.R ^ 2 / p.ε))⌉₊ + 1

noncomputable def currentPoint (p : Public.{u}) (st : OuterState p.E) : p.E :=
  if st.k = 0 then p.x0 else st.point + shift p • st.value

noncomputable def currentValue (p : Public.{u}) (st : OuterState p.E) : p.E :=
  if st.k = 0 then 0 else st.value

noncomputable def anchorMix (p : Public.{u}) (st : OuterState p.E) (a : ℝ) : p.E :=
  (a / (st.mass + a)) • p.x0 + (st.mass / (st.mass + a)) • currentPoint p st

noncomputable def midpoint (p : Public.{u}) (st : OuterState p.E) (a : ℝ) : p.E :=
  anchorMix p st a - (a * st.mass / (st.mass + a)) • currentValue p st

noncomputable def errorScale (p : Public.{u}) (st : OuterState p.E) (a : ℝ) : ℝ :=
  (a / (st.mass + a)) * p.R / ((st.k : ℝ) + 1)

noncomputable def centerTolerance (p : Public.{u}) (st : OuterState p.E) (a : ℝ) : ℝ :=
  min (errorScale p st a / 64) (1 / (4096 * p.H * a))

noncomputable def endpointTolerance (p : Public.{u}) (st : OuterState p.E) (a : ℝ) : ℝ :=
  min (errorScale p st a / (64 * (1 + a * p.H * p.R))) (1 / (4096 * p.H * a))

noncomputable def trialPlan (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) (a : ℝ) :
    Program p.E (p.E × (p.E →L[ℝ] p.E)) (Trial p.E) :=
  let center := if st.k = 0 then Program.done initial else
    inversePlan (shift p * p.H) (shift p) (centerTolerance p st a) (midpoint p st a) st.point
  center.map fun sample =>
    let n := sample.1 + shift p • sample.2.1
    ⟨a, sample, modelPoint (shift p) a (anchorMix p st a) n sample.2.1 sample.2.2⟩

noncomputable def merit (p : Public.{u}) (trial : Trial p.E) : ℝ :=
  trial.step * p.H * ‖trial.model - (trial.sample.1 + shift p • trial.sample.2.1)‖

noncomputable def searchPlan (p : Public.{u}) (st : OuterState p.E)
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) :
    ℕ → ℝ → ℝ → ℝ → Program p.E (p.E × (p.E →L[ℝ] p.E)) (Option (Trial p.E))
  | 0, _, _, _ => .done none
  | fuel + 1, low, high, a => by
      classical
      exact (trialPlan p st initial a).bind fun trial =>
        if merit p trial ≤ 1 / 32 ∧ (1 / 64 ≤ merit p trial ∨ a = maxStep p) then
          .done (some trial)
        else if merit p trial < 1 / 64 then
          searchPlan p st initial fuel a high
            (if high = 0 then min (2 * a) (maxStep p) else (a + high) / 2)
        else
          searchPlan p st initial fuel low a
            (if low = 0 then max (a / 2) (baseStep p) else (low + a) / 2)

noncomputable def outerPlan (p : Public.{u})
    (initial : p.E × (p.E × (p.E →L[ℝ] p.E))) :
    ℕ → OuterState p.E → Program p.E (p.E × (p.E →L[ℝ] p.E)) p.E
  | 0, st => .done st.point
  | fuel + 1, st => by
      classical
      exact if st.k ≠ 0 ∧ ‖st.value‖ ≤ p.ε then .done st.point else
        (searchPlan p st initial (searchFuel p) 0 0 st.previous).bind fun found =>
          match found with
          | none => .done st.point
          | some trial =>
              (inversePlan (shift p * p.H) (shift p) (endpointTolerance p st trial.step)
                trial.model trial.sample.1).bind fun endpoint =>
                  if trial.step = maxStep p then .done endpoint.1 else
                    outerPlan p initial fuel
                      ⟨st.k + 1, st.mass + trial.step, trial.step, endpoint.1, endpoint.2.1⟩

noncomputable def plan (p : Public.{u}) : Program p.E (p.E × (p.E →L[ℝ] p.E)) p.E :=
  .ask p.x0 fun reply =>
    let D := ContinuousLinearMap.id ℝ p.E + shift p • reply.2
    let d := trustRegion D (shift p • reply.1) p.R
    (inversePlan (shift p * p.H) (shift p)
      (min (p.R / 64) (1 / (4096 * p.H * maxStep p))) p.x0 (p.x0 + d)).bind fun initial =>
        outerPlan p initial (horizon p) ⟨0, 0, baseStep p, initial.1, initial.2.1⟩

noncomputable def algorithm (p : Public.{u}) :
    OracleTemplate.Algorithm p.E (p.E × (p.E →L[ℝ] p.E)) p.E where
  State := Program p.E (p.E × (p.E →L[ℝ] p.E)) p.E
  initial := fun _ => plan p
  query := fun state => (0, state.query p.x0)
  update := Program.update
  output := Program.output p.x0

noncomputable def output (p : Public.{u})
    (oracle : OracleTemplate.Oracle p.E (p.E × (p.E →L[ℝ] p.E))) (K : ℕ)
    (oracleSeed : (k : ℕ) → oracle.Seed k) : p.E :=
  OracleTemplate.execute oracle (algorithm p) (fun _ => K) () oracleSeed

end LongTails.Algorithms.CohypomonotoneNewton
