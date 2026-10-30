import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LongTails.Algorithms.RobustValue
import LongTails.Algorithms.RobustGradientEstimator

open scoped BigOperators NNReal

namespace LongTails.Algorithms.GeneralizedLipschitzPilot

structure Config where
  rawCount : ℕ
  scales : ℕ
  momentCount : ℕ
  depth : ℕ
  meanCount : ℕ
  repetitions : ℕ
  updateCount : ℕ

def Config.scaleCalls (c : Config) : ℕ := 3 ^ c.depth * c.momentCount + c.repetitions * c.meanCount

def Config.calls (c : Config) : ℕ := c.rawCount + c.scales * c.scaleCalls + c.updateCount

noncomputable def tuning (κ δ : ℝ) : Config :=
  let n := max 1 ⌈16 * κ * Real.log (9 / δ)⌉₊
  let K := 2 * κ + Real.sqrt (9 * (n : ℝ) / δ)
  let J := ⌈Real.log (2 * K) / Real.log 2⌉₊ + 2
  { rawCount := n
    scales := J
    momentCount := max 1 ⌈67108864 * κ⌉₊
    depth := Nat.clog 2 ⌈Real.log (3 * (J : ℝ) / δ) / Real.log 4⌉₊
    meanCount := max 1 ⌈9216 * κ⌉₊
    repetitions := max 1 ⌈Real.log (3 * (J : ℝ) / δ) / Real.log 2⌉₊
    updateCount := max 1 ⌈16 * κ⌉₊ }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rawMaximum {n : ℕ} (samples : Fin n → E) : ℝ :=
  (Finset.univ.sup (fun i => ‖samples i‖₊) : ℝ≥0)
noncomputable def rawScale {n : ℕ} (G0 : ℝ) (samples : Fin n → E) : ℝ :=
  2 * max G0 (rawMaximum samples)

noncomputable def momentReply (B : ℝ) (n depth : ℕ)
    (samples : OracleTemplate.FiniteVariance.TreeSample (Fin n → E) depth) : ℝ :=
  OracleTemplate.FiniteVariance.treeValue
    (fun z : Fin n → E => (∑ i, ‖OracleTemplate.clip B (z i)‖ ^ 2) / n)
    depth samples

noncomputable def meanReply (B m : ℝ) (n r : ℕ) (samples : Fin r → Fin n → E) : E :=
  OracleTemplate.RobustGradient.pilotCenter (m / 16)
    (fun j => (1 / (n : ℝ)) • ∑ i, OracleTemplate.clip B (samples j i))

noncomputable def scale (G0 initial : ℝ) (j : ℕ) : ℝ :=
  max G0 (initial / 2 ^ j)

inductive Decision where
  | terminal
  | update (index : ℕ)
  | exhausted
  deriving DecidableEq

noncomputable def select (G0 initial κ : ℝ) (moments : ℕ → ℝ) (means : ℕ → E)
    (index : ℕ) : ℕ → Decision
  | 0 => .exhausted
  | remaining + 1 =>
    let m := scale G0 initial index
    if m ≤ 64 * G0 then .terminal
    else if κ * m ^ 2 / 32 ≤ moments index ∨ m / 4 ≤ ‖means index‖ then .update index
    else select G0 initial κ moments means (index + 1) remaining

section Execution

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
noncomputable def blockMoment (c : Config) (κ G0 initial : ℝ) (data : ℕ → F) (j : ℕ) : ℝ :=
  let B := 256 * κ * scale G0 initial j
  OracleTemplate.FiniteVariance.blockValue
    (fun (_ : Unit) leaf =>
      (∑ i : Fin c.momentCount,
        ‖OracleTemplate.clip B (data (c.rawCount + j * c.scaleCalls + leaf * c.momentCount + i))‖ ^ 2) /
        c.momentCount) c.depth () 0

noncomputable def blockMean (c : Config) (κ G0 initial : ℝ) (data : ℕ → F) (j : ℕ) : F :=
  let m := scale G0 initial j
  meanReply (256 * κ * m) m c.meanCount c.repetitions
    (fun k i => data (c.rawCount + j * c.scaleCalls + 3 ^ c.depth * c.momentCount + k * c.meanCount + i))

noncomputable def blockDecision (c : Config) (κ G0 : ℝ) (data : ℕ → F) : Decision :=
  let initial := rawScale G0 (fun i : Fin c.rawCount => data i)
  select G0 initial κ (blockMoment c κ G0 initial data) (blockMean c κ G0 initial data) 0 c.scales

noncomputable def blockUpdate (c : Config) (center : F) (R G G0 κ : ℝ)
    (state : F × Bool) (data : ℕ → F) : F × Bool :=
  if state.2 then state
  else
    match blockDecision c κ G0 data with
    | .terminal => (state.1, true)
    | .exhausted => (state.1, true)
    | .update j =>
      let initial := rawScale G0 (fun i : Fin c.rawCount => data i)
      let m := scale G0 initial j
      let v := (1 / (c.updateCount : ℝ)) •
        ∑ i : Fin c.updateCount, data (c.rawCount + c.scales * c.scaleCalls + i)
      (center + OracleTemplate.clip R (state.1 - (1 / (128 * G * m)) • v - center), false)

noncomputable def blockAlgorithm (c : Config) (center : F) (R G G0 κ : ℝ) :
    OracleTemplate.Algorithm F (Fin c.calls → F) F where
  State := F × Bool
  initial _ := (center, false)
  query s := (0, s.1)
  update s reply := blockUpdate c center R G G0 κ s (fun k => if h : k < c.calls then reply ⟨k, h⟩ else 0)
  output s := s.1

noncomputable def burninAlgorithm (c : Config) (hc : 0 < c.calls)
    (center : F) (R G G0 κ : ℝ) : OracleTemplate.Algorithm F F F :=
  OracleTemplate.batched hc (blockAlgorithm c center R G G0 κ)
    (fun (s : F × Bool) _ => s.1) (fun _ reply => reply) (0 : F)

noncomputable def burninOutput (c : Config) (hc : 0 < c.calls)
    (center : F) (R G G0 κ : ℝ) (T : ℕ) (O : OracleTemplate.Oracle F F)
    (ω : (k : ℕ) → O.Seed k) : F :=
  OracleTemplate.execute O (burninAlgorithm c hc center R G G0 κ) (fun _ => T * c.calls) () ω

end Execution

end LongTails.Algorithms.GeneralizedLipschitzPilot
