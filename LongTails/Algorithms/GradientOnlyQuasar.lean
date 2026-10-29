import LongTails.Setups.GradientOnlyGeneralizedQuasar
import LongTails.Algorithms.RelativeQuasar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

noncomputable section

def smoothRamp (s : ℝ) : ℝ :=
  2 * (max 0 s) ^ 2 - 4 * (max 0 (s - 1 / 2)) ^ 2 + 2 * (max 0 (s - 1)) ^ 2

def smoothRampSlope (s : ℝ) : ℝ :=
  4 * max 0 s - 8 * max 0 (s - 1 / 2) + 4 * max 0 (s - 1)

def momentOrder (q : Params) : ℕ := 1 + Nat.clog 2 ⌈4 / q.δ⌉₊

def stageCount (q : Params) : ℕ := Nat.clog 2 ⌈8 * q.Δ / q.ε⌉₊

def initialWeight (q : Params) : ℝ := q.R ^ 2 / (2 * q.Δ)

def energyLevel (q : Params) : ℝ := 2 * q.R ^ 2

def stageWeight (q : Params) (j : ℕ) : ℝ := (2 : ℝ) ^ j * initialWeight q

def stageDuration (q : Params) (j : ℕ) : ℝ :=
  256 * momentOrder q / q.γ * Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q)

def stageStart (q : Params) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, stageDuration q i

def weight (q : Params) (t : ℝ) : ℝ := initialWeight q +
  ∑ j ∈ Finset.range (stageCount q),
    stageWeight q j * smoothRamp ((t - stageStart q j) / stageDuration q j)

def mirrorStep (q : Params) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (stageCount q), stageWeight q j /
    stageDuration q j * smoothRampSlope ((t - stageStart q j) / stageDuration q j)) / q.γ

def curvature (q : Params) (t : ℝ) : ℝ :=
  128 * (q.L0 + q.L1 ^ 2 * energyLevel q / weight q t)

def calls (q : Params) : ℕ := ⌈65536 * (1 + Nat.clog 2 ⌈4 / q.δ⌉₊) * (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * (1 + Nat.clog 2 ⌈8 * q.Δ / q.ε⌉₊)) / q.γ⌉₊

def flow (q : Params) (s : ℝ × q.E × q.E) (h : ℝ) : ℝ × q.E × q.E :=
  (s.1 + h,
    s.2.2 + (weight q s.1 / weight q (s.1 + h)) ^ (1 / q.γ) • (s.2.1 - s.2.2),
    s.2.2)

def jump (q : Params) (s : ℝ × q.E × q.E) (v : q.E) : ℝ × q.E × q.E :=
  (s.1, s.2.1 - (1 / curvature q s.1) • v, s.2.2 - mirrorStep q s.1 • v)

def advance (q : Params) (g : q.E → q.E) (s : ℝ × q.E × q.E) (h : ℝ) :
    ℝ × q.E × q.E :=
  let y := flow q s (max 0 h)
  jump q y (g y.2.1)

def run (q : Params) (g : q.E → q.E) (k : ℕ) (s : ℝ × q.E × q.E)
    (samples : Fin k → ℝ) : ℝ × q.E × q.E :=
  ContinuizedSimilarQuasar.iterateSamples (advance q g) k s samples

def plan (q : Params) : (k : ℕ) → (ℝ × q.E × q.E) → (Fin k → ℝ) →
    QueryPlan q.E q.E (ℝ × q.E × q.E) k
  | 0, s, _ => .done s
  | k + 1, s, samples =>
      let y := flow q s (max 0 (samples 0))
      .ask y.2.1 (fun v => plan q k (jump q y v) (fun i => samples i.succ))

def accelerated (q : Params) : Algorithm q.E q.E q.E :=
  QueryPlan.algorithm (RelativeQuasar.samplesLaw (calls q)) q.x0 q.x0 (calls q)
    (fun samples => QueryPlan.map (fun s => s.2.1)
      (plan q (calls q) (0, q.x0, q.x0) samples))

def output (q : Params) (O : Oracle q.E q.E)
    (seed : (accelerated q).Seed × ((k : ℕ) → O.Seed k)) : q.E :=
  execute O (accelerated q) (fun _ => calls q) seed.1 seed.2

end

end OracleTemplate.GradientOnlyQuasar
