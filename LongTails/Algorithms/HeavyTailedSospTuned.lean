import LongTails.Algorithms.HeavyTailedSosp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.HeavyTailedSospTuned

open LongTails.Setups.HeavyTailedHessianVector

noncomputable def accuracy (p : Params) : ℝ := p.ε / 25
noncomputable def curvature (p : Params) : ℝ := Real.sqrt (p.ρ * accuracy p)
noncomputable def stepSize (p : Params) : ℝ := accuracy p / (100 * (p.L + curvature p))
noncomputable def ncLength (p : Params) : ℝ := curvature p / p.ρ
noncomputable def errorScale (p : Params) : ℝ := accuracy p / 10000
noncomputable def conjugate (p : Params) : ℝ := p.p / (p.p - 1)
noncomputable def momentConstant (p : Params) : ℝ := 144 * conjugate p
noncomputable def cycleCount (p : Params) : ℕ := max 1 ⌈100 * p.Δ / (stepSize p * accuracy p)⌉₊
noncomputable def resetScale (p : Params) : ℝ := 1 + momentConstant p * p.σg / errorScale p
noncomputable def transportNoise (p : Params) : ℝ := 7 * (p.σh + p.ρ * stepSize p)
noncomputable def transportScale (p : Params) : ℝ := momentConstant p * transportNoise p * stepSize p / errorScale p
noncomputable def epochCount (p : Params) : ℕ := max 1 ⌊(cycleCount p : ℝ) * resetScale p / (resetScale p + cycleCount p * transportScale p)⌋₊
noncomputable def resetBatch (p : Params) : ℕ := ⌈resetScale p ^ conjugate p⌉₊
noncomputable def transportBatch (p : Params) : ℕ := 1 + ⌈(epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p⌉₊
noncomputable def probeConstant (p : Params) : ℝ := (4 : ℝ) ^ (-conjugate p) / 16
noncomputable def dimensionScale (p : Params) : ℝ := 4 * (Real.log (2 * Real.sqrt (2 * p.d)) + 2)
noncomputable def spectralStep (p : Params) : ℝ := 1 / (2 * p.L + curvature p + (256 * dimensionScale p * p.σh ^ p.p / (probeConstant p * curvature p)) ^ (1 / (p.p - 1)))
noncomputable def probeSteps (p : Params) : ℕ := ⌈2 * dimensionScale p / (spectralStep p * curvature p)⌉₊
noncomputable def missRisk (p : Params) : ℝ := stepSize p * accuracy p / (100 * (p.L + curvature p) * ncLength p ^ 2)
noncomputable def repeatCount (p : Params) : ℕ := ⌈(4 / probeConstant p) * Real.log (2 / missRisk p)⌉₊
noncomputable def validationBatch (p : Params) : ℕ := max 1 ⌈(6 * p.σh ^ p.p / (curvature p / 8) ^ p.p) ^ (1 / (p.p - 1))⌉₊
noncomputable def validationGroups (p : Params) : ℕ := 2 * ⌈4 * Real.log (2 * repeatCount p / missRisk p)⌉₊ + 1
noncomputable def ncSegments (p : Params) : ℕ := ⌈ncLength p / stepSize p⌉₊

noncomputable def config (p : Params) : HeavyTailedSosp.Config where
  cycles := cycleCount p
  epoch := epochCount p
  resetBatch := resetBatch p
  transportBatch := transportBatch p
  probeSteps := probeSteps p
  repeats := repeatCount p
  meanBatch := validationBatch p
  groups := validationGroups p
  ncSegments := ncSegments p
  h := stepSize p
  s := ncLength p
  η := spectralStep p
  shift := p.L + curvature p
  γ := curvature p

end LongTails.Algorithms.HeavyTailedSospTuned
