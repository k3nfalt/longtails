import LongTails.Algorithms.StochasticQuasarAcceleration
import LongTails.Setups.StochasticConstrainedQuasar

namespace OracleTemplate.StochasticQuasar

open LongTails.Setups.StochasticConstrainedQuasar

noncomputable def outerOrder (q : Params) : ℕ := 2 + ⌈8 * Real.log (8 / q.δ)⌉₊

noncomputable def outerDamping (q : Params) : ℝ := 1 / (4096 * outerOrder q)

noncomputable def outerStep (q : Params) : ℝ := 1 / (8192 * outerOrder q * q.L)

noncomputable def outerScale (q : Params) : ℝ := q.γ ^ 2 / (134217728 * (outerOrder q : ℝ) ^ 2 * q.L)

noncomputable def outerHorizon (q : Params) : ℝ :=
  65536 * outerOrder q * Real.sqrt (q.L * q.D ^ 2 / q.ε) / q.γ

noncomputable def outerCount (q : Params) : ℕ := ⌈8 * outerHorizon q + 8 * outerOrder q⌉₊

noncomputable def outerWeight (q : Params) (t : ℝ) : ℝ :=
  accelerationWeight (1 / (4 * q.L)) (outerScale q) (outerHorizon q) t

noncomputable def outerMirror (q : Params) (t : ℝ) : ℝ :=
  accelerationWeightSlope (outerScale q) (outerHorizon q) t / q.γ

noncomputable def outerThreshold (q : Params) (t : ℝ) : ℝ :=
  256 * q.D * Real.sqrt (q.L / outerWeight q t)

noncomputable def outerDeviation (q : Params) : ℝ :=
  Real.sqrt (q.γ * Real.sqrt q.L * q.ε * Real.sqrt q.ε / (1048576 * q.D))

noncomputable def outerBias (q : Params) : ℝ := q.γ * q.ε / (1048576 * q.D)

noncomputable def outputRadius (q : Params) : ℝ := Real.sqrt (q.ε / (110592 * q.L))

noncomputable def outputBatch (q : Params) : ℕ := max 1 ⌈147456 * q.σ ^ 2 * q.D ^ 2 / q.ε ^ 2⌉₊

end OracleTemplate.StochasticQuasar
