import LongTails.Algorithms.FairVarianceReduction

namespace OracleTemplate.FairVarianceReduction

noncomputable def tuneRadius (r ε : ℝ) : ℝ := r + ε

noncomputable def tuneScale (L r Δ ε : ℝ) : ℝ := ((r + ε) ^ 2 + L * Δ) / ε ^ 2

noncomputable def tuneStep (L ε : ℝ) : ℝ := ε / (64 * L)

noncomputable def tuneIterations (L Δ ε : ℝ) : ℕ := max 1 ⌈512 * L * Δ / ε ^ 2⌉₊

noncomputable def tunePeriod (L κ Δ ε : ℝ) : ℕ :=
  ⌈L / (κ * ε + L / tuneIterations L Δ ε)⌉₊

noncomputable def tuneGradientBound (L Δ ε : ℝ) : ℝ :=
  Real.sqrt (2 * L * Δ) + L * tuneIterations L Δ ε * tuneStep L ε

noncomputable def tuneClip (r ε : ℝ) : ℝ := 64 * (2 : ℝ) ^ 23 * (r + ε) ^ 2 / ε

noncomputable def tuneRefreshBatch (r ε : ℝ) : ℕ := ⌈(2 : ℝ) ^ 20 * (r + ε) ^ 2 / ε ^ 2⌉₊

noncomputable def tuneIncrementBatch (L κ r Δ ε : ℝ) : ℕ :=
  1 + ⌈(2 : ℝ) ^ 43 * tunePeriod L κ Δ ε * κ ^ 2 * (r + ε) ^ 2 / L ^ 2⌉₊

noncomputable def tuneBlockQuarter (L r Δ ε : ℝ) : ℕ :=
  1 + ⌈Real.log ((2 : ℝ) ^ 121 * (tuneScale L r Δ ε) ^ 3) / Real.log 4⌉₊

noncomputable def tunedConfig (L κ r Δ ε : ℝ) : Config where
  η := tuneStep L ε
  R := tuneRadius r ε
  G := tuneGradientBound L Δ ε
  B := tuneClip r ε
  T := tuneIterations L Δ ε
  q := tunePeriod L κ Δ ε
  m := 4 * tuneBlockQuarter L r Δ ε
  b0 := tuneRefreshBatch r ε
  b := tuneIncrementBatch L κ r Δ ε

end OracleTemplate.FairVarianceReduction
