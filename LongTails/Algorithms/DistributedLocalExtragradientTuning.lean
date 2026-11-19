import LongTails.Algorithms.DistributedLocalExtragradientWarmStart
import LongTails.Algorithms.DistributedLocalExtragradientProcess
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.DistributedLocalExtragradientTuning

open LongTails.Setups.DistributedJacobianStrongGrowth

noncomputable def growth (p : Params) : ℝ := 2 + p.ρ / 8 + p.ρ ^ 2 / 128

noncomputable def localDepth (p : Params) : ℕ :=
  min ⌊p.L / p.μ⌋₊ ⌊Real.log ((p.n : ℝ) / (64 * (p.L / p.μ))) / Real.log (growth p)⌋₊

noncomputable def radius (p : Params) (T : ℕ) : ℝ :=
  p.L * p.R / (p.L + 32 * (p.L / p.μ) * p.ρ * growth p ^ T * p.M * p.R)

noncomputable def contraction (p : Params) (T : ℕ) : ℝ := T / (64 * (p.L / p.μ))

noncomputable def clipRadius (p : Params) (T : ℕ) : ℝ :=
  256 * (p.L / p.μ) * (growth p ^ T + 1) * radius p T / T

noncomputable def warmSpacing (p : Params) (T : ℕ) : ℝ := radius p T / (8 * Real.sqrt p.d)

noncomputable def warmWidth (p : Params) (T : ℕ) : ℕ :=
  Nat.log2 ⌈2 * p.R / warmSpacing p T⌉₊ + 1

noncomputable def warmCount (p : Params) (T : ℕ) : ℕ :=
  ⌈p.ρ * (p.L / p.μ) ^ 2 * (Real.log (64 * p.d * p.R ^ 2 / radius p T ^ 2) +
    (2 / (p.n : ℝ)) * Real.log (8 * p.R ^ 2 / p.ε ^ 2))⌉₊

noncomputable def refinementSpacing (p : Params) (T : ℕ) : ℝ :=
  p.ε * contraction p T / (8 * Real.sqrt p.d)

noncomputable def refinementWidth (p : Params) (T : ℕ) : ℕ :=
  Nat.log2 ⌈2 * clipRadius p T / refinementSpacing p T⌉₊ + 1

noncomputable def refinementCount (p : Params) (T : ℕ) : ℕ :=
  ⌈(2 / contraction p T) * Real.log (4 * radius p T ^ 2 / p.ε ^ 2)⌉₊

noncomputable def output (p : Params) (T : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) : Point p :=
  DistributedLocalExtragradientProcess.refineRun p (warmCount p T) T (clipRadius p T)
    (refinementWidth p T) (refinementSpacing p T) (radius p T) g
    (DistributedLocalExtragradientWarmStart.warmCenter p (warmCount p T) (warmWidth p T)
      (warmSpacing p T) g samples) samples (refinementCount p T)

noncomputable def baselineCount (p : Params) : ℕ :=
  ⌈p.ρ * (p.L / p.μ) ^ 2 * Real.log (p.R ^ 2 / p.ε ^ 2)⌉₊

noncomputable def baselineOutput (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) : Point p :=
  LocalNonlinearExtragradient.warmRun (p.μ / (p.ρ * p.L ^ 2)) (g p.root) p.x0
    (fun j => samples (p.n * j + p.root.val)) (baselineCount p)

noncomputable def selectedOutput (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) : Point p :=
  if p.R ≤ p.ε then p.x0
  else if 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) then output p (localDepth p) g samples
  else baselineOutput p g samples

end LongTails.Algorithms.DistributedLocalExtragradientTuning
