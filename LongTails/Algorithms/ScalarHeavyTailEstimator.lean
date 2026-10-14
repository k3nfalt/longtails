import LongTails.Algorithms.RobustGradientEstimator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.ScalarHeavyTailEstimator

noncomputable def radius (σ p u : ℝ) : ℝ :=
  2 * (256 * (σ + u) ^ p / u) ^ (1 / (p - 1))

noncomputable def batchSize (σ p u : ℝ) : ℕ :=
  1 + ⌈16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2⌉₊

noncomputable def blockSize (σ p u : ℝ) : ℕ := by
  classical
  exact if 128 * σ ≤ u then 1 else 1 + batchSize σ p u

noncomputable def block (σ p u : ℝ) (samples : ℕ → ℝ) : ℝ := by
  classical
  exact if 128 * σ ≤ u then samples 0 else
    (1 / (batchSize σ p u : ℝ)) *
      ∑ i : Fin (batchSize σ p u),
        RobustGradient.centeredClip (radius σ p u) (samples 0) (samples (i + 1))

noncomputable def estimate (σ p u : ℝ) (k : ℕ) (samples : ℕ → ℝ) : ℝ :=
  RobustGradient.pilotCenter (6 * u) (fun i : Fin k =>
    block σ p u (fun j => samples (i * blockSize σ p u + j)))

noncomputable def noiseLevel (σ u : ℝ) : ℕ :=
  ⌈Real.logb 2 (max 1 (128 * σ / u))⌉₊

noncomputable def repetitions (σ u : ℝ) (j : ℕ) : ℕ :=
  1 + 32 * (j + 1) / (1 + (j - noiseLevel σ u))

noncomputable def calls (σ p u : ℝ) (k : ℕ) : ℕ := k * blockSize σ p u

end OracleTemplate.ScalarHeavyTailEstimator
