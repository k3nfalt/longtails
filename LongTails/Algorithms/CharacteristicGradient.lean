import LongTails.Setups.QuantileSymmetricRemainderConvex
import LongTails.Algorithms.Batched
import LongTails.Algorithms.AcceleratedBiasedStochastic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Exponential

namespace LongTails.Algorithms.CharacteristicGradient

noncomputable def phaseIncrement (t y : ℝ) : ℂ :=
  1 - Complex.exp (Complex.I * ((t * y : ℝ) : ℂ))

noncomputable def logPolynomial {K : ℕ} (u : Fin K → ℂ) : ℂ :=
  ∑ k : Fin K, (∏ j ∈ Finset.Iic k, u j) / ((k.val : ℂ) + 1)

noncomputable def coordinateEstimate {K : ℕ} (t : ℝ) (replies : Fin K → ℝ) : ℝ :=
  -(logPolynomial (fun j => phaseIncrement t (replies j))).im / t

noncomputable def batchEstimate {d K : ℕ} (t : ℝ)
    (replies : Fin K → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => coordinateEstimate t (fun j => replies j i)

noncomputable def batchedOracle {d K : ℕ} {Ω : Type}
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (ξ : Fin K → Ω) : EuclideanSpace ℝ (Fin d) :=
  batchEstimate t (fun j => g x (ξ j))

noncomputable def output {d K : ℕ} {Ω : Type}
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (D R t : ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (N : ℕ) (ξ : Fin N → Fin K → Ω) :
    EuclideanSpace ℝ (Fin d) :=
  (OracleTemplate.BiasedStochasticGradient.projectedRun (batchedOracle g t) D R x0 N 0 x0 x0 ξ).1

noncomputable def algorithm {d K : ℕ} (hK : 0 < K) (D R t : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) :
    OracleTemplate.Algorithm (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  OracleTemplate.batched hK (OracleTemplate.BiasedStochasticGradient.projectedAccelerated D R x0)
    (fun s _ => OracleTemplate.Gradient.acceleratedQuery s)
    (fun _ replies => batchEstimate t replies) 0

open LongTails.Setups.QuantileSymmetricRemainderConvex

noncomputable def scale (q : Params) : ℝ :=
  8 * (2 * q.L * q.R + q.r) + 64 * Real.sqrt q.d * q.M * q.R / q.ε

noncomputable def shape (q : Params) : ℝ :=
  Real.sqrt q.d * q.R * (2 * q.L * q.R + q.r) / q.ε +
    8 * q.d * q.M * q.R ^ 2 / q.ε ^ 2

noncomputable def batchCount (q : Params) : ℕ :=
  1 + ⌈Real.log (1 + 512 * shape q) / Real.log 2⌉₊

noncomputable def iterationCount (q : Params) : ℕ :=
  1 + ⌈4 * Real.sqrt (q.L * q.R ^ 2 / q.ε) + 32768 * (shape q) ^ 2⌉₊

noncomputable def curvature (q : Params) : ℝ :=
  2 * q.L + 64 * iterationCount q * q.d * (scale q) ^ 2 / q.ε

noncomputable def tunedAlgorithm (q : Params) :
    OracleTemplate.Algorithm (Space q.d) (Space q.d) (Space q.d) :=
  algorithm (K := batchCount q) (by unfold batchCount; omega)
    (curvature q) q.R (1 / scale q) q.x0

end LongTails.Algorithms.CharacteristicGradient
