import LongTails.Algorithms.AdaptivePairedZerothOrder
import LongTails.Algorithms.ClippedTwoPointWork
import LongTails.Algorithms.QueryLayers

namespace LongTails.Algorithms.AdaptivePairedZerothOrderWork

open LongTails.Setups.AdaptivePairedZerothOrder
open LongTails.Algorithms.ClippedTwoPointWork

structure Tuning where
  A : ℝ
  scale : ℝ
  τ : ℝ
  h : ℝ
  s : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  K : ℕ

noncomputable def minimum (a b : ℝ) : Charged ℝ := do
  let first ← realLe a b
  if first then pure a else pure b

noncomputable def preprocess (p : Public) : Charged Tuning := do
  let nr ← natReal p.N
  let tr ← natReal p.T
  let dr ← natReal p.d
  let successor ← realAdd nr 1
  let product ← realMul nr successor
  let A ← realDiv product 2
  let rootT ← realSqrt tr
  let numerator ← realMul p.ε rootT
  let dell ← realAdd dr p.ell
  let rootDell ← realSqrt dell
  let scaledD ← realMul 16777216 p.D
  let denominator ← realMul scaledD rootDell
  let scale ← realDiv numerator denominator
  let dTimesEll ← realMul dr p.ell
  let clipRatio ← realDiv tr dTimesEll
  let rootClipRatio ← realSqrt clipRatio
  let τ ← realMul scale rootClipRatio
  let squaredD ← realMul p.D p.D
  let hDenominator ← realMul 64 squaredD
  let hNumerator ← realMul p.ε A
  let h ← realDiv hNumerator hDenominator
  let validationRatio ← realDiv tr p.ell
  let rootValidationRatio ← realSqrt validationRatio
  let validationScale ← realMul scale p.D
  let s ← realMul validationScale rootValidationRatio
  let smoothCandidate ← realDiv p.D nr
  let γ₁ ← minimum p.γmax smoothCandidate
  let rootD ← realSqrt dr
  let fourthRootD ← realSqrt rootD
  let nonsmoothNumerator ← realMul fourthRootD p.D
  let nonsmoothCandidate ← realDiv nonsmoothNumerator nr
  let γ₂ ← minimum p.γmax nonsmoothCandidate
  let tCalls ← natMul 6 p.T
  let nCalls ← natMul 4 p.N
  let K ← natAdd tCalls nCalls
  pure ⟨A, scale, τ, h, s, γ₁, γ₂, K⟩

def natSub (a b : ℕ) : Charged ℕ := ⟨a - b, { operations := 1 }⟩

noncomputable def evaluate (p : Public) (seed : ℕ → Point p.d)
    (reply : ℕ → Point p.d → ℝ) : Charged (Point p.d) := do
  let tuning ← preprocess p
  let registers ← dualRun p.d p.T tuning.A tuning.τ tuning.τ tuning.γ₁ tuning.γ₂ tuning.h
    p.project ⟨((p.x0, p.x0), (p.x0, p.x0)), 0, 0⟩ seed reply p.N
  let chosen ← selection tuning.s registers.states.1.1 registers.states.2.1 reply p.T registers.call
  let validationCalls ← natMul 2 p.T
  let consumed ← natAdd registers.call validationCalls
  let remaining ← natSub tuning.K consumed
  padding p.x0 reply chosen remaining consumed

noncomputable def paddedExecutionPlan (p : Public)
    (seed : ℕ → LongTails.Algorithms.AdaptivePairedZerothOrder.Direction p) :=
  LongTails.Algorithms.QueryLayers.paddedPlan p.x0
    (LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d
      (LongTails.Algorithms.AdaptivePairedZerothOrder.clipRadius p)
      (LongTails.Algorithms.AdaptivePairedZerothOrder.clipRadius p)
      (smoothRadius p) (nonsmoothRadius p)
      (LongTails.Algorithms.AdaptivePairedZerothOrder.regularization p)
      (LongTails.Algorithms.AdaptivePairedZerothOrder.validationClip p)
      p.project (p.x0, p.x0) (LongTails.Algorithms.AdaptivePairedZerothOrder.batch p)
      (LongTails.Algorithms.AdaptivePairedZerothOrder.firstDirections p seed)
      (LongTails.Algorithms.AdaptivePairedZerothOrder.secondDirections p seed) p.N p.T)
    (6 * p.T + 4 * p.N - (2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls
      (LongTails.Algorithms.AdaptivePairedZerothOrder.batch p) p.N))

end LongTails.Algorithms.AdaptivePairedZerothOrderWork
