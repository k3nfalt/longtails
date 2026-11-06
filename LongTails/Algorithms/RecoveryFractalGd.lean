import LongTails.Algorithms.FractalChebyshevSteps
import LongTails.Setups.SmoothHessianLipschitzGd
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.RecoveryFractalGd

open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd

noncomputable def scaledGap (p : Params) : ℝ := p.L * p.Δ / p.ε ^ 2

noncomputable def curvatureScale (p : Params) : ℝ := p.ρ * p.ε / p.L ^ 2

def admissibleLevel (p : Params) (k : ℕ) : Prop :=
  2 ≤ k ∧ (2 ^ k : ℝ) ^ 2 ≤ scaledGap p ∧
    curvatureScale p * (k + 8 : ℝ) ^ 2 * (2 ^ k : ℝ) ^ 6 ≤ 1 / 2 ^ 28 ∧
    2 ^ 16 * curvatureScale p * (k + 8 : ℝ) ^ 2 *
      (2 ^ k : ℝ) ^ (17 / 2 : ℝ) ≤ scaledGap p

open Classical in
noncomputable def level (p : Params) : ℕ :=
  Nat.findGreatest (admissibleLevel p) (Nat.log2 ⌈scaledGap p⌉₊)

noncomputable def blockLength (p : Params) : ℕ := 2 ^ level p

noncomputable def repetitions (p : Params) : ℕ := level p + 8

noncomputable def epochLength (p : Params) : ℕ := blockLength p * repetitions p

noncomputable def lowerCurvature (p : Params) : ℝ := p.L / (blockLength p : ℝ) ^ 2

noncomputable def threshold (p : Params) : ℝ := Real.sqrt (blockLength p) * p.ε

noncomputable def radius (p : Params) : ℝ :=
  32 * repetitions p * threshold p / lowerCurvature p

noncomputable def errorBound (p : Params) : ℝ := p.ρ * radius p ^ 2

noncomputable def prefixIncrease (p : Params) : ℝ :=
  64 * epochLength p * threshold p * errorBound p / lowerCurvature p +
    2 * repetitions p * errorBound p ^ 2 / lowerCurvature p + p.ρ * radius p ^ 3

noncomputable def recoveryTarget (p : Params) : ℝ :=
  4 * p.L * prefixIncrease p + 16 * epochLength p * threshold p ^ 2

noncomputable def fractalStep (p : Params) (i : ℕ) : ℝ :=
  FractalChebyshev.stepOf p.L (lowerCurvature p)
    ((FractalChebyshev.angles (level p)).getD (i % blockLength p) 0)

structure Control where
  phase : ℕ
  recovering : Bool
  recoverySum : ℝ

def idle : Control := ⟨0, false, 0⟩

open Classical in
noncomputable def recoveryControl (p : Params) (total : ℝ) : Control :=
  if recoveryTarget p ≤ total then idle else ⟨0, true, total⟩

open Classical in
noncomputable def rule (p : Params) (c : Control) (reply : p.E) : ℝ × Control :=
  if level p < 2 then (1 / p.L, idle)
  else if c.recovering then
    (1 / p.L, recoveryControl p (c.recoverySum + ‖reply‖ ^ 2))
  else if c.phase ≠ 0 ∧ 8 * threshold p < ‖reply‖ then
    (1 / p.L, recoveryControl p (‖reply‖ ^ 2))
  else if c.phase = 0 ∨ 2 * epochLength p ≤ c.phase then
    if threshold p < ‖reply‖ then (1 / p.L, idle)
    else (fractalStep p 0, ⟨1, false, 0⟩)
  else (fractalStep p c.phase, ⟨c.phase + 1, false, 0⟩)

structure State (E : Type*) where
  point : E
  best : E
  bestNorm : ℝ
  count : ℕ
  control : Control

open Classical in
noncomputable def method (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := ⟨p.x0, p.x0, 0, 0, idle⟩
  query s := (0, s.point)
  update s reply :=
    ⟨s.point - (rule p s.control reply).1 • reply,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then s.point else s.best,
      if s.count = 0 ∨ ‖reply‖ ^ 2 ≤ s.bestNorm then ‖reply‖ ^ 2 else s.bestNorm,
      s.count + 1, (rule p s.control reply).2⟩
  output s := s.best

end LongTails.Algorithms.RecoveryFractalGd
