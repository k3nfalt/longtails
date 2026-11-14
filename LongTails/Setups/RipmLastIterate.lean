import LongTails.Setups.RipmGeneral

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Setups.RipmLastIterate

noncomputable section

structure Params where
  d : ℕ
  m : ℕ
  x0 : Core.Vec d
  xstar : Core.Vec d
  L : ℝ
  Lg : ℝ
  D2 : ℝ
  Delta : ℝ
  S : ℝ
  epsilon : ℝ

def valid (p : Params) : Prop :=
  0 < p.m ∧ 0 < p.L ∧ 0 ≤ p.Lg ∧ 0 ≤ p.D2 ∧ 0 ≤ p.Delta ∧
    0 ≤ p.S ∧ 0 < p.epsilon

def boundScale (p : Params) : ℝ :=
  p.L * p.D2 + p.Delta + (p.S + 4 * (p.m : ℝ) ^ 2 * p.Lg ^ 2) / p.L

def horizon (p : Params) : ℕ :=
  ⌈(64 * (1 + 10 * boundScale p / p.epsilon) *
    (1 + Real.log (1 + 10 * boundScale p / p.epsilon))) ^ 2⌉₊

def step (p : Params) : ℝ :=
  1 / (5 * p.L * Real.sqrt (horizon p))

def publicInput (p : Params) : Core.Public :=
  ⟨p.d, p.m, p.x0, step p⟩

def admissible (p : Params) (I : Core.Problem p.d p.m)
    (O : OracleTemplate.Oracle (ℝ × Core.Vec p.d) (Core.Vec p.d) 2) : Prop :=
  ∃ sigmaSq decodeI decodeJ,
    Core.SourceAssumptions I p.L p.Lg p.xstar sigmaSq ∧ sigmaSq ≤ p.S ∧
    ‖p.x0 - p.xstar‖ ^ 2 ≤ p.D2 ∧ Core.objective I p.x0 - Core.objective I p.xstar ≤ p.Delta ∧
    Core.OracleExact I O decodeI decodeJ ∧ Core.OracleSamples I O (step p) p.x0 decodeI decodeJ

def spec : OracleTemplate.Setup where
  numOracles := 2
  Params := Params
  Public := Core.Public
  Instance p := Core.Problem p.d p.m
  Query p := ℝ × Core.Vec p.d
  Reply p := Core.Vec p.d
  Output p := Core.Vec p.d
  publicInput := publicInput
  valid := valid
  admissible := admissible
  successful := fun p I output P =>
    Measurable output ∧
    Integrable (fun omega => Core.objective I (output omega) - Core.objective I p.xstar)
      (P : Measure _) ∧
    (∫ omega, Core.objective I (output omega) - Core.objective I p.xstar ∂(P : Measure _)) ≤ p.epsilon
  allowedAlgorithm := fun p A => A = Core.method p

end

end LongTails.Setups.RipmLastIterate
