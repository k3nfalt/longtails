import LongTails.Setups.GeneralizedLipschitzMinty
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Setups.HighDimensionalGeneralizedMinty

open OracleTemplate

abbrev spec : Setup := { GeneralizedLipschitzMinty.spec with
  valid := fun p =>
    let T := p.R * (p.L0 / p.ε + p.L1)
    GeneralizedLipschitzMinty.spec.valid p ∧ 1024 ≤ T ∧
      32 * Real.log (1 + p.L1 * p.ε / p.L0) ≤ p.L1 * p.R ∧
      8192 * (1 + ⌊(T / 1024) ^ 2⌋₊) ^ 3 ≤ p.d }

end LongTails.Setups.HighDimensionalGeneralizedMinty
