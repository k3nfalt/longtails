import LongTails.Setups.GeneralCovarianceReverseFisher
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open OracleTemplate

namespace LongTails.Algorithms.GeneralCovarianceReverseFisherGD

open LongTails.Setups.GeneralCovarianceReverseFisher

noncomputable def stepSize (p : Params) : ℝ :=
  p.components * p.lower ^ 2 / (2 * (1 + 8 * Real.log p.components))

noncomputable def algorithm (p : Params) : Algorithm (Means p) (Means p) (Means p) where
  State := Means p
  initial _ := WithLp.toLp 2 p.start
  query θ := (0, θ)
  update θ g := θ - stepSize p • g
  output θ := θ

noncomputable def output (p : Params) (oracle : Oracle (Means p) (Means p)) (K : ℕ)
    (oracleSeed : (k : ℕ) → oracle.Seed k) : Means p :=
  execute oracle (algorithm p) (fun _ => K) () oracleSeed

end LongTails.Algorithms.GeneralCovarianceReverseFisherGD
