import LongTails.Setups.StochasticPowerSmoothFixedPoint
import LongTails.Algorithms.RecursiveAnchorKm

namespace LongTails.Algorithms.PowerSmoothAnchoring

open OracleTemplate
open LongTails.Setups.StochasticPowerSmoothFixedPoint

noncomputable def levels (q : Params) : ℕ := Nat.clog 2 (⌈16 * q.D / q.ε⌉₊ + 1)

noncomputable def strength (q : Params) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j / (2 : ℝ) ^ levels q

noncomputable def relaxation (q : Params) : ℝ :=
  1 / (1 + (2 : ℝ) ^ levels q +
    (65536 * q.K * (q.σ / q.ε) ^ q.exponent * (levels q + 1 : ℝ) ^ q.exponent) ^
      (1 / (q.exponent - 1)))

noncomputable def innerSteps (q : Params) : ℕ :=
  ⌈8 * (levels q + 1 : ℝ) / relaxation q⌉₊

noncomputable def anchorWeight (q : Params) (j : ℕ) : ℝ :=
  if j = 0 then strength q 0 else strength q (j - 1)

noncomputable def stageStep (q : Params) (j : ℕ) : ℝ :=
  relaxation q * (1 + strength q j) / strength q j

noncomputable def algorithm (q : Params) : Algorithm q.E q.E q.E :=
  RecursiveAnchorKm.recursiveAnchorKm (levels q) (anchorWeight q) (strength q)
    (stageStep q) (fun _ => innerSteps q) q.x0

noncomputable def output (q : Params) (O : Oracle q.E q.E)
    (budget : Fin 1 → ℕ) (ξ : (k : ℕ) → O.Seed k) : q.E :=
  execute O (algorithm q) budget () ξ

end LongTails.Algorithms.PowerSmoothAnchoring
