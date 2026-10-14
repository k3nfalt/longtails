import LongTails.Setups.GapSmoothStrongGrowth
import LongTails.Algorithms.Clipping
import LongTails.Algorithms.StochasticGeneralizedAccelerated

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

noncomputable def confidence (p : Params) : ℝ := 128 * (1 + |Real.log p.δ|)

noncomputable def increment (p : Params) (A : ℝ) : ℝ :=
  A / (32768 * confidence p * (1 + p.R * Real.sqrt p.H1 + Real.sqrt (p.H0 * A)))

noncomputable def weight (p : Params) : ℕ → ℝ
  | 0 => p.R ^ 2 / p.Δ
  | n + 1 => weight p n + increment p (weight p n)

noncomputable def batchSize (p : Params) : ℕ := ⌈p.ρ⌉₊

noncomputable def queryPoint (p : Params) (n : ℕ) (s : p.E × p.E) : p.E :=
  let A := weight p n
  let a := increment p A
  (A / (A + a)) • s.1 + (a / (A + a)) • s.2

noncomputable def step (p : Params) (n : ℕ) (s : p.E × p.E) (v : p.E) : p.E × p.E :=
  let A := weight p n
  let a := increment p A
  let h := clip (p.R / (confidence p * a)) v
  (queryPoint p n s - (32 * confidence p * a ^ 2 / (A + a)) • h, s.2 - a • h)

abbrev State (E : Type*) := ℕ × (E × E) × ℕ × E

noncomputable def algorithm (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := (0, (p.x0, p.x0), 0, 0)
  query s := (0, queryPoint p s.1 s.2.1)
  update s reply :=
    if s.2.2.1 + 1 < batchSize p then
      (s.1, s.2.1, s.2.2.1 + 1, s.2.2.2 + reply)
    else
      (s.1 + 1, step p s.1 s.2.1 ((1 / (batchSize p : ℝ)) • (s.2.2.2 + reply)), 0, 0)
  output s := s.2.1.1

noncomputable def run (p : Params) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → Fin (batchSize p) → p.Ω) : ℕ → p.E × p.E
  | 0 => (p.x0, p.x0)
  | n + 1 =>
    let s := run p g ξ n
    step p n s (StochasticGeneralized.batchReply g (queryPoint p n s) (ξ n))

end OracleTemplate.GapStrongGrowth
