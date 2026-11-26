import LongTails.Setups.TerminalClippingConvex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open LongTails.Setups.TerminalClippingConvex

namespace OracleTemplate.TerminalClippingSingleLog

noncomputable def horizon (p : Public) : ℕ :=
  if p.G * p.R ≤ p.ε then 0 else
    ⌈576 * p.R ^ 2 * (p.G ^ 2 + 16 * p.B ^ 2 * p.R ^ 2) *
      Real.log (8 / p.δ) / p.ε ^ 2⌉₊

noncomputable def momentScale (p : Public) : ℝ :=
  Real.sqrt (p.G ^ 2 + 16 * p.B ^ 2 * p.R ^ 2)

noncomputable def slope (p : Public) (T : ℕ) : ℝ :=
  max 0 p.R / (12 * momentScale p * T * Real.sqrt (T * Real.log (8 / p.δ)))

noncomputable def level (p : Public) (T : ℕ) : ℝ :=
  momentScale p * Real.sqrt (T / Real.log (8 / p.δ))

inductive State (q : Public)
  | sample (t : ℕ) (x : Vector q.d)
  | project (t : ℕ) (x proposal : Vector q.d)

noncomputable def algorithm (q : Public) : Algorithm (Query q) (Vector q.d) (Vector q.d) where
  State := State q
  initial _ := .sample 0 q.x0
  query
    | .sample _ x => (0, .subgradient x)
    | .project _ _ w => (0, .projection w)
  update
    | .sample t x, g =>
      let T := horizon q
      .project t x (x - (slope q T * (T - t : ℕ)) •
        clipReply (if t < T then level q T else 0) g)
    | .project t _ _, x => .sample (t + 1) x
  output
    | .sample _ x | .project _ x _ => x

end OracleTemplate.TerminalClippingSingleLog
