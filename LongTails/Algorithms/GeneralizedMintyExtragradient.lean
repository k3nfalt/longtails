import LongTails.Setups.GeneralizedLipschitzMinty

namespace LongTails.Algorithms.GeneralizedMintyExtragradient

open OracleTemplate LongTails.Setups.GeneralizedLipschitzMinty

variable (p : Params)

abbrev E := EuclideanSpace ℝ (Fin p.d)

noncomputable def stepSize (v : E p) : ℝ :=
  if ‖v‖ ≤ p.ε then 0 else (4 * (p.L0 + p.L1 * ‖v‖))⁻¹

abbrev State := E p ⊕ (E p × ℝ × E p)

def output : State p → E p
  | .inl x => x
  | .inr (x, _, _) => x

noncomputable def algorithm : Algorithm (E p) (E p) (E p) where
  State := State p
  initial _ := .inl p.x0
  query s := (0, match s with | .inl x => x | .inr (_, _, y) => y)
  update s v := match s with
    | .inl x => let η := stepSize p v; .inr (x, η, x - η • v)
    | .inr (x, η, _) => .inl (x - η • v)
  output := output p

end LongTails.Algorithms.GeneralizedMintyExtragradient
