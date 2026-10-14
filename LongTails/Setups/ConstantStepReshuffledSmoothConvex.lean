import LongTails.Setups.ReshuffledSmoothConvex

namespace LongTails.Setups.ConstantStepReshuffledSmoothConvex

open OracleTemplate

abbrev Params := LongTails.Setups.ReshuffledSmoothConvex.Params

abbrev spec : Setup :=
  { LongTails.Setups.ReshuffledSmoothConvex.spec with
    allowedAlgorithm := fun q algorithm =>
      ∃ (K : ℕ) (η : ℝ), 0 < η ∧ algorithm =
        ReshuffledConvex.reshuffledGradient K (fun _ => η) q.x0 }

end LongTails.Setups.ConstantStepReshuffledSmoothConvex
