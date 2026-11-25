import LongTails.Setups.SpatialRankingLogistic

namespace LongTails.Setups.SpatialRankingFrozenFilter

noncomputable def spec : OracleTemplate.Setup :=
  { SpatialRankingLogistic.spec with
    valid := fun p => 8 ≤ p.n ∧ 32 * (p.n+1) ≤ p.d
    allowedAlgorithm := fun p => SpatialRankingLogistic.family p .frozen }

end LongTails.Setups.SpatialRankingFrozenFilter
