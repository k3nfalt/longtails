import LongTails.Algorithms.CyclicGradient

namespace OracleTemplate.CyclicGradientPassDisplacement

open LongTails.Setups.InterpolatedFiniteSum

noncomputable def algorithm (p : Public) : Algorithm (Fin p.m × p.E) p.E p.E :=
  CyclicInterpolation.cyclicGradient p.m p.L p.x0

end OracleTemplate.CyclicGradientPassDisplacement
