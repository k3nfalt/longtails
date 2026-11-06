import LongTails.Setups.SelfConcordantBFGS

namespace LongTails.Algorithms.SelfConcordantBFGS

open OracleTemplate LongTails.Setups.SelfConcordantBFGS

noncomputable def method (p : Public) : Algorithm (Vec p.d × Vec p.d) (ℝ × Vec p.d) (Vec p.d) :=
  bfgs p.x0 p.B0

end LongTails.Algorithms.SelfConcordantBFGS
