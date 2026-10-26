import LongTails.Setups.LinearPredictorBFGS

namespace LongTails.Algorithms.LinearPredictorBFGS

open OracleTemplate LongTails.Setups.LinearPredictorBFGS

noncomputable def method (p : Public) :
    Algorithm (Space p.d × Space p.d) (ℝ × Space p.d) (Space p.d) :=
  bfgs p.L p.x0

end LongTails.Algorithms.LinearPredictorBFGS
