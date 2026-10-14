import LongTails.Algorithms.QueryPlan

namespace OracleTemplate.QueryPlan

variable {Q R U Ω : Type*}

def sampledEval (g : Q → Ω → R) (ξ : ℕ → Ω) :
    {k : ℕ} → QueryPlan Q R U k → ℕ → U
  | _, .done value, _ => value
  | _, .ask q next, call => sampledEval g ξ (next (g q (ξ call))) (call + 1)

end OracleTemplate.QueryPlan
