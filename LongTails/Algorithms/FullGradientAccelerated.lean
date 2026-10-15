import LongTails.Setups.QuadraticFiniteSum
import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.Batched

open scoped BigOperators

noncomputable section

namespace OracleTemplate.FullGradientAccelerated

open LongTails.Setups.QuadraticFiniteSum

def core (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E where
  State := p.E × p.E
  initial _ := (p.x0, p.x0)
  query s := (0, (0, InexactGradient.query (InexactGradient.momentum p.L p.μ 0) s))
  update s g := InexactGradient.step p.L p.μ (InexactGradient.momentum p.L p.μ 0) s g
  output s := s.1

def algorithm (p : Params) : Algorithm (Fin p.n × p.E) p.E p.E :=
  batched (NeZero.pos p.n) (core p)
    (fun s i => (i, InexactGradient.query (InexactGradient.momentum p.L p.μ 0) s))
    (fun _ replies => (p.n : ℝ)⁻¹ • ∑ i, replies i) 0

def output (p : Params) (g : p.E → p.E) (K : ℕ) : p.E :=
  execute { answer := fun _ q _ => g q.2 }
    (InexactGradient.inexactAccelerated p.L p.μ 0 p.x0) (fun _ => K)

end OracleTemplate.FullGradientAccelerated
