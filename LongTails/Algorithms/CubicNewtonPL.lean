import LongTails.Setups.HessianLipschitzPL
import LongTails.Algorithms.PLMinimaxCubic

namespace LongTails.Algorithms.CubicNewtonPL

open OracleTemplate LongTails.Setups.HessianLipschitzPL

noncomputable def step (p : Public) (x : p.E) (reply : ℝ × p.E × (p.E →L[ℝ] p.E)) : p.E :=
  x + OracleTemplate.PLMinimax.envelopeCubicStep reply.2.1 reply.2.2 p.H

noncomputable def method (p : Public) :
    Algorithm p.E (ℝ × p.E × (p.E →L[ℝ] p.E)) p.E where
  State := p.E
  initial _ := p.x0
  query x := (0, x)
  update x reply := step p x reply
  output x := x

end LongTails.Algorithms.CubicNewtonPL
