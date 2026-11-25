import LongTails.Setups.TwoTapLogisticSeparation

open OracleTemplate

namespace LongTails.Algorithms.TwoTapLogisticGd

open LongTails.Setups.TwoTapLogisticSeparation
open LongTails.Setups.TwoSampleQuadraticPerceptron

noncomputable def stepSize (p : LongTails.Setups.TwoTapLogisticSeparation.Params) : ℝ :=
  let U := p.start.1.1^2+p.start.1.2^2
  let V := ‖p.start.2‖^2
  let D := |V-U|+2
  let u := if p.δ ≤ U-V then p.δ/2 else min 1 ((p.δ/p.R)^2/(1+D))
  let K := 5*(2+(D+2)/u)
  let M := U+V+2+4*(4*Real.sqrt K/p.γ)
  let L := 1+8*p.R+32*p.R^2*M
  1/(L+(if p.δ ≤ U-V then 4/p.δ else 0))

noncomputable def algorithm (p : LongTails.Setups.TwoTapLogisticSeparation.Params) (η : ℝ) :
    Algorithm (Space .conv p.d) (Space .conv p.d) (Space .conv p.d) where
  State := Space .conv p.d
  initial _ := p.start
  query θ := (0,θ)
  update θ g := θ+η • g
  output θ := θ

end LongTails.Algorithms.TwoTapLogisticGd
