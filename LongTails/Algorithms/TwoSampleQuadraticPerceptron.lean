import LongTails.Setups.TwoSampleQuadraticPerceptron

open OracleTemplate

namespace LongTails.Algorithms.TwoSampleQuadraticPerceptron

open LongTails.Setups.TwoSampleQuadraticPerceptron

noncomputable def update (P : Public) (γ : ℝ) (θ : Space P.model P.dimension)
    (reply : Reply P.model P.dimension) : Space P.model P.dimension :=
  if reply.first ≤ 0 then move P.model P.dimension θ γ reply.firstDirection
  else if reply.second ≤ 0 then move P.model P.dimension θ γ reply.secondDirection
  else θ

noncomputable def algorithm (P : Public) :
    Algorithm (Space P.model P.dimension) (Reply P.model P.dimension)
      (Space P.model P.dimension) where
  State := Space P.model P.dimension
  initial _ := P.start
  query θ := (0, θ)
  update θ reply := update P (1 / (2 * P.radius)) θ reply
  output θ := θ

end LongTails.Algorithms.TwoSampleQuadraticPerceptron
