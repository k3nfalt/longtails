import LongTails.Algorithms.StrongGrowthWeights
import LongTails.Algorithms.WeightedInterpolationSgd

namespace LongTails.Algorithms.DistributedGrowthSgd

open LongTails.Setups.DistributedMeanStrongGrowth StrongGrowthWeights
open DistributedTemplate

noncomputable def peak (p : Params) : ℝ := Finset.univ.sup' Finset.univ_nonempty (signal p)

noncomputable def cap (p : Params) (i : Fin p.n) : ℝ := by
  classical
  exact if weight p i = Finset.univ.sup' Finset.univ_nonempty (weight p) then
    3 * p.n * p.L * peak p / signal p i else p.μ * signal p i

noncomputable def schedule (p : Params) : LongTails.Setups.DistributedWeakInterpolation.Params where
  d := p.d
  n := p.n
  Ω := p.Ω
  h := p.h
  l := p.l
  b := p.b
  x0 := p.x0
  R := p.R
  ε := p.ε
  σ := p.σ
  μ := p.μ
  L := cap p

noncomputable def algorithm (p : Params) (T : Time) :=
  WeightedInterpolationSgd.algorithm (schedule p) T

noncomputable def output (p : Params) (T : Time) (g : Fin p.n → Point p → p.Ω → Point p) :=
  WeightedInterpolationSgd.output (schedule p) T g

end LongTails.Algorithms.DistributedGrowthSgd
