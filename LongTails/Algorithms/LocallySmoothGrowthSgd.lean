import LongTails.Algorithms.GradientDiversitySgd
import LongTails.Setups.DistributedLocallySmoothGrowth

namespace LongTails.Algorithms.LocallySmoothGrowthSgd

open LongTails.Setups.DistributedLocallySmoothGrowth GradientDiversitySgd

noncomputable def scale (p : Params) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => curvature (aggregate p) i * max (curvature (aggregate p) i) (p.L i))

noncomputable abbrev schedule (p : Params) := scheduleAt (aggregate p) (scale p)

noncomputable def algorithm (p : Params) (T : DistributedTemplate.Time) :=
  WeightedInterpolationSgd.algorithm (schedule p) T

noncomputable def output (p : Params) (T : DistributedTemplate.Time)
    (g : Fin p.n → Point p → p.Ω → Point p) :=
  WeightedInterpolationSgd.output (schedule p) T g

end LongTails.Algorithms.LocallySmoothGrowthSgd
