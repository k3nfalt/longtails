import LongTails.Algorithms.GrowthProfile
import LongTails.Algorithms.WeightedInterpolationSgd
import LongTails.Setups.DistributedRelativeGrowth

namespace LongTails.Algorithms.RelativeGrowthBatches

open LongTails.Setups.DistributedRelativeGrowth

noncomputable def signal (p : Params) (i : Fin p.n) : ℝ :=
  p.μ * GrowthProfile.profile (fun j => (p.h j : ℝ)) p.ρ i

noncomputable def gain (p : Params) (i : Fin p.n) : ℝ := signal p i / p.h i

noncomputable def scale (p : Params) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => signal p i * max (signal p i) (p.L i))

noncomputable def tuning (p : Params) : Setups.DistributedWeakInterpolation.Params :=
  { p.toParams with
    L := fun i =>
      if gain p i = Finset.univ.sup' Finset.univ_nonempty (gain p) then scale p / signal p i
      else signal p i }

noncomputable def algorithm (p : Params) (T : DistributedTemplate.Time) :=
  WeightedInterpolationSgd.algorithm (tuning p) T

noncomputable def output (p : Params) (T : DistributedTemplate.Time)
    (g : Fin p.n → Point p → p.Ω → Point p) :=
  WeightedInterpolationSgd.output (tuning p) T g

end LongTails.Algorithms.RelativeGrowthBatches
