import LongTails.Algorithms.StrongGrowthWeights
import LongTails.Algorithms.WeightedInterpolationSgd

namespace LongTails.Algorithms.GradientDiversitySgd

open LongTails.Setups.DistributedMeanStrongGrowth StrongGrowthWeights

noncomputable def curvature (p : Params) (i : Fin p.n) : ℝ := p.μ * signal p i

noncomputable def gain (p : Params) (i : Fin p.n) : ℝ := curvature p i / p.h i

noncomputable def peak (p : Params) : Fin p.n :=
  Classical.choose (Finset.exists_max_image Finset.univ (gain p) Finset.univ_nonempty)

noncomputable def largest (p : Params) : ℝ := Finset.univ.sup' Finset.univ_nonempty (curvature p)

noncomputable def speed (p : Params) : ℝ := ∑ i, (p.h i : ℝ)⁻¹

noncomputable def spread (p : Params) : ℝ := min (p.n : ℝ) (1 + Real.sqrt (p.n * (p.ρ - 1)))

noncomputable def scale (p : Params) : ℝ :=
  p.L * max (largest p * spread p) (p.n * gain p (peak p) / speed p)

noncomputable def capacity (p : Params) (i : Fin p.n) : ℝ :=
  if i = peak p then scale p / curvature p i else curvature p i

noncomputable def schedule (p : Params) : LongTails.Setups.DistributedWeakInterpolation.Params where
  d := p.d
  n := p.n
  Ω := p.Ω
  h := p.h
  l := p.l
  b := p.b
  L := capacity p
  μ := p.μ
  R := p.R
  σ := p.σ
  ε := p.ε
  x0 := p.x0

noncomputable def algorithm (p : Params) (T : DistributedTemplate.Time) :=
  WeightedInterpolationSgd.algorithm (schedule p) T

noncomputable def output (p : Params) (T : DistributedTemplate.Time)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) : Point p :=
  WeightedInterpolationSgd.output (schedule p) T g s

end LongTails.Algorithms.GradientDiversitySgd
