import LongTails.Setups.DistributedMeanStrongGrowth

namespace LongTails.Algorithms.StrongGrowthWeights

open LongTails.Setups.DistributedMeanStrongGrowth

noncomputable def service (p : Params) (t : ℝ) (i : Fin p.n) : ℝ :=
  p.h i / ((1-t) * p.h i + t)

noncomputable def normalized (p : Params) (t : ℝ) (i : Fin p.n) : ℝ :=
  p.n * service p t i / ∑ j, service p t j

noncomputable def mixing (p : Params) : ℝ := by
  classical
  exact if h : ∃ t : ℝ, 0 ≤ t ∧ min (1-t) (p.n*p.ρ - ∑ i, normalized p t i ^ 2) = 0
    then h.choose else 0

noncomputable def signal (p : Params) := normalized p (mixing p)

noncomputable def weight (p : Params) (i : Fin p.n) : ℝ := signal p i / p.h i

noncomputable def information (p : Params) : ℝ := ∑ i, weight p i * signal p i

end LongTails.Algorithms.StrongGrowthWeights
