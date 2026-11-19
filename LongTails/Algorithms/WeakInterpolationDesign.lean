import LongTails.Setups.DistributedWeakInterpolation

namespace LongTails.Algorithms.WeakInterpolationDesign

open LongTails.Setups.DistributedWeakInterpolation

variable {ι : Type*}

def curvature (L h : ι → ℝ) (c : ℝ) (i : ι) : ℝ := min (L i) (c * h i)

noncomputable def weight (L h : ι → ℝ) (c : ℝ) (i : ι) : ℝ := curvature L h c i / h i

noncomputable def threshold (p : Params) : ℝ := by
  classical
  exact if h : ∃ c : ℝ, 0 ≤ c ∧
    ∑ i, curvature p.L (fun j => p.h j) c i = (p.n : ℝ) * p.μ then h.choose else 0

noncomputable def profile (p : Params) := curvature p.L (fun j => p.h j) (threshold p)

noncomputable def weights (p : Params) := weight p.L (fun j => p.h j) (threshold p)

noncomputable def information (p : Params) : ℝ := ∑ i, weights p i * profile p i

noncomputable def largestCurvature (p : Params) : ℝ :=
  (Finset.univ : Finset (Fin p.n)).sup' Finset.univ_nonempty (fun i => profile p i * p.L i)

noncomputable def smoothness (p : Params) : ℝ :=
  2 * (∑ i, (p.h i : ℝ)⁻¹) * largestCurvature p

noncomputable def noiseRadius (p : Params) : ℝ :=
  p.σ * (Finset.univ : Finset (Fin p.n)).sup' Finset.univ_nonempty (profile p) / largestCurvature p

end LongTails.Algorithms.WeakInterpolationDesign
