import LongTails.Setups.DistributedGradientDiversity

namespace LongTails.Algorithms.GradientDiversityDesign

open LongTails.Setups.DistributedGradientDiversity

noncomputable def share (p : Params) (t : ℝ) (i : Fin p.n) : ℝ :=
  p.h i / (1 - t + t * (p.h i : ℝ))

noncomputable def profile (p : Params) (t : ℝ) (i : Fin p.n) : ℝ :=
  (p.n : ℝ) * share p t i / ∑ j, share p t j

noncomputable def moment (p : Params) (t : ℝ) : ℝ := ∑ i, profile p t i ^ 2

noncomputable def parameter (p : Params) : ℝ := by
  classical
  exact if h : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ moment p t = (p.n : ℝ) * p.ρ then h.choose else 0

noncomputable def amplitude (p : Params) := profile p (parameter p)

noncomputable def weight (p : Params) (i : Fin p.n) : ℝ := amplitude p i / p.h i

noncomputable def information (p : Params) : ℝ := ∑ i, weight p i * amplitude p i

end LongTails.Algorithms.GradientDiversityDesign
