import LongTails.Setups.MultirateSmoothNonconvex

namespace LongTails.Algorithms.MultirateAllocation

open LongTails.Setups.MultirateSmoothNonconvex

noncomputable def precision (p : Params) : ℝ := p.ε / 1024

noncomputable def startupWeight (p : Params) (i : Fin p.n) : ℝ := p.h i * p.σ i ^ 2

noncomputable def refreshWeight (p : Params) (i : Fin p.n) : ℝ :=
  p.σ i * Real.sqrt (p.L i * p.h i)

noncomputable def share (p : Params) (i : Fin p.n) : ℝ :=
  ((p.n : ℝ) * precision p) ^ 2 / 2 *
    (startupWeight p i / (∑ j, startupWeight p j) + refreshWeight p i / (∑ j, refreshWeight p j))

noncomputable def batch (p : Params) (i : Fin p.n) : ℕ :=
  1 + ⌊p.σ i ^ 2 / share p i⌋₊

end LongTails.Algorithms.MultirateAllocation
