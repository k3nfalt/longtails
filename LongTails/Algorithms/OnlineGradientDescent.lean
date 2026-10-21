import LongTails.Setups.OnlineConvexBoundedGradient
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.OnlineGradientDescent

open LongTails.Setups.OnlineConvexBoundedGradient

def steps (p : Public) : ℕ := p.T

noncomputable def stepSize (p : Public) : ℝ := p.D / (p.G * Real.sqrt (steps p))

noncomputable def project (p : Public) (z : EuclideanSpace ℝ (Fin p.d)) : p.K := by
  classical
  exact if h : IsCompact p.K ∧ Convex ℝ p.K then
    let hmin := exists_norm_eq_iInf_of_complete_convex ⟨p.x0.val, p.x0.property⟩
      h.1.isComplete h.2 z
    ⟨hmin.choose, hmin.choose_spec.1⟩
  else p.x0

noncomputable def algorithm (p : Public) : Algorithm p.K (EuclideanSpace ℝ (Fin p.d)) Unit where
  State := p.K
  initial _ := p.x0
  query x := (0, x)
  update x g := project p (x.val - stepSize p • g)
  output _ := ()

noncomputable def trajectory (p : Public) (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ) : ℕ → p.K
  | 0 => p.x0
  | t + 1 => project p ((trajectory p losses t).val -
      stepSize p • gradient (losses t) (trajectory p losses t))

end OracleTemplate.OnlineGradientDescent
