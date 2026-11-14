import LongTails.Setups.StochasticMfcqInequalities
import LongTails.Algorithms.FiniteHullDirection
import LongTails.Algorithms.RobustGradientEstimator
import Mathlib.Analysis.InnerProductSpace.ProdL2

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.StochasticMfcqDirection

open LongTails.Setups.StochasticMfcqInequalities

noncomputable def precision (p : Params) : ℝ := p.μ * min p.ε (min 1 p.τ) / (40 * p.H)

noncomputable def stepSize (p : Params) : ℝ := precision p / (4 * p.H)

noncomputable def outerSteps (p : Params) : ℕ := 1 + ⌈2 * p.H * p.Δ / precision p ^ 2⌉₊

noncomputable def epochLength (p : Params) : ℕ :=
  max 1 ⌈outerSteps p * p.σ * p.H /
    (outerSteps p * p.L * precision p + p.H * (p.σ + precision p))⌉₊

noncomputable def resetBatch (p : Params) : ℕ := 1 + ⌈1152 * p.σ ^ 2 / precision p ^ 2⌉₊

noncomputable def incrementBatch (p : Params) : ℕ := 1 + ⌈72 * epochLength p * p.L ^ 2 / p.H ^ 2⌉₊

noncomputable def replicas (p : Params) : ℕ := 1 + ⌈Real.log (outerSteps p / p.ρ) / Real.log 4⌉₊

noncomputable def hullSteps (p : Params) : ℕ := 1 + ⌈10 * (p.H + 1) ^ 2 / precision p ^ 2⌉₊

abbrev JointSpace (p : Params) := WithLp 2 (p.E × WithLp 2 (Constraint p × Jacobian p))

instance (p : Params) : MeasurableSpace (JointSpace p) := borel (JointSpace p)
instance (p : Params) : BorelSpace (JointSpace p) := ⟨rfl⟩

noncomputable def jointEquiv (p : Params) : Primitive p ≃L[ℝ] JointSpace p :=
  ((ContinuousLinearEquiv.refl ℝ p.E).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Constraint p) (Jacobian p)).symm).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ p.E (WithLp 2 (Constraint p × Jacobian p))).symm

noncomputable def active (p : Params) (v : Primitive p) (i : Fin p.m) : Prop :=
  -4 * precision p ≤ v.2.1 i

noncomputable def vectors (p : Params) (v : Primitive p) : Fin (p.m + 1) → p.E := by
  classical
  exact Fin.cases v.1 (fun i => if active p v i then v.2.2 i else v.1)

noncomputable def coefficients (p : Params) (v : Primitive p) : Fin (p.m + 1) → ℝ :=
  FiniteHullDirection.weights (vectors p v) (hullSteps p)

noncomputable def residual (p : Params) (v : Primitive p) : p.E :=
  FiniteHullDirection.point (vectors p v) (coefficients p v)

noncomputable def objectiveWeight (p : Params) (v : Primitive p) : ℝ := by
  classical
  exact coefficients p v 0 + ∑ i : Fin p.m, if active p v i then 0 else coefficients p v i.succ

noncomputable def constraintWeight (p : Params) (v : Primitive p) (i : Fin p.m) : ℝ := by
  classical
  exact if active p v i then coefficients p v i.succ else 0

noncomputable def multipliers (p : Params) (v : Primitive p) : Constraint p := by
  exact WithLp.toLp 2 (fun i => constraintWeight p v i / objectiveWeight p v)

noncomputable def direction (p : Params) (v : Primitive p) : p.E :=
  -(‖residual p v‖⁻¹ • residual p v)

noncomputable def robustEstimate (p : Params) (estimates : Fin (replicas p) → JointSpace p) :
    Primitive p :=
  (jointEquiv p).symm (OracleTemplate.RobustGradient.pilotCenter (2 * precision p) estimates)

end LongTails.Algorithms.StochasticMfcqDirection
