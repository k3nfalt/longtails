import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LongTails.Setups.SmoothAndConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OracleTemplate.NearestAiming

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def nesterovStep (L μ : ℝ) (state : E × E) (g : E) : E × E :=
  let s := 1 / (2 * Real.sqrt L)
  let q := Real.sqrt μ * s
  (state.1 + s • state.2 - s ^ 2 • g,
    ((1 - q) / (1 + q)) • (state.2 - s • g))

end OracleTemplate.NearestAiming

open Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Setups.LocalStrongAiming

open OracleTemplate OracleTemplate.NearestAiming

structure Public extends toGradientPublic : LongTails.Setups.SmoothAndConvex.Public where
  [finiteE : FiniteDimensional ℝ E]
  μ : ℝ

attribute [instance] Public.finiteE

structure Params extends Public where
  r : ℝ
  Δ : ℝ
  ε : ℝ

def FollowsNesterov (p : Public) (A : Algorithm p.E p.E p.E) : Prop :=
  ∃ position velocity : A.State → p.E,
    (∀ seed, position (A.initial seed) = p.x0 ∧ velocity (A.initial seed) = 0) ∧
    (∀ state, (A.query state).2 = position state + (1 / (2 * Real.sqrt p.L)) • velocity state) ∧
    (∀ state reply, (position (A.update state reply), velocity (A.update state reply)) =
      nesterovStep p.L p.μ (position state, velocity state) reply) ∧
    (∀ state, A.output state = position state)

abbrev CertifiedAlgorithm (p : Public) :=
  {A : Algorithm p.E p.E p.E // FollowsNesterov p A}

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput := Params.toPublic
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.r ∧ 0 ≤ p.Δ ∧
    256 * p.Δ ≤ p.μ * p.r ^ 2 ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x) ∧
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∃ xstar, IsMinOn f univ xstar ∧ f p.x0 - f xstar ≤ p.Δ ∧
      let M := {x | f x = f xstar}
      infDist p.x0 M < p.r ∧
      (∀ x y, infDist x M < p.r → infDist y M < p.r →
        ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
      (∀ x y, infDist x M < p.r → infDist y M < p.r →
        f x + ⟪gradient f x, y - x⟫ - Real.sqrt (p.μ * p.L) * ‖y - x‖ ^ 2 ≤ f y) ∧
      (∀ x z, infDist x M < p.r → z ∈ M → infDist x M = ‖x - z‖ →
        f x - f xstar + p.μ / 2 * ‖x - z‖ ^ 2 ≤ ⟪gradient f x, x - z⟫))
  successful p f output P :=
    ∃ xstar, IsMinOn f univ xstar ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), f (output ω) - f xstar ≤ p.ε
  allowedAlgorithm := FollowsNesterov

end LongTails.Setups.LocalStrongAiming
