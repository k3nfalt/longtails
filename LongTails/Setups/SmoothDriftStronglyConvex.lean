import LongTails.Setups.StochasticSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.SmoothDriftStronglyConvex

open OracleTemplate
open LongTails.Setups.StochasticSmoothAndConvex

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  [countableE : SecondCountableTopology E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  μ : ℝ
  L : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.linearE Public.completeE Public.measurableE
  Public.borelE Public.countableE Public.measurableΩ

structure Params extends Public where
  Γ : ℝ
  R : ℝ
  V : ℝ
  H : ℕ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := ℕ → p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E × ℕ
  publicInput := Params.toPublic
  valid q := 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 ≤ q.σ ∧ 0 ≤ q.Γ ∧ 0 ≤ q.R ∧ 0 ≤ q.V ∧ 0 < q.ε ∧
    9792 * q.Γ ^ 2 * (2 * q.L / q.μ + 99 * q.σ ^ 2 / (q.μ ^ 2 * q.ε)) ^ 4 ≤ q.ε
  admissible q f O :=
    ∃ (oracle : ℕ → q.E → q.Ω → q.E) (P : ProbabilityMeasure q.Ω),
    O = { Seed := fun _ => q.Ω
          law := ⟨Measure.infinitePi (fun _ : ℕ => (P : Measure q.Ω)), inferInstance⟩
          answer := fun k (_, x) seed => oracle k x seed } ∧
    (∀ k, IsStochasticGradient q.E q.Ω P (f k) (oracle k) q.σ) ∧
    (∀ k x, HasGradientAt (f k) (gradient (f k) x) x) ∧
    (∀ k x y, f k x + ⟪gradient (f k) x, y - x⟫ + q.μ / 2 * ‖y - x‖ ^ 2 ≤ f k y) ∧
    (∀ k x y, ‖gradient (f k) x - gradient (f k) y‖ ≤ q.L * ‖x - y‖) ∧
    ∃ xstar : ℕ → q.E, (∀ k, IsMinOn (f k) Set.univ (xstar k)) ∧
      ‖q.x0 - xstar 0‖ ≤ q.R ∧ ‖xstar 1 - xstar 0‖ ≤ q.V ∧
      ∀ k, ‖(xstar (k + 2) - xstar (k + 1)) - (xstar (k + 1) - xstar k)‖ ≤ q.Γ
  successful q f output P :=
    ∃ xstar : ℕ → q.E, (∀ k, IsMinOn (f k) Set.univ (xstar k)) ∧
      Integrable (fun ω => ‖(output ω).1 - xstar ((output ω).2 - 1)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖(output ω).1 - xstar ((output ω).2 - 1)‖ ^ 2 ∂(P : Measure _)) ≤ q.ε
  allowedAlgorithm _ A :=
    ∃ clock : A.State → ℕ, (∀ seed, clock (A.initial seed) = 0) ∧
      (∀ state reply, clock (A.update state reply) = clock state + 1) ∧
      ∀ state, (A.output state).2 = clock state

end LongTails.Setups.SmoothDriftStronglyConvex
