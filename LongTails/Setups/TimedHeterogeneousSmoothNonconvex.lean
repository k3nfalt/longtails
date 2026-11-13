import LongTails.TemplateTimed
import LongTails.Setups.NetworkModels
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.TimedHeterogeneousSmoothNonconvex

open OracleTemplate LongTails.Setups.NetworkModels
open LongTails.Setups.StochasticSmoothAndConvex LongTails.Setups.StochasticGeneralizedSmoothAndConvex

structure Params where
  d : ℕ
  n : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  τ : Fin n → ℝ
  hUp : ℝ
  hDown : ℝ
  L : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

noncomputable def average (p : Params) (F : Fin p.n → Point p → ℝ) (x : Point p) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ i, F i x

abbrev spec : TimedSetup where
  Params := Params
  Public := Params
  numNodes p := p.n + 1
  Instance p := Fin p.n → Point p → ℝ
  Query p := Point p
  Reply p := Point p
  Output p := Point p
  publicInput p := p
  valid p := 0 < p.n ∧ (∀ i, 0 < p.τ i) ∧ 0 ≤ p.hUp ∧ 0 ≤ p.hDown ∧
    0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p F oracles environment :=
    environment = queueEnvironment (starNetwork p.n p.τ p.hUp p.hDown) ∧
    SilentOracle (oracles 0) ∧
    (∀ x, HasGradientAt (average p F) (gradient (average p F) x) x) ∧
    (∀ x y, ‖gradient (average p F) x - gradient (average p F) y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ average p F x) ∧ average p F p.x0 - lower ≤ p.Δ) ∧
    ∀ i : Fin p.n, (∀ x, HasGradientAt (F i) (gradient (F i) x) x) ∧
      ∃ (g : Point p → p.Ω → Point p) (μ : ProbabilityMeasure p.Ω)
        (P : ProbabilityMeasure (ℕ → p.Ω)),
      IID (fun k (ξ : ℕ → p.Ω) => ξ k) (μ : Measure _) (P : Measure _) ∧
      oracles i.succ = { Seed := fun _ => p.Ω, law := P, answer := fun _ q ξ => g q.2 ξ } ∧
      IsStochasticGradient (Point p) p.Ω μ (F i) g p.σ
  successful p F output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (average p F) (output ω)‖ ^ 2) (P : Measure _) ∧
    ∫ ω, ‖gradient (average p F) (output ω)‖ ^ 2 ∂(P : Measure _) ≤ p.ε

end LongTails.Setups.TimedHeterogeneousSmoothNonconvex
