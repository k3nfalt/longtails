import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

structure OracleTemplate.RestartedScheduleGD.State (E : Type*) where
  point : E
  centre : E
  index : ℕ
  done : Bool

noncomputable def OracleTemplate.RestartedScheduleGD.algorithm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L ε G1 R : ℝ) (steps : List ℝ) (x0 : E) :
    OracleTemplate.Algorithm E E E where
  State := OracleTemplate.RestartedScheduleGD.State E
  initial _ := ⟨x0, x0, 0, false⟩
  query s := (0, s.point)
  update s g :=
    if s.done ∨ ‖g‖ ≤ ε then ⟨s.point, s.centre, s.index, true⟩
    else if s.index = 0 ∧ G1 < ‖g‖ then ⟨s.point - L⁻¹ • g, s.centre, 0, false⟩
    else
      let y := if s.index = 0 then s.point else s.centre
      let x' := s.point - steps.getD s.index 0 • g
      ⟨x', y, if s.index + 1 < steps.length ∧ ‖x' - y‖ ≤ R then s.index + 1 else 0, false⟩
  output s := s.point

namespace LongTails.Setups.HessianLipschitzGradientStationarity

open OracleTemplate

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  x0 : E
  L : ℝ
  ρ : ℝ
  Δ : ℝ
  ε : ℝ

attribute [instance] Params.normedE Params.innerE Params.finiteE

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.ρ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    ContDiff ℝ 2 f ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) ∧
    (∀ x, f p.x0 - f x ≤ p.Δ) ∧
    (∀ k x seed, O.answer k (0, x) seed = gradient f x)
  successful p f output _ := ∀ ω, ‖gradient f (output ω)‖ ≤ p.ε
  allowedAlgorithm p A :=
    ∃ (G1 R : ℝ) (steps : List ℝ), (∀ h ∈ steps, 0 < h) ∧
      A = RestartedScheduleGD.algorithm p.L p.ε G1 R steps p.x0

end LongTails.Setups.HessianLipschitzGradientStationarity
