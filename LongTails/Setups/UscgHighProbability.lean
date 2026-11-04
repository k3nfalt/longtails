import LongTails.Setups.UscgConstant

open MeasureTheory

namespace LongTails.Setups.UscgHighProbability

open OracleTemplate
open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO Problem)

structure Public where
  d : ℕ
  N : Seminorm ℝ (Space d)
  x₁ : Space d
  L : ℝ
  L₂ : ℝ
  σ : ℝ
  Δ : ℝ
  R : ℝ
  ζ : ℝ
  ε : ℝ
  δ : ℝ

structure Params extends Public where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]

attribute [instance] Params.measurableΩ

structure State (d : ℕ) where
  count : ℕ
  point : Space d
  momentum : Space d
  waitingForLmo : Bool
  trajectory : ℕ → Space d

noncomputable def method (p : Public) (α η : ℕ → ℝ) :
    Algorithm (Space p.d) (Space p.d) (ℕ × (ℕ → Space p.d)) 2 where
  State := State p.d
  initial _ := ⟨0, p.x₁, 0, false, fun _ => p.x₁⟩
  query s := if s.waitingForLmo then (1, s.momentum) else (0, s.point)
  update s r :=
    if s.waitingForLmo then
      ⟨s.count + 1, s.point + η (s.count + 1) • r, s.momentum, false,
        Function.update s.trajectory s.count s.point⟩
    else
      ⟨s.count, s.point,
        α (s.count + 1) • r + (1 - α (s.count + 1)) • s.momentum,
        true, s.trajectory⟩
  output s := (s.count, s.trajectory)

noncomputable def averageStationarity (p : Public) (f : Space p.d → ℝ)
    (xs : ℕ × (ℕ → Space p.d)) : ℝ :=
  (∑ k ∈ Finset.range xs.1, dualNorm p.N (gradient f (xs.2 k))) / (xs.1 : ℝ)

abbrev spec : Setup where
  numOracles := 2
  Params := Params
  Public := Public
  Instance p := Space p.d → ℝ
  Query p := Space p.d
  Reply p := Space p.d
  Output p := ℕ × (ℕ → Space p.d)
  publicInput p := p.toPublic
  valid p :=
    (∀ x, p.N x = 0 → x = 0) ∧
      0 < p.R ∧ (∀ x, p.N x ≤ 1 → ‖x‖ ≤ p.R) ∧
      0 < p.ζ ∧ (∀ z, dualNorm p.N z ≤ p.ζ * ‖z‖) ∧
      0 < p.L ∧ 0 ≤ p.L₂ ∧ 0 ≤ p.σ ∧ 0 ≤ p.Δ ∧
      0 < p.ε ∧ 0 < p.δ ∧ p.δ < 1 / 2
  admissible p f O :=
    ∃ (g : Space p.d → p.Ω → Space p.d) (lmo : Space p.d → Space p.d)
      (P₀ : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → p.Ω) => ξ k) (P₀ : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => p.Ω
            law := P
            answer := fun _ (i, x) ω => if i = 0 then g x ω else lmo x } ∧
      IsBallLMO p.N 1 lmo ∧
      Problem p.N p.L p.L₂ p.σ p.Δ p.x₁ f g (P₀ : Measure _)
  successful p f output P :=
    Measurable output ∧ (∀ ω, 0 < (output ω).1) ∧
      Measurable (fun ω => averageStationarity p.toPublic f (output ω)) ∧
      (P : Measure _) {ω | p.ε < averageStationarity p.toPublic f (output ω)} ≤
        ENNReal.ofReal p.δ
  allowedAlgorithm p A :=
    ∃ (α η : ℕ → ℝ), α 1 = 1 ∧
      (∀ t, 1 ≤ t → 0 < α t ∧ α t ≤ 1 ∧ 0 < η t) ∧
      (∀ t, 2 ≤ t → α t < 1) ∧ A = method p α η

end LongTails.Setups.UscgHighProbability
