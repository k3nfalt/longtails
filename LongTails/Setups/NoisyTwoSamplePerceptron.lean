import LongTails.Setups.FiniteLogisticTwoTap
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory OracleTemplate ProbabilityTheory
open LongTails.Setups.FiniteLogisticTwoTap (Weights Reply signedInput answer Separates)

namespace LongTails.Setups.NoisyTwoSamplePerceptron

structure Params where
  d : ℕ
  μ : ℝ
  x₀ : Weights d
  signal : ℝ
  ρ : ℝ

noncomputable def slowProjection {d : ℕ} (i : Fin d) (x : Weights d) : ℝ :=
  (-x (.inl 0) + x (.inl 1) + x (.inr i) - x (.inr (finRotate d i))) / 2

structure State (d : ℕ) where
  point : Weights d
  first : Option (Reply d)
  clock : ℕ
  noise : ℕ → Weights d

noncomputable def update {d : ℕ} (η σ : ℝ) (s : State d) (reply : Reply d) : State d :=
  match s.first with
  | none => {s with first := some reply}
  | some a =>
    let move := fun (g : Weights d) => s.point + η • g + σ • s.noise s.clock
    let x := if a.margin ≤ 0 then move a.direction else
      if reply.margin ≤ 0 then move reply.direction else s.point
    ⟨x, none, s.clock + 1, s.noise⟩

def family (p : Params) (A : Algorithm (Bool × Weights p.d) (Reply p.d) (Weights p.d)) : Prop :=
  ∃ (η σ : ℝ) (ξ : ℕ → A.Seed → Weights p.d) (view : A.State → State p.d),
    0 < η ∧ 0 < σ ∧ StochasticGeneralizedSmoothAndConvex.IID ξ (stdGaussian _) A.law ∧
    (∀ ω, view (A.initial ω) = ⟨p.x₀, none, 0, fun k => ξ k ω⟩) ∧
    (∀ s, A.query s = (0, (view s).first.isSome, (view s).point)) ∧
    (∀ s reply, view (A.update s reply) = update η σ (view s) reply) ∧
    (∀ s, A.output s = (view s).point)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.d
  Query p := Bool × Weights p.d
  Reply p := Reply p.d
  Output p := Weights p.d
  publicInput := id
  valid p := 2 ≤ p.d ∧ 0 < p.μ ∧ p.μ ≤ 1 / 10 ∧ 0 < p.signal ∧
    (∃ i : Fin p.d, p.signal ≤ |slowProjection i p.x₀|) ∧
    0 < p.ρ ∧ p.ρ < 1
  admissible p i O := p.signal ≤ |slowProjection i p.x₀| ∧
    ∀ history query seed, O.answer history query seed = answer (signedInput p.μ i query.2.1) query.2.2
  successful p i out P := (P : Measure _) {ω | ¬Separates p.μ i (out ω)} ≤ ENNReal.ofReal p.ρ
  allowedAlgorithm := family

end LongTails.Setups.NoisyTwoSamplePerceptron
