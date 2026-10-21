import LongTails.Algorithms.Muon
import LongTails.Setups.StochasticSmoothAndConvex
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.MuonFrobenius

open OracleTemplate OracleTemplate.Muon

structure Params where
  m : ℕ
  n : ℕ
  L : ℝ
  σ : ℝ
  η : ℝ
  β : ℝ
  B : ℕ
  T : ℕ
  W0 : Mat m n

def publicInput (p : Params) : Muon.Public := ⟨p.m, p.n, p.η, p.β, p.B, p.T, p.W0⟩

def FrobeniusSmooth {m n : ℕ} (L : ℝ) (f : Mat m n → ℝ) : Prop :=
  (∀ W, HasGradientAt f (gradient f W) W) ∧ ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖

def StochasticOracleModel {m n : ℕ} (f : Mat m n → ℝ) (σ : ℝ) (O : Oracle (Mat m n) (Mat m n)) : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω)) (g : Mat m n → Ω → Mat m n),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
        (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
      LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ ∧
      O = sampleOracle P g

noncomputable def averageNuclear (p : Params) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : ℝ :=
  (1 / (p.T : ℝ)) * ∑ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P

def Guarantee (p : Params) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : Prop :=
  let r : ℝ := (min p.m p.n : ℕ)
  let T : ℝ := p.T
  let Δ : ℝ := f p.W0 - ⨅ W, f W
  let avg := averageNuclear p f W P
  (∀ t, Measurable (fun ω => W ω t)) ∧
  (∀ t, Integrable (fun ω => nuclearNorm (gradient f (W ω t))) P) ∧
  (∀ t, Integrable (fun ω => f (W ω t)) P) ∧
  avg ≤ (∫ ω, f (W ω 0) - f (W ω (Fin.last p.T)) ∂P) / (T * p.η) + p.L * r * p.η / 2 +
      2 * p.σ * Real.sqrt (r * (1 - p.β)) / Real.sqrt (p.B * (1 + p.β)) +
      2 * p.β * p.σ * Real.sqrt r / ((1 - p.β) * T * Real.sqrt p.B) +
      2 * r * p.η * p.β * p.L / (1 - p.β) ∧
  (0 < p.L → p.B = 1 → p.η = Real.sqrt ((1 - p.β) * Δ / (r * T * p.L)) →
    1 - p.β = (if p.σ = 0 then 1 else min (Real.sqrt (p.L * Δ) / (p.σ * Real.sqrt T)) 1) →
    avg ≤ 6 * ((r ^ 2 * p.L * Δ * p.σ ^ 2 / T) ^ (1 / 4 : ℝ) + Real.sqrt (r * p.L * Δ / T) +
      Real.sqrt r * p.σ ^ 2 / Real.sqrt (p.L * Δ * T)) ∧
    ∀ ε > 0, 18 ^ 4 * r ^ 2 * p.L * Δ * p.σ ^ 2 / ε ^ 4 + 18 ^ 2 * r * p.L * Δ / ε ^ 2 +
        18 ^ 2 * r * p.σ ^ 4 / (p.L * Δ * ε ^ 2) ≤ T →
      avg ≤ ε ∧ ∃ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P ≤ ε)

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Muon.Public
  Instance p := Mat p.m p.n → ℝ
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Fin (p.T + 1) → Mat p.m p.n
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.L ∧ 0 ≤ p.σ ∧ 0 < p.η ∧ 0 ≤ p.β ∧ p.β < 1 ∧
    1 ≤ p.B ∧ 1 ≤ p.T
  admissible p f O := FrobeniusSmooth p.L f ∧ BddBelow (Set.range f) ∧ StochasticOracleModel f p.σ O
  successful p f W P := Guarantee p f W (P : Measure _)
  allowedAlgorithm q A := A = muon q

attribute [local simp] publicInput FrobeniusSmooth StochasticOracleModel averageNuclear Guarantee

end LongTails.Setups.MuonFrobenius
