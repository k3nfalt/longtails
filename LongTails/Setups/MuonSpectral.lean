import LongTails.Setups.MuonFrobenius
import LongTails.Setups.MuonFrobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace LongTails.Setups.MuonSpectral

open OracleTemplate OracleTemplate.Muon

structure Constants where
  m : ℕ
  n : ℕ
  Ls : ℝ
  σ : ℝ
  η : ℝ
  β : ℝ
  B : ℕ
  T : ℕ
  W0 : Mat m n

def publicInput (p : Constants) : Muon.Public := ⟨p.m, p.n, p.η, p.β, p.B, p.T, p.W0⟩

def SpectralSmooth {m n : ℕ} (Ls : ℝ) (f : Mat m n → ℝ) : Prop :=
  (∀ W, HasGradientAt f (gradient f W) W) ∧
    ∀ W W', nuclearNorm (gradient f W - gradient f W') ≤ Ls * spectralNorm (W - W')

noncomputable def averageNuclear (p : Constants) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : ℝ :=
  (1 / (p.T : ℝ)) * ∑ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P

def Guarantee (p : Constants) (f : Mat p.m p.n → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (W : Ω → Fin (p.T + 1) → Mat p.m p.n) (P : Measure Ω) : Prop :=
  let r : ℝ := (min p.m p.n : ℕ)
  let T : ℝ := p.T
  let Δ : ℝ := f p.W0 - ⨅ W, f W
  let avg := averageNuclear p f W P
  (∀ t, Measurable (fun ω => W ω t)) ∧
  (∀ t, Integrable (fun ω => nuclearNorm (gradient f (W ω t))) P) ∧
  (∀ t, Integrable (fun ω => f (W ω t)) P) ∧
  avg ≤ (∫ ω, f (W ω 0) - f (W ω (Fin.last p.T)) ∂P) / (T * p.η) + p.Ls * p.η / 2 +
      2 * p.σ * Real.sqrt (r * (1 - p.β)) / Real.sqrt ((1 + p.β) * p.B) +
      2 * p.β * p.σ * Real.sqrt r / ((1 - p.β) * T * Real.sqrt p.B) +
      2 * p.η * p.β * p.Ls / (1 - p.β) ∧
  (0 < p.Ls → p.B = 1 → p.η = Real.sqrt ((1 - p.β) * Δ / (T * p.Ls)) →
    1 - p.β = (if p.σ = 0 then 1 else min (Real.sqrt (p.Ls * Δ) / (p.σ * Real.sqrt (r * T))) 1) →
    avg ≤ 6 * ((r * p.Ls * Δ * p.σ ^ 2 / T) ^ (1 / 4 : ℝ) + Real.sqrt (p.Ls * Δ / T) +
      r * p.σ ^ 2 / Real.sqrt (p.Ls * Δ * T)) ∧
    ∀ ε > 0, 18 ^ 4 * r * p.Ls * Δ * p.σ ^ 2 / ε ^ 4 + 18 ^ 2 * p.Ls * Δ / ε ^ 2 +
        18 ^ 2 * r ^ 2 * p.σ ^ 4 / (p.Ls * Δ * ε ^ 2) ≤ T →
      avg ≤ ε ∧ ∃ t : Fin p.T, ∫ ω, nuclearNorm (gradient f (W ω t.castSucc)) ∂P ≤ ε)

def Valid (p : Constants) : Prop :=
  0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.Ls ∧ 0 ≤ p.σ ∧ 0 < p.η ∧ 0 ≤ p.β ∧ p.β < 1 ∧
    1 ≤ p.B ∧ 1 ≤ p.T

structure Params extends OracleTemplate.MuonTuning.Public

noncomputable abbrev spec : Setup where
  Params := Params
  Public := OracleTemplate.MuonTuning.Public
  Instance p := Mat p.m p.n → ℝ
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Mat p.m p.n
  publicInput := Params.toPublic
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p f O :=
    LongTails.Setups.MuonSpectral.SpectralSmooth p.L f ∧ BddBelow (Set.range f) ∧
    f p.W0 - ⨅ W, f W ≤ p.Δ ∧
    LongTails.Setups.MuonFrobenius.StochasticOracleModel f p.σ O
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => nuclearNorm (gradient f (output ω))) (P : Measure _) ∧
    (∫ ω, nuclearNorm (gradient f (output ω)) ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm p A := A = OracleTemplate.MuonTuning.spectral p

attribute [local simp] publicInput SpectralSmooth averageNuclear Guarantee

end LongTails.Setups.MuonSpectral
