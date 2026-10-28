import LongTails.Algorithms.SimplifiedMuon
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace LongTails.Setups.MuonThirdOrder

open OracleTemplate OracleTemplate.Muon

structure Constants where
  m : ℕ
  n : ℕ
  s : ℝ
  η : ℝ
  T : ℕ
  W0 : Mat m n

def publicInput (p : Constants) : SimplifiedMuon.Public := ⟨p.m, p.n, p.η, p.T, p.W0⟩

def ThirdDerivativeBounded {m n : ℕ} (s : ℝ) (f : Mat m n → ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ (fderiv ℝ f) ∧ Differentiable ℝ (iteratedFDeriv ℝ 2 f) ∧
    ∀ W U V X, |iteratedFDeriv ℝ 3 f W ![U, V, X]| ≤ s * ‖U‖ * ‖V‖ * ‖X‖

noncomputable def hessianQuadratic {m n : ℕ} (f : Mat m n → ℝ) (W : Mat m n) : ℝ :=
  iteratedFDeriv ℝ 2 f W ![orthogonalize (gradient f W), orthogonalize (gradient f W)]

def Guarantee (p : Constants) (f : Mat p.m p.n → ℝ) (W : Fin (p.T + 1) → Mat p.m p.n) : Prop :=
  let r : ℝ := (min p.m p.n : ℕ)
  let T : ℝ := p.T
  let Δ : ℝ := f p.W0 - ⨅ W, f W
  let avg := (1 / T) * ∑ t : Fin p.T, nuclearNorm (gradient f (W t.castSucc))
  let J := (1 / T) * ∑ t : Fin p.T, hessianQuadratic f (W t.castSucc)
  avg ≤ (f (W 0) - f (W (Fin.last p.T))) / (T * p.η) + p.η * J / 2 +
      p.s * p.η ^ 2 * (r * Real.sqrt r) / 6 ∧
  (0 < J → p.η = Real.sqrt (2 * Δ / (J * T)) →
    avg ≤ Real.sqrt (2 * J * Δ / T) + p.s * (r * Real.sqrt r) * Δ / (3 * J * T) ∧
    ∀ ε > 0, 8 * J * Δ / ε ^ 2 ≤ T → 2 * p.s * (r * Real.sqrt r) * Δ / (3 * J * ε) ≤ T →
      avg ≤ ε ∧ ∃ t : Fin p.T, NuclearStationary f (W t.castSucc) ε)

def Valid (p : Constants) : Prop :=
  0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.s ∧ 0 < p.η ∧ 1 ≤ p.T

structure Params extends OracleTemplate.MuonBest.Public

noncomputable abbrev spec : Setup where
  Params := Params
  Public := OracleTemplate.MuonBest.Public
  Instance p := Mat p.m p.n → ℝ
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Mat p.m p.n
  publicInput := Params.toPublic
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.s ∧ 0 < p.J ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p f O :=
    LongTails.Setups.MuonThirdOrder.ThirdDerivativeBounded p.s f ∧ BddBelow (Set.range f) ∧
    f p.W0 - ⨅ W, f W ≤ p.Δ ∧
    (∀ W, LongTails.Setups.MuonThirdOrder.hessianQuadratic f W ≤ p.J) ∧
    ∀ k W seed, O.answer k (0, W) seed = gradient f W
  successful p f output _ := ∀ ω, nuclearNorm (gradient f (output ω)) ≤ p.ε
  allowedAlgorithm p A := A = OracleTemplate.MuonBest.algorithm p

attribute [local simp] publicInput ThirdDerivativeBounded hessianQuadratic Guarantee

end LongTails.Setups.MuonThirdOrder
