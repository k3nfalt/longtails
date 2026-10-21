import outputs.Algorithms.SimplifiedMuon
import Mathlib.Analysis.Calculus.Gradient.Basic

open MeasureTheory

namespace outputs.Setups.MuonThirdOrder

open OracleTemplate OracleTemplate.Muon

structure Params where
  m : ℕ
  n : ℕ
  s : ℝ
  η : ℝ
  T : ℕ
  W0 : Mat m n

def publicInput (p : Params) : SimplifiedMuon.Public := ⟨p.m, p.n, p.η, p.T, p.W0⟩

def ThirdDerivativeBounded {m n : ℕ} (s : ℝ) (f : Mat m n → ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ (fderiv ℝ f) ∧ Differentiable ℝ (iteratedFDeriv ℝ 2 f) ∧
    ∀ W U V X, |iteratedFDeriv ℝ 3 f W ![U, V, X]| ≤ s * ‖U‖ * ‖V‖ * ‖X‖

noncomputable def hessianQuadratic {m n : ℕ} (f : Mat m n → ℝ) (W : Mat m n) : ℝ :=
  iteratedFDeriv ℝ 2 f W ![orthogonalize (gradient f W), orthogonalize (gradient f W)]

def Guarantee (p : Params) (f : Mat p.m p.n → ℝ) (W : Fin (p.T + 1) → Mat p.m p.n) : Prop :=
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

noncomputable abbrev spec : Setup where
  Params := Params
  Public := SimplifiedMuon.Public
  Instance p := Mat p.m p.n → ℝ
  Query p := Mat p.m p.n
  Reply p := Mat p.m p.n
  Output p := Fin (p.T + 1) → Mat p.m p.n
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 ≤ p.s ∧ 0 < p.η ∧ 1 ≤ p.T
  admissible p f O :=
    ThirdDerivativeBounded p.s f ∧ BddBelow (Set.range f) ∧
      ∀ k W seed, O.answer k (0, W) seed = gradient f W
  successful p f W _ := ∀ ω, Guarantee p f (W ω)
  allowedAlgorithm q A := A = SimplifiedMuon.simplifiedMuon q

attribute [local simp] publicInput ThirdDerivativeBounded hessianQuadratic Guarantee

end outputs.Setups.MuonThirdOrder
