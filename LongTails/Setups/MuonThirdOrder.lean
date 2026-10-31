import LongTails.Setups.MuonFrobenius
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace OracleTemplate.SimplifiedMuon

open Muon

structure Public where
  m : ℕ
  n : ℕ
  η : ℝ
  T : ℕ
  W0 : Mat m n

structure State (p : Public) where
  iter : ℕ
  point : Mat p.m p.n
  iterates : ℕ → Mat p.m p.n

noncomputable def step (p : Public) (s : State p) (G : Mat p.m p.n) : State p :=
  let W := s.point - p.η • orthogonalize G
  ⟨s.iter + 1, W, Function.update s.iterates (s.iter + 1) W⟩

noncomputable def simplifiedMuon (p : Public) :
    Algorithm (Mat p.m p.n) (Mat p.m p.n) (Fin (p.T + 1) → Mat p.m p.n) where
  State := State p
  initial _ := ⟨0, p.W0, fun _ => p.W0⟩
  query s := (0, s.point)
  update := step p
  output s := fun j => s.iterates j

noncomputable def trajectory (p : Public) (G : Mat p.m p.n → Mat p.m p.n) (t : ℕ) : Mat p.m p.n :=
  (fun W => W - p.η • orthogonalize (G W))^[t] p.W0

attribute [local simp] step simplifiedMuon trajectory

end OracleTemplate.SimplifiedMuon

namespace OracleTemplate.MuonBest

open OracleTemplate OracleTemplate.Muon

structure Public where
  m : ℕ
  n : ℕ
  s : ℝ
  J : ℝ
  Δ : ℝ
  ε : ℝ
  W0 : Mat m n

noncomputable def horizon (p : Public) : ℕ := ⌈8 * p.J * p.Δ / p.ε ^ 2 + 2 * p.s * (((min p.m p.n : ℕ) : ℝ) * Real.sqrt ((min p.m p.n : ℕ) : ℝ)) * p.Δ / (3 * p.J * p.ε)⌉₊ + 1

noncomputable def stepSize (p : Public) : ℝ :=
  Real.sqrt (2 * p.Δ / (p.J * (horizon p : ℝ)))

noncomputable def sourceInput (p : Public) : OracleTemplate.SimplifiedMuon.Public :=
  ⟨p.m, p.n, stepSize p, horizon p, p.W0⟩

structure State (p : Public) where
  point : Mat p.m p.n
  best : Mat p.m p.n
  score : ℝ
  seen : Bool

def initial (p : Public) : State p := ⟨p.W0, p.W0, 0, false⟩

noncomputable def step (p : Public) (st : State p) (G : Mat p.m p.n) : State p :=
  let score := nuclearNorm G
  let point := st.point - stepSize p • orthogonalize G
  if st.seen = false ∨ score ≤ st.score then ⟨point, st.point, score, true⟩
  else ⟨point, st.best, st.score, true⟩

noncomputable def algorithm (p : Public) : Algorithm (Mat p.m p.n) (Mat p.m p.n) (Mat p.m p.n) where
  State := State p
  initial _ := initial p
  query st := (0, st.point)
  update := step p
  output st := st.best

noncomputable def stateAt (p : Public) (G : Mat p.m p.n → Mat p.m p.n) (K : ℕ) : State p :=
  (fun st => step p st (G st.point))^[K] (initial p)

attribute [local simp] horizon stepSize sourceInput initial step algorithm stateAt

end OracleTemplate.MuonBest

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
