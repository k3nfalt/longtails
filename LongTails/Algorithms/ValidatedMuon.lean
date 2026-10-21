import LongTails.Setups.FiniteVarianceSpectralSmooth

namespace LongTails.Algorithms.ValidatedMuon

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar LongTails.Setups.FiniteVarianceSpectralSmooth

noncomputable abbrev trainingStep {m n : ℕ} (α η : ℝ)
    (state : Space m n × Space m n) (g : Space m n) : Space m n × Space m n :=
  LongTails.Setups.FiniteVarianceSpectralSmooth.trainingStep α η state g

noncomputable abbrev representativeIndex {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Fin (k + 1) :=
  LongTails.Setups.FiniteVarianceSpectralSmooth.representativeIndex ρ B

noncomputable abbrev representative {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Space m n :=
  LongTails.Setups.FiniteVarianceSpectralSmooth.representative ρ B

noncomputable abbrev bestIndex {m n q : ℕ} (G : Fin (q + 1) → Space m n) : Fin (q + 1) :=
  LongTails.Setups.FiniteVarianceSpectralSmooth.bestIndex G

noncomputable def trajectory {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call : ℕ) : ℕ → Space m n × Space m n
  | 0 => state
  | t + 1 => trainingStep α η (trajectory α η g ξ state call t)
      (g (trajectory α η g ξ state call t).1 (ξ (call + t)))

noncomputable def validatedMuon {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  validatedMuonDirect α η ρ T b k q x0

noncomputable def returnInitial {m n : ℕ} (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  LongTails.Setups.FiniteVarianceSpectralSmooth.returnInitial x0

noncomputable def finiteVarianceMuon {m n : ℕ} (L Δ s ε δ : ℝ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) := by
  classical
  let e := ε / 8
  let γ := δ / 4
  let D := L * Δ / e ^ 2
  let a := max 1 (4096 * s ^ 2 / e ^ 2)
  let H := Real.log (1073741824 * a * D / γ)
  let T := ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊
  let q := ⌈Real.log (1 / γ) / Real.log 2⌉₊
  let b := max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊
  let k := ⌈8 * Real.log ((q : ℝ) / γ)⌉₊
  exact if 2 * L * Δ ≤ ε ^ 2 then returnInitial x0 else
    validatedMuon (1 / a) (Δ / (e * T)) (2 * e / 3) (T - 1) b (k - 1) (q - 1) x0

end LongTails.Algorithms.ValidatedMuon
