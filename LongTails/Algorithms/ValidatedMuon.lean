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

inductive ValidatedMuonState (m n T b k q : ℕ) where
  | training (seed : Fin (q + 1) → Fin (T + 1)) (i : Fin (T + 1))
      (x M : Space m n) (points : Fin (T + 1) → Space m n)
  | validating (sources : Fin (q + 1) → Space m n) (i : Fin (q + 1))
      (j : Fin (k + 1)) (sample : Fin b) (acc : Space m n)
      (means : Fin (k + 1) → Space m n) (reps : Fin (q + 1) → Space m n)
  | done (output : Space m n)

noncomputable def returnInitial {m n : ℕ} (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) where
  State := Unit
  initial _ := ()
  query _ := (0, x0)
  update _ _ := ()
  output _ := x0

noncomputable def validatedMuonDirect {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) where
  Seed := Fin (q + 1) → Fin (T + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure, inferInstance⟩
  State := ValidatedMuonState m n T b k q
  initial seed := .training seed ⟨0, by omega⟩ x0 0 (fun _ => x0)
  query
    | .training _ _ x _ _ => (0, x)
    | .validating sources i _ _ _ _ _ => (0, sources i)
    | .done _ => (0, x0)
  update
    | .training seed i x M points, g =>
        let (x', M') := trainingStep α η (x, M) g
        let points' := Function.update points i x
        if hlast : i.val + 1 = T + 1 then
          let sources := fun j => points' (seed j)
          if hb : 0 < b then
            .validating sources ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, hb⟩ 0
              (fun _ => 0) (fun _ => 0)
          else
            let G : Fin (q + 1) → Space m n := fun _ =>
              representative (m := m) (n := n) (k := k) ρ (fun _ => 0)
            .done (sources (bestIndex (m := m) (n := n) G))
        else
          .training seed ⟨i.val + 1, by omega⟩ x' M' points'
    | .validating sources i j sample acc means reps, g =>
        if hs : sample.val + 1 < b then
          .validating sources i j ⟨sample.val + 1, hs⟩ (acc + g) means reps
        else
          let means' := Function.update means j ((1 / (b : ℝ)) • (acc + g))
          if hj : j.val + 1 < k + 1 then
            .validating sources i ⟨j.val + 1, hj⟩ ⟨0, by omega⟩ 0 means' reps
          else
            let reps' := Function.update reps i (representative ρ means')
            if hi : i.val + 1 < q + 1 then
              .validating sources ⟨i.val + 1, hi⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ 0
                (fun _ => 0) reps'
            else
              .done (sources (bestIndex reps'))
    | .done output, _ => .done output
  output
    | .training _ _ _ _ _ => x0
    | .validating _ _ _ _ _ _ _ => x0
    | .done output => output

noncomputable def trajectory {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call : ℕ) : ℕ → Space m n × Space m n
  | 0 => state
  | t + 1 => trainingStep α η (trajectory α η g ξ state call t)
      (g (trajectory α η g ξ state call t).1 (ξ (call + t)))

noncomputable def validatedMuon {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  validatedMuonDirect α η ρ T b k q x0

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
