import LongTails.Algorithms.MatrixPolar
import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.ValidatedMuon

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar

noncomputable def trainingPlan {m n : ℕ} (α η : ℝ) :
    (T : ℕ) → Space m n → Space m n → QueryPlan (Space m n) (Space m n) (Fin T → Space m n) T
  | 0, _, _ => .done Fin.elim0
  | T + 1, x, M => .ask x fun g =>
      (trainingPlan α η T (x - η • polar ((1 - α) • M + α • g))
        ((1 - α) • M + α • g)).map (Fin.cons x)

noncomputable def trainingStep {m n : ℕ} (α η : ℝ)
    (state : Space m n × Space m n) (g : Space m n) : Space m n × Space m n :=
  let M := (1 - α) • state.2 + α • g
  (state.1 - η • polar M, M)

noncomputable def trajectory {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call : ℕ) : ℕ → Space m n × Space m n
  | 0 => state
  | t + 1 => trainingStep α η (trajectory α η g ξ state call t)
      (g (trajectory α η g ξ state call t).1 (ξ (call + t)))

noncomputable def batchSumPlan {m n : ℕ} (x : Space m n) :
    (b : ℕ) → Space m n → QueryPlan (Space m n) (Space m n) (Space m n) b
  | 0, s => .done s
  | b + 1, s => .ask x fun g => batchSumPlan x b (s + g)

noncomputable def batchMeanPlan {m n : ℕ} (x : Space m n) (b : ℕ) :
    QueryPlan (Space m n) (Space m n) (Space m n) b :=
  (batchSumPlan x b 0).map fun s => (1 / (b : ℝ)) • s

def collect {Q R U : Type*} {c : ℕ} : (k : ℕ) → (Fin k → QueryPlan Q R U c) →
    QueryPlan Q R (Fin k → U) (c * k)
  | 0, _ => .done Fin.elim0
  | k + 1, plans => (plans 0).bind fun a =>
      (collect k (fun i => plans i.succ)).map (Fin.cons a)

noncomputable def representativeIndex {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Fin (k + 1) := by
  classical
  let S := Finset.univ.filter fun i =>
    k + 1 < 2 * (Finset.univ.filter fun j => nuclearNorm (B i - B j) ≤ ρ).card
  exact if h : S.Nonempty then S.min' h else 0

noncomputable def representative {m n k : ℕ} (ρ : ℝ)
    (B : Fin (k + 1) → Space m n) : Space m n := B (representativeIndex ρ B)

noncomputable def bestIndex {m n q : ℕ} (G : Fin (q + 1) → Space m n) : Fin (q + 1) := by
  classical
  let S := Finset.univ.filter fun i => ∀ j, nuclearNorm (G i) ≤ nuclearNorm (G j)
  exact if h : S.Nonempty then S.min' h else 0

noncomputable def validationPlan {m n : ℕ} (ρ : ℝ) (b k q : ℕ)
    (x : Fin (q + 1) → Space m n) :
    QueryPlan (Space m n) (Space m n) (Space m n) ((b * (k + 1)) * (q + 1)) :=
  (collect (q + 1) (fun i =>
    (collect (k + 1) (fun _ => batchMeanPlan (x i) b)).map (representative ρ))).map
      (fun G => x (bestIndex G))

noncomputable def returnInitial {m n : ℕ} (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) where
  State := Unit
  initial _ := ()
  query _ := (0, x0)
  update _ _ := ()
  output _ := x0

noncomputable def validatedMuon {m n : ℕ} (α η ρ : ℝ) (T b k q : ℕ) (x0 : Space m n) :
    Algorithm (Space m n) (Space m n) (Space m n) :=
  QueryPlan.algorithm
    ⟨(PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure, inferInstance⟩
    x0 x0 ((b * (k + 1)) * (q + 1) + (T + 1)) fun seed =>
      (trainingPlan α η (T + 1) x0 0).bind fun xs =>
        validationPlan ρ b k q (fun i => xs (seed i))

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
