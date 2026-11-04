import LongTails.Algorithms.TaylorCorrectedNewton
import LongTails.Algorithms.TensorFreeModel
import LongTails.Algorithms.QuarticProximal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.QuarticProximalTrial

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Algorithms.TaylorCorrectedNewton LongTails.Algorithms.QuarticProximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev epochCount : ℕ := 2 ^ 17

abbrev StageSeed (n J : ℕ) := Fin (J + 1) → RestartSeed n epochCount

noncomputable def stage {n : ℕ} (L γ Δ : ℝ) (c y0 : E) (J : ℕ) (seed : StageSeed n J) :
    QueryPlan (Fin n × E) (Reply E) E (((n + n) * epochCount) * (J + 1)) :=
  let ρ := (12 * Δ / γ) ^ (1 / 4 : ℝ)
  let η := 1 / (32 * L * ρ ^ 2)
  let μ := Δ / (16 * ρ ^ 2)
  augmentPlan (augment γ μ c y0) (restarts η ρ y0 epochCount (J + 1) y0 seed)

noncomputable def stages {n : ℕ} (L γ : ℝ) (c : E) (J : ℕ) :
    (S : ℕ) → ℝ → E → (Fin S → StageSeed n J) →
      QueryPlan (Fin n × E) (Reply E) E ((((n + n) * epochCount) * (J + 1)) * S)
  | 0, _, y, _ => .done y
  | S + 1, Δ, y, seed => QueryPlan.bind (stage L γ Δ c y J (seed 0))
      (fun next => stages L γ c J S ((3 / 4 : ℝ) * Δ) next (fun i => seed i.succ))


noncomputable def modelSolve {n : ℕ} (ε R Q L γ : ℝ) (c z : E) :
    QueryPlan (Fin n × E) (Reply E) (TensorFreeModel.ModelState E)
      ((n + (n + n)) * (5000 * (1 + ⌈Real.log Q⌉₊) + 1) + n) :=
  augmentPlan (augment γ 0 c c)
    (TensorFreeModel.solveModel L (1 / Q ^ 142) (R * Q ^ 18) (ε / (R * Q ^ 84)) (ε / (R * Q ^ 12)) z
      (5000 * (1 + ⌈Real.log Q⌉₊)))


inductive TrialResult (E : Type*)
  | accurate (point : E)
  | proximal (point gradient : E)
  | failed

noncomputable def classify (γ tol : ℝ) (c y g : E) : TrialResult E := by
  classical
  exact if ‖g‖ ≤ γ * ‖y - c‖ ^ 3 / 32 then .proximal y (g - γ • grad (y - c))
    else if ‖g‖ ≤ tol then .accurate y else .failed

def padResult {n : ℕ} {U : Type*} (q : Fin n × E) : (k : ℕ) → U → QueryPlan (Fin n × E) (Reply E) U k
  | 0, u => .done u
  | k + 1, u => .ask q (fun _ => padResult q k u)

noncomputable def logarithm (Q : ℝ) : ℕ := 1 + ⌈Real.log Q⌉₊

noncomputable def modelCost (n : ℕ) (Q : ℝ) : ℕ := (n + (n + n)) * (5000 * logarithm Q + 1) + n

noncomputable def stagesCost (n : ℕ) (Q : ℝ) : ℕ :=
  (((n + n) * epochCount) * (24 * logarithm Q + 1)) * (64 * logarithm Q)

noncomputable def trialCost (n : ℕ) (Q : ℝ) : ℕ :=
  ((modelCost n Q + stagesCost n Q) + modelCost n Q) + modelCost n Q

noncomputable def trial {n : ℕ} [NeZero n] (ε R Q L γ : ℝ) (x0 c : E)
    (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
    QueryPlan (Fin n × E) (Reply E) (TrialResult E) (trialCost n Q) := by
  classical
  exact QueryPlan.bind (modelSolve ε R Q L γ c c) (fun first =>
    let z0 := c + first.displacement
    if ‖first.trueGradient‖ ≤ ε / (R * Q ^ 12) then
      padResult (0, x0) ((modelCost n Q + stagesCost n Q) + modelCost n Q)
        (classify γ (ε / (R * Q ^ 12)) c z0 first.trueGradient)
    else QueryPlan.bind (modelSolve ε R Q L γ c z0) (fun second =>
      let y0 := z0 + second.displacement
      if ‖second.trueGradient‖ ≤ ε / (R * Q ^ 12) then
        padResult (0, x0) (modelCost n Q + stagesCost n Q)
          (classify γ (ε / (R * Q ^ 12)) c y0 second.trueGradient)
      else
        let Δ := 3 * (‖second.trueGradient‖ ^ 4 / γ) ^ (1 / 3 : ℝ)
        QueryPlan.bind (stages L γ c (24 * logarithm Q) (64 * logarithm Q) Δ y0 seed) (fun y =>
          QueryPlan.map (fun last => classify γ (ε / (R * Q ^ 12)) c (y + last.displacement) last.trueGradient)
            (modelSolve ε R Q L γ c y))))

end LongTails.Algorithms.QuarticProximalTrial
