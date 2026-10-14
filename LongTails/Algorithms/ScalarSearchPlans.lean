import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.ScalarHeavyTailEstimator
import LongTails.Algorithms.ScalarNoisySearch
import Mathlib.Data.Fin.VecNotation

namespace OracleTemplate.ScalarSearchPlans

open Classical

noncomputable def samplesPlan (x : ℝ) : (n : ℕ) → QueryPlan ℝ ℝ (Fin n → ℝ) n
  | 0 => .done Fin.elim0
  | n + 1 => .ask x (fun value => QueryPlan.map (Fin.cons value) (samplesPlan x n))

noncomputable def estimatePlan (σ p u : ℝ) (k : ℕ) (x : ℝ) :
    QueryPlan ℝ ℝ ℝ (ScalarHeavyTailEstimator.calls σ p u k) :=
  QueryPlan.map (fun samples => ScalarHeavyTailEstimator.estimate σ p u k
    (fun j => if h : j < ScalarHeavyTailEstimator.calls σ p u k then samples ⟨j, h⟩ else 0))
    (samplesPlan x (ScalarHeavyTailEstimator.calls σ p u k))

noncomputable def triplePlan (σ p u : ℝ) (k : ℕ) (x0 s : ℝ) (points : Fin 3 → ℝ) :
    QueryPlan ℝ ℝ (Fin 3 → ℝ) (3 * ScalarHeavyTailEstimator.calls σ p u k) := by
  let c := ScalarHeavyTailEstimator.calls σ p u k
  have he : (c + c) + c = 3 * c := by omega
  rw [← he]
  exact QueryPlan.bind (m := c + c) (k := c) (estimatePlan σ p u k (x0 + s * points 0)) (fun a =>
    QueryPlan.bind (m := c) (k := c) (estimatePlan σ p u k (x0 + s * points 1)) (fun b =>
      QueryPlan.map (fun d => ![s * a, s * b, s * d])
        (estimatePlan σ p u k (x0 + s * points 2))))

noncomputable def walkPlan (σ p ε x0 s : ℝ) (D : ℕ) :
    (n : ℕ) → List ScalarNoisySearch.Node →
      QueryPlan ℝ ℝ (List ℝ) (3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * n)
  | 0, _ => .done []
  | n + 1, path =>
      QueryPlan.bind (triplePlan σ p (ε / 96) 6 x0 s
        (ScalarNoisySearch.queries (path.headD (.interval 0 0 0))))
        (fun values => QueryPlan.map (ScalarNoisySearch.recordedPoint 0 path :: ·)
          (walkPlan σ p ε x0 s D n (ScalarNoisySearch.advance ε D (2 * D) values path)))

noncomputable def rootAttemptPlan (σ p ε x0 s hi : ℝ) (D time : ℕ) :
    QueryPlan ℝ ℝ (ℝ × ℝ)
      (ScalarHeavyTailEstimator.calls σ p (ε / 48) 6 +
        3 * ScalarHeavyTailEstimator.calls σ p (ε / 96) 6 * (16 * D)) :=
  QueryPlan.bind (walkPlan σ p ε x0 s D (16 * D) [.interval 0 hi 0])
    (fun records =>
      let x := x0 + s * records[time]?.getD 0
      QueryPlan.map (fun value => (x, value)) (estimatePlan σ p (ε / 48) 6 x))

end OracleTemplate.ScalarSearchPlans
