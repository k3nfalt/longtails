import LongTails.Algorithms.StochasticEnvelopePilot
import LongTails.Algorithms.AcceleratedMarkov
import LongTails.Algorithms.MultiplicativeRobustEstimator

namespace LongTails.Algorithms.StochasticEnvelopeLocalization

open OracleTemplate

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stage (g : E → Ω → E) (L μ p s a U D : ℝ) (center anchor : E)
    (K n : ℕ) (ξ : Fin (n + 1) → ℕ → Ω) : E :=
  let σ := s + a * μ * U + 2 * a * L * D
  let e := μ * D ^ 2 / 131072
  let Λ := 2 * (L + μ) + e * (K : ℝ) ^ 2 / (16 * D ^ 2)
  let C := 4 * (L + μ) * D + e / D * (256 * σ * D / e) ^ (p / (p - 1))
  MultiplicativeRobustEstimator.medoid (fun i =>
    (HeavyTailedMarkovGradient.clippedRun (fun x ω => g x ω + μ • (x - center))
      Λ D C 1 anchor (ξ i) K).2.1)

noncomputable def refineStep (g : E → Ω → E) (L μ p s a U n : ℝ) (center : E)
    (K replicas : ℕ) (state : ℕ × E) (ξ : Fin (replicas + 1) → ℕ → Ω) : ℕ × E :=
  let D := U / (2 : ℝ) ^ state.1
  let point := if D ≤ (s / μ + a * U) * n ^ (-(p - 1) / p) then state.2
    else stage g L μ p s a U D center state.2 K replicas ξ
  (state.1 + 1, point)

noncomputable def refineRun (g : E → Ω → E) (L μ p s a U n : ℝ) (center start : E)
    (K replicas : ℕ) (ξ : ℕ → Fin (replicas + 1) → ℕ → Ω) : ℕ → E
  | 0 => start
  | j + 1 =>
      let anchor := refineRun g L μ p s a U n center start K replicas ξ j
      let D := U / (2 : ℝ) ^ j
      if D ≤ (s / μ + a * U) * n ^ (-(p - 1) / p) then anchor
      else stage g L μ p s a U D center anchor K replicas (ξ j)

noncomputable def approximate (g : E → Ω → E) (L μ p s a n β : ℝ) (center : E)
    (b pilotReplicas innerReplicas pilotSteps K J : ℕ)
    (rough : Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)
    (pilot : ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)
    (inner : ℕ → Fin (innerReplicas + 1) → ℕ → Ω) : E :=
  let U := StochasticEnvelopePilot.localizedRadius g L μ s β center rough pilot pilotSteps
  refineRun g L μ p s a U n center center K innerReplicas inner J

end LongTails.Algorithms.StochasticEnvelopeLocalization
