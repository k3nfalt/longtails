import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.Clipping
import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Proofs.SgdExecution

namespace LongTails.Algorithms.StochasticEnvelopePilot

open OracleTemplate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def robustMean {b n : ℕ}
    (v : Fin (n + 1) → Fin 8 → Fin (b + 1) → E) : E :=
  MultiplicativeRobustEstimator.medoid (fun i =>
    MultiplicativeRobustEstimator.medoid (fun j =>
      MultiplicativeRobustEstimator.blockMean (v i j)))

noncomputable def update (L μ β : ℝ) (center : E) (state : E × E) (reply : E) : E × E :=
  let θ := InexactGradient.momentum (L + μ) μ (2 * β)
  InexactGradient.step (L + μ) μ θ state
    (reply + μ • (InexactGradient.query θ state - center))

noncomputable def bounded (L μ β radius : ℝ) (center : E) : Algorithm E E E where
  State := E × E
  initial _ := (center, center)
  query state := (0, InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β)) state)
  update state reply :=
    let next := update L μ β center state reply
    (center + clip radius (next.1 - center), center + clip radius (next.2 - center))
  output state := state.1

noncomputable def boundedRun (L μ β radius : ℝ) (center : E) (answer : ℕ → E → E)
    (N call : ℕ) : E × E :=
  let A := bounded L μ β radius center
  StochasticGradient.advance (fun k state => A.update state (answer k (A.query state).2))
    N call (center, center)

noncomputable def sampledReply {Ω : Type*} (g : E → Ω → E) (θ : ℝ)
    {b n : ℕ} (state : E × E) (ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) : E :=
  robustMean (fun i j k => g (InexactGradient.query θ state) (ξ i j k))

noncomputable def sampledStep {Ω : Type*} (g : E → Ω → E)
    (L μ β radius : ℝ) (center : E) {b n : ℕ} (state : E × E)
    (ξ : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) : E × E :=
  let reply := sampledReply g (InexactGradient.momentum (L + μ) μ (2 * β)) state ξ
  let next := update L μ β center state reply
  (center + clip radius (next.1 - center), center + clip radius (next.2 - center))

noncomputable def sampledRun {Ω : Type*} (g : E → Ω → E)
    (L μ β radius : ℝ) (center : E) {b n : ℕ}
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) : E × E :=
  StochasticGradient.advance (fun k state => sampledStep g L μ β radius center state (ξ k))
    N 0 (center, center)

noncomputable def localizedRadius {Ω : Type*} (g : E → Ω → E)
    (L μ s β : ℝ) (center : E) {b n : ℕ}
    (rough : Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω)
    (ξ : ℕ → Fin (n + 1) → Fin 8 → Fin (b + 1) → Ω) (N : ℕ) : ℝ :=
  let estimate := robustMean (fun i j k => g center (rough i j k))
  let S := 4 * (‖estimate‖ + s) / μ
  let radius := 72 * Real.sqrt ((L + μ) / μ) * S
  let point := (sampledRun g L μ β radius center ξ N).1
  2 * ‖center - point‖ + 128 * s / μ

noncomputable def run (L μ β : ℝ) (center : E) (answer : ℕ → E → E)
    (N call : ℕ) : E × E :=
  StochasticGradient.advance
    (fun k state => update L μ β center state
      (answer k (InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β)) state)))
    N call (center, center)

end LongTails.Algorithms.StochasticEnvelopePilot
