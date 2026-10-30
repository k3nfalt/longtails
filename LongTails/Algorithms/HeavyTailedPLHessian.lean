import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Algorithms.Batched
import LongTails.Algorithms.MarkovQuadraticSgd
import LongTails.Setups.PLHessianLipschitzKurtosis

namespace OracleTemplate.HeavyTailedPLHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def pilot (v : Fin 8 → Fin 8 → E) : E :=
  MultiplicativeRobustEstimator.medoid
    (fun i => MultiplicativeRobustEstimator.medoid (v i))

noncomputable def estimate (τ : ℝ) (v : Fin 8 → Fin 8 → E) (y : E) : E :=
  RobustGradient.centeredClip τ (pilot v) y

def pilotIndex (i j : Fin 8) : Fin 65 := ⟨8 * i.val + j.val, by omega⟩

noncomputable def flatEstimate (τ : ℝ) (v : Fin 65 → E) : E :=
  estimate τ (fun i j => v (pilotIndex i j)) (v (Fin.last 64))

noncomputable def iterate {Ω : Type*} (g : E → Ω → E) (η τ : ℝ) (x0 : E)
    (ξ : ℕ → Fin 65 → Ω) (k : ℕ) : E :=
  MarkovQuadratic.iterate (fun x block => flatEstimate τ (fun i => g x (block i))) η x0 ξ k

noncomputable def output {Ω : Type*} (g : E → Ω → E) (η τ : ℝ) (x0 : E)
    (n m : ℕ) (seed : Fin (m + 1)) (ξ : ℕ → Fin 65 → Ω) : E :=
  iterate g η τ x0 ξ (n + seed.val)

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def method (η τ : ℝ) (n m : ℕ) (x0 : F) : Algorithm F F F :=
  batched (by norm_num : 0 < 65) (WindowSgd.method η n m x0)
    (fun state _ => state.2.2) (fun _ replies => flatEstimate τ replies) 0

end OracleTemplate.HeavyTailedPLHessian
