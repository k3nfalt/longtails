import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.FullRangeMlmc

open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def epochOf (n0 k : ℕ) : ℕ := Nat.clog 2 ((k + n0) / n0)

noncomputable def stepAt (γ0 : ℝ) (n0 k : ℕ) : ℝ := γ0 / (2 : ℝ) ^ epochOf n0 k

noncomputable def innerStep (J : ℝ → E → E) (η γ : ℝ) (x z p : E) : E :=
  J (γ * η) (z - γ • (z - x + η • p))

noncomputable def innerAdvance (J : ℝ → E → E) (g : E → Ω → E) (η γ0 : ℝ) (n0 : ℕ) (x : E)
    (s : ℕ × E) (ω : Ω) : ℕ × E :=
  (s.1 + 1, innerStep J η (stepAt γ0 n0 s.1) x s.2 (g s.2 ω))

noncomputable def innerPath (J : ℝ → E → E) (g : E → Ω → E) (η γ0 : ℝ) (n0 : ℕ) (x : E)
    (k : ℕ) (ξ : ℕ → Ω) : E :=
  (iterateSamples (innerAdvance J g η γ0 n0 x) k (0, x) (fun i : Fin k => ξ i)).2

noncomputable def levelTime (n0 l : ℕ) : ℕ := n0 * 2 ^ l

noncomputable def levelWeight (top l : ℕ) : ℝ :=
  if l = 0 then 1 / (2 : ℝ) ^ top else 1 / (2 : ℝ) ^ l

noncomputable def estimator (J : ℝ → E → E) (g : E → Ω → E) (η γ0 : ℝ) (n0 top : ℕ) (x : E)
    (l : ℕ) (ξ : ℕ → Ω) : E :=
  if l = 0 then innerPath J g η γ0 n0 x n0 ξ
  else innerPath J g η γ0 n0 x n0 ξ +
    (levelWeight top l)⁻¹ • (innerPath J g η γ0 n0 x (levelTime n0 l) ξ -
      innerPath J g η γ0 n0 x (levelTime n0 (l - 1)) ξ)

end LongTails.Algorithms.FullRangeMlmc
