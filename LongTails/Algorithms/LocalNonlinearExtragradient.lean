import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.LocalNonlinearExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def step (η : ℝ) (g : E → Ω → E) (x : E) (first second : Ω) : E :=
  x - η • g (x - η • g x first) second

noncomputable def run (η : ℝ) (g : E → Ω → E) (x : E) (samples : ℕ → Ω) : ℕ → E
  | 0 => x
  | k + 1 => step η g (run η g x samples k) (samples (2 * k)) (samples (2 * k + 1))

noncomputable def warmRun (η : ℝ) (g : E → Ω → E) (x : E) (samples : ℕ → Ω) : ℕ → E
  | 0 => x
  | k + 1 => warmRun η g x samples k - η • g (warmRun η g x samples k) (samples k)

end LongTails.Algorithms.LocalNonlinearExtragradient
