import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Algorithms.NormalizedSam

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def method (η ρ : ℝ) (x0 : E) : OracleTemplate.Algorithm E E E 1 where
  State := E × E × Bool
  initial _ := (x0, 0, false)
  query s := (0, if s.2.2 then s.1 + (ρ / ‖s.2.1‖) • s.2.1 else s.1)
  update s reply := if s.2.2 then (s.1 - η • reply, 0, false) else (s.1, reply, true)
  output s := s.1

noncomputable def step (g : E → E) (η ρ : ℝ) (x : E) : E :=
  x - η • g (x + (ρ / ‖g x‖) • g x)

noncomputable def output (g : E → E) (η ρ : ℝ) (x0 : E) (T : ℕ) : E :=
  (step g η ρ)^[T] x0

end LongTails.Algorithms.NormalizedSam
