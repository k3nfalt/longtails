import LongTails.Template
import Mathlib.Algebra.Module.Basic

open OracleTemplate

namespace LongTails.Algorithms.FirstFitGradientDescent

variable {E : Type} [Add E] [SMul ℝ E]

noncomputable def algorithm (x₀ : E) (η : ℝ) : Algorithm E (E × Bool) E where
  State := E
  initial := fun _ => x₀
  query x := (0,x)
  update x reply := if reply.2 then x else x + η • reply.1
  output := id

noncomputable def output (x₀ : E) (η : ℝ) (o : Oracle E (E × Bool)) (queries : ℕ)
    (ξ : (k : ℕ) → o.Seed k) : E :=
  execute o (algorithm x₀ η) (fun _ => queries) () ξ

end LongTails.Algorithms.FirstFitGradientDescent
