import LongTails.Template
import LongTails.Algorithms.LinearDecaySgd
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.SampledComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def path {Ξ : Type*} (grad : Ξ → E → E) (prox : ℝ → E → E → E) (η : ℝ) (T : ℕ)
    (x0 : E) (ξ : ℕ → Ξ) : ℕ → E
  | 0 => x0
  | k + 1 =>
    prox (η * ((T : ℝ) - k) / T) (path grad prox η T x0 ξ k)
      (grad (ξ (2 * k)) (path grad prox η T x0 ξ k))

noncomputable def proximalLinearDecaySgd (η : ℝ) (T : ℕ) (x0 : E) :
    Algorithm (E ⊕ (ℝ × E × E)) E E where
  State := ℕ × Bool × E × E
  initial _ := (0, false, x0, 0)
  query s :=
    if s.2.1 then (0, Sum.inr (η * ((T : ℝ) - s.1) / T, s.2.2.1, s.2.2.2))
    else (0, Sum.inl s.2.2.1)
  update s r := if s.2.1 then (s.1 + 1, false, r, s.2.2.2) else (s.1, true, s.2.2.1, r)
  output s := s.2.2.1

end OracleTemplate.SampledComposite
