import LongTails.Setups.StochasticSmoothNonconvex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Distributions.Uniform

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def update (η : ℝ) (s : ℕ × E × E) (g : E) : ℕ × E × E :=
  (s.1 - 1, s.2.1 - η • g, if s.1 = 1 then s.2.1 else s.2.2)

noncomputable def randomSgd (η : ℝ) (N : ℕ) [NeZero N] (x0 : E) : Algorithm E E E where
  Seed := Fin N
  law := ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩
  State := ℕ × E × E
  initial i := (i.val + 1, x0, x0)
  query s := (0, s.2.1)
  update := update η
  output s := s.2.2

noncomputable def selected (g : E → Ω → E) (η : ℝ) :
    (K : ℕ) → E → (Fin K → Ω) → Fin K → E
  | 0, _, _, i => Fin.elim0 i
  | K + 1, x, ξ, i => Fin.cases x
      (fun j => selected g η K (x - η • g x (ξ 0)) (fun k => ξ k.succ) j) i

noncomputable def tunedSgd (p : Params) : Algorithm p.E p.E p.E :=
  let η := 1 / (p.L + 2 * p.L * p.σ ^ 2 / p.ε ^ 2)
  let K := ⌈4 * p.L * p.Δ / p.ε ^ 2 + 8 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊ + 1
  randomSgd η K p.x0

end OracleTemplate.StochasticNonconvex
