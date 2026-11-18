import LongTails.Algorithms.AbcSgd
import LongTails.Algorithms.AcceleratedMarkov
import LongTails.Setups.MarkovSmoothNonconvex

namespace LongTails.Algorithms.MarkovClippedSgd

open OracleTemplate HeavyTailedMarkovGradient AbcSgd LongTails.Setups.MarkovSmoothNonconvex

noncomputable def clipped {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η C : ℝ) (K : ℕ) (x0 : E) : Algorithm E E E :=
  let A := sampledSgd η K x0
  { A with update := fun s v => A.update s (clip C v) }

noncomputable def point {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Z → E) (η C : ℝ) (m : ℕ) (x0 : E) (z : ℕ → Z) : ℕ → E
  | 0 => x0
  | k + 1 =>
    let x := point g η C m x0 z k
    x - η • clip C (g x (z (k * m)))

noncomputable def output {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Z → E) (η C : ℝ) (m : ℕ) (x0 : E) {K : ℕ} (i : Fin (K + 1)) (z : ℕ → Z) : E :=
  point g η C m x0 z i.val

noncomputable def threshold (p : Params) : ℝ := 64 * p.σ ^ 2 / p.ε

noncomputable def stepSize (p : Params) : ℝ := p.ε / (64 * p.L * threshold p)

noncomputable def steps (p : Params) : ℕ := ⌈32768 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊

noncomputable def period (p : Params) : ℕ := ⌈p.τ * Real.log (8192 * p.σ ^ 2 / p.ε ^ 2)⌉₊

noncomputable def algorithm (p : Params) : Algorithm (Space p) (Space p) (Space p) :=
  spaced (period p) (clipped (stepSize p) (threshold p) (steps p) p.x0)

end LongTails.Algorithms.MarkovClippedSgd
