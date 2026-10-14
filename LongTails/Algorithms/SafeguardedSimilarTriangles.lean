import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.LocalHiddenConvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ballProj (x0 : E) (r : ℝ) (w : E) : E :=
  if ‖w - x0‖ ≤ r then w else x0 + (r / ‖w - x0‖) • (w - x0)

noncomputable def stepScale (L σ R : ℝ) (k : ℕ) : ℝ :=
  4 * L + σ * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) / R

noncomputable def mixPoint (k : ℕ) (x z : E) : E :=
  ((k : ℝ) / ((k : ℝ) + 2)) • x + (2 / ((k : ℝ) + 2)) • z

noncomputable def dualStep (L σ R : ℝ) (x0 : E) (k : ℕ) (z g : E) : E :=
  ballProj x0 (2 * R) (z - (((k : ℝ) + 1) / (2 * stepScale L σ R k)) • g)

noncomputable def safeguardedSimilarTriangles (L σ R : ℝ) (x0 : E) : Algorithm E E E where
  State := ℕ × E × E
  initial _ := (0, x0, x0)
  query s := (0, mixPoint s.1 s.2.1 s.2.2)
  update s g :=
    (s.1 + 1, mixPoint s.1 s.2.1 (dualStep L σ R x0 s.1 s.2.2 g), dualStep L σ R x0 s.1 s.2.2 g)
  output s := s.2.1

noncomputable def safeguardedRun (g : E → Ω → E) (L σ R : ℝ) (x0 : E) :
    (K : ℕ) → ℕ → E → E → (Fin K → Ω) → E × E
  | 0, _, x, z, _ => (x, z)
  | K + 1, k, x, z, ξ =>
      let z' := dualStep L σ R x0 k z (g (mixPoint k x z) (ξ 0))
      safeguardedRun g L σ R x0 K (k + 1) (mixPoint k x z') z' (fun i => ξ i.succ)

end OracleTemplate.LocalHiddenConvex
