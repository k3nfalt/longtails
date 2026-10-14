import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

namespace OracleTemplate.SaddlePoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def project (X : Set E) (x : E) : E := by
  classical
  exact if h : ∃ p ∈ X, ‖x - p‖ = ⨅ q : X, ‖x - q‖ then h.choose else 0

noncomputable def start (X : Set E) : E := by
  classical
  exact if h : X.Nonempty then h.choose else 0

noncomputable def prox (X : Set E) (Y : Set F) (η : ℝ) (z g : E × F) : E × F :=
  (project X (z.1 - η • g.1), project Y (z.2 - η • g.2))

abbrev ExtraState (E F : Type*) := Bool × ℕ × (E × F) × (E × F) × (E × F)

noncomputable def extragradient (p : ℝ × ℝ × ℝ × Set E × Set F) :
    Algorithm (E × F) (E × F) (E × F) where
  State := ExtraState E F
  initial := fun _ => (false, 0, (start p.2.2.2.1, start p.2.2.2.2), 0, 0)
  query :=  fun (phase, _, z, w, _) => (0, if phase then w else z)
  update := fun (phase, n, z, w, total) g =>
    if phase then (false, n + 1, prox p.2.2.2.1 p.2.2.2.2 (1 / (2 * p.1)) z g, w, total + w)
    else (true, n, z, prox p.2.2.2.1 p.2.2.2.2 (1 / (2 * p.1)) z g, total)
  output := fun (_, n, z, _, total) => if n = 0 then z else (n : ℝ)⁻¹ • total

end OracleTemplate.SaddlePoint
