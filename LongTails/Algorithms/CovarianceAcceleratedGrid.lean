import LongTails.Algorithms.CovarianceAccelerated

namespace LongTails.Algorithms.CovarianceAcceleratedGrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def grid (R ε : ℝ) : Finset E := by
  classical
  exact @Classical.epsilon (Finset E) ⟨{0}⟩ (fun S =>
    0 ∈ S ∧ (∀ z ∈ S, ‖z‖ ≤ R) ∧ ∀ x : E, ‖x‖ ≤ R → ∃ z ∈ S, ‖x - z‖ ≤ ε)

noncomputable def centers (R ε a : ℝ) : Fin (Fintype.card ↥(grid (E := E) R ε) + 1) → E :=
  Fin.cases 0 (fun i => a⁻¹ • ((Fintype.equivFin ↥(grid (E := E) R ε)).symm i).val)

noncomputable def config (x0 : E) (R ε a η β γ : ℝ) (window : ℕ) :
    CovarianceAccelerated.Config E (Fintype.card ↥(grid (E := E) R ε) + 1) where
  centers := centers R ε a
  initialIndex := 0
  x0 := x0
  window := window
  a := a
  η := η
  β := β
  γ := γ

end LongTails.Algorithms.CovarianceAcceleratedGrid
