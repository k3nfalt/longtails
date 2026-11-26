import LongTails.Algorithms.WeakMintyHybrid

namespace OracleTemplate.FullRangeWeakMintyFirstOrder

open WeakMintyHybrid (margin hybrid)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def advance (L ρ ε : ℝ) (s : E × E) (v : E) : E × E :=
  if ‖v‖ ≤ ε then s else
    let g := L⁻¹ • v
    (s.1 - g + (1 - margin L ρ / 4) • s.2, g)

noncomputable def valueOnly (L ρ ε : ℝ) (x0 : E) :
    Algorithm (E ⊕ E) (E × (E →L[ℝ] E)) E where
  State := E × E
  initial := fun _ => (x0, 0)
  query := fun s => (0, .inl s.1)
  update := fun s reply => advance L ρ ε s reply.1
  output := Prod.fst

def useValues (L M ρ ε : ℝ) : Prop :=
  let δ := margin L ρ
  8 * L ^ 2 / (δ ^ 2 * ε ^ 2) ≤ 1048576 * Real.log (2 / δ) / δ ^ 5 * M / ε

noncomputable def select [FiniteDimensional ℝ E] (L M ρ ε : ℝ) (x0 : E) :
    Algorithm (E ⊕ E) (E × (E →L[ℝ] E)) E := by
  classical
  exact if useValues L M ρ ε then valueOnly L ρ ε x0 else hybrid L M ρ ε x0

end OracleTemplate.FullRangeWeakMintyFirstOrder
