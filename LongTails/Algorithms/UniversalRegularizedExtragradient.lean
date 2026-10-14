import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.HolderMonotone

structure UregState (E : Type u) where
  phase : ℕ
  ρ : ℝ
  x : E
  g : E
  s : ℝ

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stageStart (ε : ℝ) (x0 : E) (ρ : ℝ) : UregState E :=
  ⟨0, ρ, x0, 0, ρ / (2 * ε)⟩

noncomputable def uregStep (ε : ℝ) (x0 : E) (σ : UregState E) (r : E) : UregState E :=
  if σ.phase = 0 then
    if ‖r‖ ≤ ε then ⟨2, σ.ρ, σ.x, r, σ.s⟩
    else if ‖r + (ε / (4 * σ.ρ)) • (σ.x - x0)‖ ≤ ε / 2 then stageStart ε x0 (2 * σ.ρ)
    else ⟨1, σ.ρ, σ.x, r + (ε / (4 * σ.ρ)) • (σ.x - x0), σ.s⟩
  else if σ.phase = 1 then
    if ‖r + (ε / (4 * σ.ρ)) • (σ.x - σ.s • σ.g - x0) - σ.g‖ ≤ ‖σ.g‖ / 2 then
      ⟨0, σ.ρ, σ.x - σ.s • (r + (ε / (4 * σ.ρ)) • (σ.x - σ.s • σ.g - x0)), 0, σ.s⟩
    else ⟨1, σ.ρ, σ.x, σ.g, σ.s / 2⟩
  else σ

noncomputable def universalRegularizedExtragradient (ε r0 : ℝ) (x0 : E) : Algorithm E E E where
  State := UregState E
  initial := fun _ => stageStart ε x0 r0
  query :=  fun σ => (0, if σ.phase = 1 then σ.x - σ.s • σ.g else σ.x)
  update := uregStep ε x0
  output := fun σ => σ.x

end OracleTemplate.HolderMonotone
