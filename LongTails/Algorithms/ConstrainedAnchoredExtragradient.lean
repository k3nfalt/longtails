import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.ConstrainedMonotone

structure AnchoredState (E : Type u) where
  stage : ℕ
  x : E
  ξ : E
  g : E
  w : E
  S : ℝ

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def mval (a x g ξ : E) (S : ℝ) : ℝ :=
  ‖g‖ + ‖g + ξ‖ + ‖x - a‖ / S

noncomputable def stepSize (L0 L1 : ℝ) (a x g ξ : E) (S : ℝ) : ℝ :=
  if S = 0 then 1 / (4 * (L0 + L1 * mval a x g ξ S))
  else min (S / 3) (1 / (4 * (L0 + L1 * mval a x g ξ S)))

noncomputable def anchorPoint (a x : E) (S γ : ℝ) : E :=
  x + (γ / (S + γ)) • (a - x)

noncomputable def halfPoint (a x g ξ : E) (S γ : ℝ) : E :=
  anchorPoint a x S γ - (S / (S + γ) * γ) • (g + ξ)

noncomputable def targetPoint (a x h : E) (S γ : ℝ) : E :=
  anchorPoint a x S γ - γ • h

noncomputable def constrainedAnchored (L0 L1 : ℝ) (x0 : E) : Algorithm E E E 2 where
  State := AnchoredState E
  initial := fun _ => ⟨0, x0, 0, 0, 0, 0⟩
  query := fun s =>
    if s.stage = 0 then (0, s.x)
    else if s.stage = 1 then
      (0, halfPoint x0 s.x s.g s.ξ s.S (stepSize L0 L1 x0 s.x s.g s.ξ s.S))
    else (1, s.w)
  update := fun s r =>
    if s.stage = 0 then ⟨1, s.x, s.ξ, r, s.w, s.S⟩
    else if s.stage = 1 then
      ⟨2, s.x, s.ξ, s.g, targetPoint x0 s.x r s.S (stepSize L0 L1 x0 s.x s.g s.ξ s.S), s.S⟩
    else
      ⟨0, r, (stepSize L0 L1 x0 s.x s.g s.ξ s.S)⁻¹ • (s.w - r), s.g, s.w,
        s.S + stepSize L0 L1 x0 s.x s.g s.ξ s.S⟩
  output := fun s => s.x

end OracleTemplate.ConstrainedMonotone
