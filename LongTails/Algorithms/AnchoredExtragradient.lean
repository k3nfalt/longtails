import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.GeneralizedMonotone

structure AnchoredState (E : Type u) where
  half : Bool
  x : E
  g : E
  S : ℝ

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepSize (L0 L1 : ℝ) (a x g : E) (S : ℝ) : ℝ :=
  if S = 0 then 1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S)))
  else min (S / 3) (1 / (4 * (L0 + L1 * (‖g‖ + ‖x - a‖ / S))))

noncomputable def anchorPoint (L0 L1 : ℝ) (a x g : E) (S : ℝ) : E :=
  x + (stepSize L0 L1 a x g S / (S + stepSize L0 L1 a x g S)) • (a - x)

noncomputable def halfPoint (L0 L1 : ℝ) (a x g : E) (S : ℝ) : E :=
  anchorPoint L0 L1 a x g S -
    ((S / (S + stepSize L0 L1 a x g S)) * stepSize L0 L1 a x g S) • g

noncomputable def nextPoint (L0 L1 : ℝ) (a x g r : E) (S : ℝ) : E :=
  anchorPoint L0 L1 a x g S - stepSize L0 L1 a x g S • r

noncomputable def anchoredExtragradient (L0 L1 : ℝ) (x0 : E) : Algorithm E E E where
  State := AnchoredState E
  initial := fun _ => ⟨false, x0, 0, 0⟩
  query :=  fun s => (0, if s.half then halfPoint L0 L1 x0 s.x s.g s.S else s.x)
  update := fun s r =>
    if s.half then
      ⟨false, nextPoint L0 L1 x0 s.x s.g r s.S, 0, s.S + stepSize L0 L1 x0 s.x s.g s.S⟩
    else ⟨true, s.x, r, s.S⟩
  output := fun s => s.x

end OracleTemplate.GeneralizedMonotone
