import LongTails.Algorithms.AnchoredExtragradient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

namespace OracleTemplate.WarmAnchoredMonotone

open GeneralizedMonotone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def warmScale (L1 R : ℝ) : ℝ := (L1 * R) ^ ((1 : ℝ) / 3)

noncomputable def warmLimit (L1 R : ℝ) : ℕ :=
  if 1 ≤ L1 * R then ⌈4 * (L1 * R) ^ ((4 : ℝ) / 3)⌉₊ + 1 else 0

noncomputable def warmThreshold (L0 L1 R : ℝ) : ℝ :=
  8 * L0 * R * Real.exp (2 * warmScale L1 R)

noncomputable def warmNext (L0 L1 R : ℝ) (x g : E) : E :=
  if warmThreshold L0 L1 R < ‖g‖ then x - (warmScale L1 R / (2 * L1 * ‖g‖)) • g else x

structure State (E : Type u) where
  left : ℕ
  anchor : E
  inner : AnchoredState E

noncomputable def output (s : State E) : E := s.inner.x

noncomputable def algorithm (L0 L1 R : ℝ) (x0 : E) : Algorithm E E E where
  State := State E
  initial := fun _ => ⟨warmLimit L1 R, x0, ⟨false, x0, 0, 0⟩⟩
  query := fun s =>
    if s.left = 0 then (anchoredExtragradient L0 L1 s.anchor).query s.inner
    else (0, s.inner.x)
  update := fun s r =>
    if s.left = 0 then
      ⟨0, s.anchor, (anchoredExtragradient L0 L1 s.anchor).update s.inner r⟩
    else if s.inner.half then
      let x := warmNext L0 L1 R s.inner.x s.inner.g
      ⟨s.left - 1, x, ⟨false, x, 0, 0⟩⟩
    else ⟨s.left, s.anchor, ⟨true, s.inner.x, r, 0⟩⟩
  output := output

end OracleTemplate.WarmAnchoredMonotone
