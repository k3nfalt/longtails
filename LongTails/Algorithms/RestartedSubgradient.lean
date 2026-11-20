import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate

structure RestartedSubgradientState (E : Type) where
  phase : ℕ
  step : ℕ
  x : E
  sum : E

noncomputable def restartedSubgradientStep (L D : ℝ) (T k : ℕ) : ℝ :=
  D / 2 ^ k / (L * Real.sqrt T)

noncomputable def restartedSubgradient {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L D : ℝ) (T : ℕ) (x0 : E) : Algorithm E (ℝ × E) E where
  State := RestartedSubgradientState E
  initial _ := ⟨0, 0, x0, 0⟩
  query s := (0, s.x)
  update s reply :=
    if s.step + 1 = T then
      ⟨s.phase + 1, 0, ((T : ℝ)⁻¹) • (s.sum + s.x), 0⟩
    else
      ⟨s.phase, s.step + 1, s.x - restartedSubgradientStep L D T s.phase • reply.2, s.sum + s.x⟩
  output s := s.x

end OracleTemplate
