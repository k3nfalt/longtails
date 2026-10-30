import LongTails.Algorithms.FractalChebyshevSteps
import LongTails.Setups.HessianLipschitzGradientStationarity

namespace OracleTemplate.RestartedScheduleGD

open OracleTemplate.FractalChebyshev

noncomputable def depth (L ρ ε : ℝ) : ℕ := Nat.log 2 ⌊L ^ 2 / (2 ^ 22 * ρ * ε)⌋₊ / 9

noncomputable def chebyshevSteps (L ρ ε : ℝ) : List ℝ :=
  if 2 ≤ depth L ρ ε then schedule L (muOf L (depth L ρ ε)) (depth L ρ ε) else []

noncomputable def chebyshevThreshold (L ρ ε : ℝ) : ℝ :=
  if 2 ≤ depth L ρ ε then 2 ^ depth L ρ ε * ε else 0

noncomputable def chebyshevRadius (L ρ ε : ℝ) : ℝ :=
  8 * (chebyshevSteps L ρ ε).sum * chebyshevThreshold L ρ ε

noncomputable def chebyshevGd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L ρ ε : ℝ) (x0 : E) : OracleTemplate.Algorithm E E E :=
  algorithm L ε (chebyshevThreshold L ρ ε) (chebyshevRadius L ρ ε) (chebyshevSteps L ρ ε) x0

end OracleTemplate.RestartedScheduleGD
