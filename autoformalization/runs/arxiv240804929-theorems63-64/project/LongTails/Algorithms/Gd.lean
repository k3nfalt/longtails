import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.Gradient

noncomputable def gd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ℝ × E → Algorithm E E E 1
  | (L, x0) => {
      State := E
      initial _ := x0
      query x := (0, x)
      update x reply := x - (1 / L) • reply
      output x := x }

end OracleTemplate.Gradient
