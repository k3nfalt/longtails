import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.SilverSchedule

noncomputable def ratio : ℝ := 1 + Real.sqrt 2

noncomputable def steps : ℕ → List ℝ
  | 0 => []
  | k + 1 => steps k ++ [1 + ratio ^ k / ratio] ++ steps k

noncomputable def run {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E → E) : List ℝ → E → E
  | [], x => x
  | h :: hs, x => run g hs (x - h • g x)

end LongTails.Algorithms.SilverSchedule
