import LongTails.Algorithms.SilverSchedule
import LongTails.Setups.SmoothConvexQuadraticGrowth

namespace LongTails.Algorithms.UniversalSilver

open LongTails.Algorithms.SilverSchedule LongTails.Setups.SmoothConvexQuadraticGrowth

def ruler : ℕ → List ℕ
  | 0 => [1]
  | a + 1 => ruler a ++ (ruler a).dropLast ++ [a + 2]

noncomputable def blocks (a : ℕ) : List ℝ := (ruler a).flatMap steps

noncomputable def stepsize (t : ℕ) : ℝ := (blocks t).getD t 1

noncomputable def method (p : Public) :=
  gradientMethod (fun t => stepsize t / p.L) p.x0

end LongTails.Algorithms.UniversalSilver
