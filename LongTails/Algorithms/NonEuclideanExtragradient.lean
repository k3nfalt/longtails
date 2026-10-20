import LongTails.Setups.NonEuclideanWeakMinty
import LongTails.Algorithms.PowerDualAveraging

namespace LongTails.Algorithms.NonEuclideanExtragradient

open OracleTemplate LongTails.Setups.NonEuclideanWeakMinty

noncomputable def mirror (d : Public) (x : d.E) (g : d.E →L[ℝ] ℝ) : d.E := by
  classical
  let f := fun z => (d.μ / (10 * d.L)) * g z + d.bregman z x
  exact if hm : ∃ z, ∀ w, f z ≤ f w then Classical.choose hm else x

noncomputable def predictor (d : Public) (x : d.E) (g : d.E →L[ℝ] ℝ) : d.E :=
  x - (1 / (2 * d.L)) • PowerDualAveraging.direction g

structure State (d : Public) where
  x : d.E
  y : d.E
  best : d.E
  bestNorm : ℝ
  seen : Bool
  correction : Bool

noncomputable def step (d : Public) (s : State d) (g : d.E →L[ℝ] ℝ) : State d := by
  classical
  exact if s.correction then
    { s with x := mirror d s.x g, correction := false }
  else
    { s with
      y := predictor d s.x g
      best := if s.seen = false ∨ ‖g‖ ≤ s.bestNorm then s.x else s.best
      bestNorm := if s.seen = false ∨ ‖g‖ ≤ s.bestNorm then ‖g‖ else s.bestNorm
      seen := true, correction := true }

def output (d : Public) (s : State d) : d.E := s.best

noncomputable def algorithm (d : Public) : Algorithm d.E (d.E →L[ℝ] ℝ) d.E where
  State := State d
  initial := fun _ => ⟨d.x0, d.x0, d.x0, 0, false, false⟩
  query := fun s => (0, if s.correction then s.y else s.x)
  update := step d
  output := output d

end LongTails.Algorithms.NonEuclideanExtragradient
