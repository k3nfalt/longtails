import LongTails.Setups.PowerGeometryRelativeErrorConvex

namespace LongTails.Algorithms.PowerDualAveraging

open OracleTemplate LongTails.Setups.PowerGeometryRelativeErrorConvex

noncomputable def direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) : E := by
  classical
  exact if h : ∃ v, ‖v‖ ≤ ‖g‖ ∧ g v = ‖g‖ ^ 2 then Classical.choose h else 0

noncomputable def mirror (d : Public) (β : ℝ) (h : d.E →L[ℝ] ℝ) : d.E :=
  d.x0 - (1 / β) • direction h

def weight (n : ℕ) : ℝ := (n : ℝ) ^ 2

noncomputable def totalWeight (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (2 * n + 1) / 6

noncomputable def geometryConstant (d : Public) : ℝ :=
  128 * max 1 (32 ^ ((d.p - 2) / 2) / d.c)

noncomputable def regularization (d : Public) (n : ℕ) : ℝ :=
  d.L * (geometryConstant d * ((n : ℝ) + 1) ^ (2 - 2 / d.p) +
    256 * d.α ^ 2 * ((n : ℝ) + 1) ^ 2)

structure State (d : Public) where
  n : ℕ
  x : d.E
  z : d.E
  h : d.E →L[ℝ] ℝ

noncomputable def queryPoint (d : Public) (s : State d) : d.E :=
  (totalWeight s.n / totalWeight (s.n + 1)) • s.x +
    (weight (s.n + 1) / totalWeight (s.n + 1)) • s.z

noncomputable def step (d : Public) (s : State d) (g : d.E →L[ℝ] ℝ) : State d :=
  let h := s.h + weight (s.n + 1) • g
  ⟨s.n + 1, queryPoint d s - (1 / (2 * d.L)) • direction g,
    mirror d (regularization d (s.n + 1)) h, h⟩

def output (d : Public) (s : State d) : d.E := s.x

noncomputable def algorithm (d : Public) : Algorithm d.E (d.E →L[ℝ] ℝ) d.E where
  State := State d
  initial := fun _ => ⟨0, d.x0, d.x0, 0⟩
  query := fun s => (0, queryPoint d s)
  update := step d
  output := output d

end LongTails.Algorithms.PowerDualAveraging
