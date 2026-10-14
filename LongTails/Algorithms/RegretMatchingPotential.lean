import LongTails.Template
import Mathlib.Algebra.BigOperators.Fin

namespace OracleTemplate.RegretMatchingPotential

noncomputable def total {m : ℕ} (Q : Fin m → ℝ) : ℝ := ∑ a, Q a

noncomputable def strategy {m : ℕ} (Q : Fin m → ℝ) : Fin m → ℝ :=
  if 0 < total Q then fun a => Q a / total Q else fun _ => 1 / (m : ℝ)

noncomputable def value {m : ℕ} (x u : Fin m → ℝ) : ℝ := ∑ a, x a * u a

noncomputable def regret {m : ℕ} (Q u : Fin m → ℝ) : Fin m → ℝ :=
  fun a => u a - value (strategy Q) u

noncomputable def step {m : ℕ} (Q u : Fin m → ℝ) : Fin m → ℝ :=
  fun a => max (Q a + regret Q u a) 0

open Classical in
noncomputable def rmPlusPotential (m n : ℕ) (ε : ℝ) :
    Algorithm ((Fin m → ℝ) × (Fin n → ℝ)) ((Fin m → ℝ) × (Fin n → ℝ))
      ((Fin m → ℝ) × (Fin n → ℝ)) where
  State := (Fin m → ℝ) × (Fin n → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))
  initial _ := (0, 0, (strategy 0, strategy 0))
  query s := (0, (strategy s.1, strategy s.2.1))
  update s r := (step s.1 r.1, step s.2.1 r.2,
    if (∀ a, regret s.1 r.1 a ≤ ε) ∧ ∀ b, regret s.2.1 r.2 b ≤ ε then
      (strategy s.1, strategy s.2.1) else s.2.2)
  output s := s.2.2

end OracleTemplate.RegretMatchingPotential
