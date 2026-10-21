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

namespace LongTails.Setups.RegretMatchingPotential

open OracleTemplate OracleTemplate.RegretMatchingPotential

structure Public where
  m : ℕ
  n : ℕ
  ε : ℝ

structure Params extends Public where
  B : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := (Fin p.m → Fin p.n → ℝ) × (Fin p.m → Fin p.n → ℝ)
  Query p := (Fin p.m → ℝ) × (Fin p.n → ℝ)
  Reply p := (Fin p.m → ℝ) × (Fin p.n → ℝ)
  Output p := (Fin p.m → ℝ) × (Fin p.n → ℝ)
  publicInput := Params.toPublic
  valid q := 0 < q.m ∧ 0 < q.n ∧ 0 < q.B ∧ 0 < q.ε
  admissible q G oracle :=
    (∃ P : Fin q.m → Fin q.n → ℝ, (∀ i j, 0 ≤ P i j ∧ P i j ≤ q.B) ∧
      (∀ i i' j, G.1 i j - G.1 i' j = P i j - P i' j) ∧
      ∀ i j j', G.2 i j - G.2 i j' = P i j - P i j') ∧
    ∀ k x y seed, oracle.answer k (0, (x, y)) seed =
      (fun i => ∑ j, G.1 i j * y j, fun j => ∑ i, G.2 i j * x i)
  successful q G output _ :=
    ∀ ω, let x := (output ω).1
      let y := (output ω).2
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1 ∧
      (∀ i, ∑ j, G.1 i j * y j ≤ ∑ i', ∑ j, x i' * G.1 i' j * y j + q.ε) ∧
      ∀ j, ∑ i, x i * G.2 i j ≤ ∑ i, ∑ j', x i * G.2 i j' * y j' + q.ε
  allowedAlgorithm p algorithm := algorithm = rmPlusPotential p.m p.n p.ε

end LongTails.Setups.RegretMatchingPotential
