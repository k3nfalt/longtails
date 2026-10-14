import LongTails.Algorithms.RegretMatchingPotential

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
