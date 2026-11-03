import LongTails.Setups.BoundedMixedIntegerLinear
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs

namespace LongTails.Setups.HiddenMixedIntegerLinear

open OracleTemplate Matrix

structure Public where
  p : ℕ
  q : ℕ
  c : Fin p → ℝ
  d : Fin q → ℝ
  lo : Fin p → ℤ
  hi : Fin p → ℤ

structure Params extends Public where
  m : ℕ
  A : Matrix (Fin m) (Fin p) ℝ
  G : Matrix (Fin m) (Fin q) ℝ
  b : Fin m → ℝ
  lam : Fin m → ℝ

abbrev data (P : Params) : BoundedMixedIntegerLinear.Params :=
  ⟨P.p, P.q, P.m, P.A, P.G, P.b, P.c, P.d, P.lo, P.hi⟩

abbrev Box (Q : Public) := (Fin Q.p → ℤ) × (Fin Q.p → ℤ)

abbrev Point (Q : Public) := (Fin Q.p → ℝ) × (Fin Q.q → ℝ)

abbrev Solution (Q : Public) := (Fin Q.p → ℤ) × (Fin Q.q → ℝ)

def lagrangian (P : Params) (z : Fin P.p → ℝ) : ℝ := (P.c + P.lam ᵥ* P.A) ⬝ᵥ z - P.lam ⬝ᵥ P.b

noncomputable def goodPoints (P : Params) : Finset (Fin P.p → ℤ) :=
  open Classical in
  (Fintype.piFinset fun j => Finset.Icc (P.lo j) (P.hi j)).filter fun z =>
    ∀ x, BoundedMixedIntegerLinear.MixedFeasible (data P) x →
      lagrangian P (fun j => (z j : ℝ)) ≤
        BoundedMixedIntegerLinear.objective (data P) (BoundedMixedIntegerLinear.toPoint (data P) x)

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance _ := Unit
  Query Q := Box Q
  Reply Q := Option (Point Q)
  Output Q := Option (Solution Q)
  publicInput P := P.toPublic
  valid P := ((∀ i, 0 ≤ P.lam i) ∧ P.d + P.lam ᵥ* P.G = 0) ∨
    ∀ x, ¬ BoundedMixedIntegerLinear.RelaxationFeasible (data P) (P.lo, P.hi) x
  admissible P _ O := BoundedMixedIntegerLinear.IsRelaxationOracle (data P) O
  successful P _ output _ := ∀ ω, BoundedMixedIntegerLinear.SolvesMixed (data P) (output ω)

end LongTails.Setups.HiddenMixedIntegerLinear
