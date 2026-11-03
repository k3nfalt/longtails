import LongTails.Template
import Mathlib.Data.Matrix.Mul

namespace LongTails.Setups.BoundedMixedIntegerLinear

open OracleTemplate Matrix

structure Params where
  p : ℕ
  q : ℕ
  m : ℕ
  A : Matrix (Fin m) (Fin p) ℝ
  G : Matrix (Fin m) (Fin q) ℝ
  b : Fin m → ℝ
  c : Fin p → ℝ
  d : Fin q → ℝ
  lo : Fin p → ℤ
  hi : Fin p → ℤ

abbrev Box (P : Params) := (Fin P.p → ℤ) × (Fin P.p → ℤ)

abbrev Point (P : Params) := (Fin P.p → ℝ) × (Fin P.q → ℝ)

abbrev Solution (P : Params) := (Fin P.p → ℤ) × (Fin P.q → ℝ)

def objective (P : Params) (x : Point P) : ℝ := P.c ⬝ᵥ x.1 + P.d ⬝ᵥ x.2

def RowFeasible (P : Params) (x : Point P) : Prop := ∀ i, (P.A *ᵥ x.1 + P.G *ᵥ x.2) i ≤ P.b i

def InBox (P : Params) (β : Box P) (z : Fin P.p → ℝ) : Prop :=
  ∀ j, (β.1 j : ℝ) ≤ z j ∧ z j ≤ β.2 j

def RelaxationFeasible (P : Params) (β : Box P) (x : Point P) : Prop :=
  RowFeasible P x ∧ InBox P (P.lo, P.hi) x.1 ∧ InBox P β x.1

def toPoint (P : Params) (x : Solution P) : Point P := (fun j => (x.1 j : ℝ), x.2)

def MixedFeasible (P : Params) (x : Solution P) : Prop :=
  RowFeasible P (toPoint P x) ∧ ∀ j, P.lo j ≤ x.1 j ∧ x.1 j ≤ P.hi j

def SolvesRelaxation (P : Params) (β : Box P) : Option (Point P) → Prop
  | none => ∀ x, ¬ RelaxationFeasible P β x
  | some x => RelaxationFeasible P β x ∧
      ∀ x', RelaxationFeasible P β x' → objective P x ≤ objective P x'

def IsRelaxationOracle (P : Params) (O : Oracle (Box P) (Option (Point P))) : Prop :=
  ∀ history (query : Fin 1 × Box P) seed, SolvesRelaxation P query.2 (O.answer history query seed)

def SolvesMixed (P : Params) : Option (Solution P) → Prop
  | none => ∀ x, ¬ MixedFeasible P x
  | some x => MixedFeasible P x ∧
      ∀ x', MixedFeasible P x' → objective P (toPoint P x) ≤ objective P (toPoint P x')

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance _ := Unit
  Query P := Box P
  Reply P := Option (Point P)
  Output P := Option (Solution P)
  publicInput P := P
  valid P := ∃ L, ∀ x, RelaxationFeasible P (P.lo, P.hi) x → L ≤ objective P x
  admissible P _ O := IsRelaxationOracle P O
  successful P _ output _ := ∀ ω, SolvesMixed P (output ω)

end LongTails.Setups.BoundedMixedIntegerLinear
