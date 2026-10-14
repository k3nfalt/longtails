import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.SplitBrox

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Query (E : Type*) := E ⊕ (E × ℝ × E)

abbrev Reply (E : Type*) := (ℝ × E) ⊕ E

inductive Phase (E : Type*) where
  | first
  | local (g : E) (cut : ℝ) (doublings : ℕ) (previous : E)

structure State (E : Type*) where
  completed : ℕ
  extra : ℕ
  momentum : E
  primal : E
  phase : Phase E

def weight (n : ℕ) : ℝ := 2 / ((n : ℝ) + 2)

def mix (n : ℕ) (y x : E) : E := (1 - weight n) • y + weight n • x

def radius (b : ℝ) (j : ℕ) : ℝ := 2 ^ j * b

def rank (s : State E) : ℕ :=
  2 * s.completed + s.extra + match s.phase with
    | .first => 0
    | .local _ _ j _ => j + 1

def query (K : ℕ) (b : ℝ) (s : State E) : Query E :=
  if K ≤ s.completed then .inr (s.momentum, 0, 0)
  else match s.phase with
    | .first => .inl (mix s.completed s.primal s.momentum)
    | .local g _ j _ => .inr (s.momentum, radius b j, g)

def update (K : ℕ) (fstar : ℝ) (s : State E) (reply : Reply E) : State E :=
  if K ≤ s.completed then s
  else match s.phase, reply with
    | .first, .inl (value, g) =>
      let z := mix s.completed s.primal s.momentum
      let cut := value + ⟪g, s.momentum - z⟫ - fstar
      if cut ≤ 0 then
        { s with completed := s.completed + 1, primal := z, phase := .first }
      else { s with phase := .local g cut 0 s.momentum }
    | .local g cut j previous, .inr v =>
      if cut ≤ ⟪g, s.momentum - v⟫ then
        { completed := s.completed + 1
          extra := s.extra + j
          momentum := if j = 0 then s.momentum else previous
          primal := mix s.completed s.primal v
          phase := .first }
      else { s with phase := .local g cut (j + 1) v }
    | _, _ => s

def algorithm (K : ℕ) (b fstar : ℝ) (x0 : E) : Algorithm (Query E) (Reply E) E where
  State := State E
  initial _ := ⟨0, 0, x0, x0, .first⟩
  query s := (0, query K b s)
  update := update K fstar
  output s := s.primal

end OracleTemplate.SplitBrox
