import LongTails.Setups.MirrorGeneralizedSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.MirrorGeneralizedAcceleration

open OracleTemplate LongTails.Setups.MirrorGeneralizedSmooth

structure Core (p : Public) where
  A : ℝ
  x : p.E
  z : p.E

noncomputable def radius (p : Public) : ℝ := 2 * Real.sqrt p.D

noncomputable def weight (p : Public) (A M : ℝ) : ℝ :=
  min (Real.sqrt (A / (64 * M))) (A / (64 * (1 + p.L1 * radius p)))

noncomputable def mix (p : Public) (s : Core p) (a : ℝ) (z : p.E) : p.E :=
  (s.A / (s.A + a)) • s.x + (a / (s.A + a)) • z

noncomputable def step (p : Public) (g : p.E → p.E →L[ℝ] ℝ)
    (prox : p.E → (p.E →L[ℝ] ℝ) → p.E) (s : Core p) : Core p :=
  let a := weight p s.A (p.L0 + p.L1 * ‖g s.x‖)
  let y := mix p s a s.z
  let w := prox s.z (a • g y)
  ⟨s.A + a, mix p s a w, w⟩

noncomputable def run (p : Public) (g : p.E → p.E →L[ℝ] ℝ)
    (prox : p.E → (p.E →L[ℝ] ℝ) → p.E) : ℕ → Core p
  | 0 => ⟨p.D / p.Δ, p.x0, p.x0⟩
  | k + 1 => step p g prox (run p g prox k)

inductive State (p : Public) where
  | pilot (s : Core p)
  | gradient (s : Core p) (a : ℝ) (y : p.E)
  | proximal (s : Core p) (a : ℝ) (g : p.E →L[ℝ] ℝ)

def State.core {p : Public} : State p → Core p
  | .pilot s => s
  | .gradient s _ _ => s
  | .proximal s _ _ => s

def query {p : Public} : State p → Fin 1 × Query p
  | .pilot s => (0, .gradient s.x)
  | .gradient _ _ y => (0, .gradient y)
  | .proximal s a g => (0, .prox s.z (a • g))

noncomputable def update {p : Public} : State p → Reply p → State p
  | .pilot s, .gradient g =>
      let a := weight p s.A (p.L0 + p.L1 * ‖g‖)
      .gradient s a (mix p s a s.z)
  | .gradient s a _, .gradient g => .proximal s a g
  | .proximal s a _, .prox z => .pilot ⟨s.A + a, mix p s a z, z⟩
  | s, _ => s

def output {p : Public} (s : State p) : p.E := s.core.x

noncomputable def algorithm (p : Public) : Algorithm (Query p) (Reply p) p.E where
  State := State p
  initial _ := .pilot ⟨p.D / p.Δ, p.x0, p.x0⟩
  query := query
  update := update
  output := output

end LongTails.Algorithms.MirrorGeneralizedAcceleration
