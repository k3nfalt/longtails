import LongTails.Setups.BirchNonEuclidean

namespace LongTails.Setups.BirchWindow

open OracleTemplate
open OracleTemplate.Rennala (Point Instance)

structure Params where
  d : ℕ
  N : Seminorm ℝ (Point d)
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  κ : ℝ

def native (p : Params) : BirchNonEuclidean.Params where
  d := p.d
  N := p.N
  L := p.L
  σ := p.σ
  ε := p.ε
  Δ := p.Δ
  x0 := p.x0
  workers := 1
  κ := p.κ
  protocol := ⟨fun _ _ => ⟨[], 0, 0, fun _ => 0⟩⟩
  profile := ⟨1, 0, 0, 0, 0⟩
  callCount := fun _ _ => 0

noncomputable def batchSize (p : Params) : ℕ :=
  1 + ⌈32 * p.κ * p.σ ^ 2 / p.ε⌉₊

noncomputable def horizon (p : Params) : ℕ :=
  1 + ⌈48 * p.L * batchSize p * p.Δ / p.ε⌉₊

noncomputable def stepSize (p : Params) : ℝ := 1 / (4 * p.L * batchSize p)

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput p := p
  valid p := (∀ x, p.N x = 0 → x = 0) ∧ Continuous p.N ∧
    0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ BirchNonEuclidean.DualRegular p.N p.κ
  admissible p I O := BirchNonEuclidean.spec.admissible (native p) I O
  successful p I output P := BirchNonEuclidean.spec.successful (native p) I output P

end LongTails.Setups.BirchWindow
