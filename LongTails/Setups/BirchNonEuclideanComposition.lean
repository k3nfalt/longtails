import LongTails.Setups.BirchNonEuclidean

namespace LongTails.Setups.BirchNonEuclideanComposition

open OracleTemplate
open OracleTemplate.Rennala (Point Instance)

inductive PacketExpr where
  | atom (worker : ℕ)
  | sequence (left right : PacketExpr)
  | fork (owner : ℕ) (left right : PacketExpr)
  | overlap (owner : ℕ) (left right afterBoth afterRight : PacketExpr)

def PacketExpr.calls : PacketExpr → ℕ
  | .atom _ => 1
  | .sequence left right | .fork _ left right => left.calls + right.calls
  | .overlap _ left right afterBoth afterRight =>
      left.calls + right.calls + afterBoth.calls + afterRight.calls

def PacketExpr.Valid (workers : ℕ) : PacketExpr → Prop
  | .atom worker => worker < workers
  | .sequence left right => left.Valid workers ∧ right.Valid workers
  | .fork owner left right => owner < workers ∧ left.Valid workers ∧ right.Valid workers
  | .overlap owner left right afterBoth afterRight => owner < workers ∧
      left.Valid workers ∧ right.Valid workers ∧ afterBoth.Valid workers ∧ afterRight.Valid workers

structure Params where
  d : ℕ
  N : Seminorm ℝ (Point d)
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  workers : ℕ
  κ : ℝ
  slots : ℕ
  credits : ℕ
  word : ℕ → ℕ → ℕ → Fin slots
  recipe : ℕ → ℕ → Fin slots → ℕ → ℕ → PacketExpr

def native (p : Params) : BirchNonEuclidean.Params where
  d := p.d
  N := p.N
  L := p.L
  σ := p.σ
  ε := p.ε
  Δ := p.Δ
  x0 := p.x0
  workers := p.workers
  κ := p.κ
  protocol := ⟨fun _ _ => ⟨[], 0, 0, fun _ => 0⟩⟩
  profile := ⟨1, 0, 0, 0, 0⟩
  callCount := fun _ _ => 0

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput p := p
  valid p := (∀ x, p.N x = 0 → x = 0) ∧ Continuous p.N ∧
    0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 < p.workers ∧
    BirchNonEuclidean.DualRegular p.N p.κ ∧ 0 < p.slots ∧ 0 < p.credits ∧
      ∀ K B slot source serial, (p.recipe K B slot source serial).Valid p.workers ∧
        (p.recipe K B slot source serial).calls = p.credits
  admissible p I O := BirchNonEuclidean.spec.admissible (native p) I O
  successful p I output P := BirchNonEuclidean.spec.successful (native p) I output P

end LongTails.Setups.BirchNonEuclideanComposition
