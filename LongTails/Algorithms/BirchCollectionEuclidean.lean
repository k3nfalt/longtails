import LongTails.Algorithms.BirchCollections

namespace LongTails.Algorithms.BirchCollectionEuclidean

open OracleTemplate.BirchSgd (Tree)
open LongTails.Setups.BirchNonEuclidean (Instruction Program)

def vertexReg (j : ℕ) : ℕ := 3 * j

def replyReg (j : ℕ) : ℕ := 3 * j + 1

def directionReg (j : ℕ) : ℕ := 3 * j + 2

def edgeCode (T : Tree) (γ : ℝ) (j : ℕ) : List Instruction :=
  [.query 0 (vertexReg (T.point j)),
    .mix 0 [(-1, replyReg j)],
    .move 0 (vertexReg (T.base j)) (directionReg (T.grad j)) γ]

def trace (T : Tree) (γ : ℝ) : ℕ → List Instruction
  | 0 => []
  | j + 1 => trace T γ j ++ edgeCode T γ j

def program (T : Tree) (γ : ℝ) (m : ℕ → ℕ) (N lastOutput : ℕ) : Program where
  instructions := trace T γ N
  outputWorker := 0
  outputCount := lastOutput
  outputPoint := fun j => vertexReg (m j.val)

noncomputable def native (p : LongTails.Setups.BirchSgd.Params) :
    LongTails.Setups.BirchNonEuclidean.Params where
  d := p.d
  N := normSeminorm ℝ (OracleTemplate.Rennala.Point p.d)
  L := p.L
  σ := p.σ
  ε := p.ε
  Δ := p.Δ
  x0 := p.x0
  workers := 1
  κ := 1
  protocol := ⟨fun _ _ => ⟨[], 0, 0, fun _ => 0⟩⟩
  profile := ⟨1, 0, 0, 0, 0⟩
  callCount := fun _ _ => 0

noncomputable def prefixProgram (p : LongTails.Setups.BirchSgd.Params) (K : ℕ) : Program :=
  let q := LongTails.Setups.BirchSgd.publicInput p
  program q.tree q.gamma q.branch (q.branch K) K

noncomputable def prefixAlgorithm (p : LongTails.Setups.BirchSgd.Params) (K : ℕ) :=
  LongTails.Setups.BirchNonEuclidean.programAlgorithm (native p) (prefixProgram p K) (fun _ => 0)

noncomputable def algorithm (p : LongTails.Setups.BirchSgd.Params) :=
  prefixAlgorithm p (LongTails.Setups.BirchSgd.publicInput p).K

end LongTails.Algorithms.BirchCollectionEuclidean
