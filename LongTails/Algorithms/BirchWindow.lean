import LongTails.Setups.BirchWindow
import LongTails.Algorithms.BirchNonEuclideanFramework

namespace LongTails.Algorithms.BirchWindow

open Finset
open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean (Instruction Params Program)

def source (B j : ℕ) : ℕ := j + 1 - B

noncomputable def iterate (p : Params) (B : ℕ) (η : ℝ) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) : ℕ → Point p.d
  | 0 => p.x0
  | k + 1 =>
    let mean := (1 / (B : ℝ)) • ∑ i : Fin B, response (k + i)
      (iterate p B η lmo response (source B (k + i)))
    iterate p B η lmo response k + η • (dualNorm p.N mean • lmo mean)
termination_by k => k
decreasing_by
  all_goals first | omega | have hi := i.isLt; unfold source; omega

def calls (B K : ℕ) : ℕ := B + K - 1

def pointReg (B k : ℕ) : ℕ := if k = 0 then 0 else B - 1 + 4 * k

def replyReg (B j : ℕ) : ℕ :=
  if j < B - 1 then j + 1 else B - 1 + 4 * (j - (B - 1)) + 1

def warm : ℕ → List Instruction
  | 0 => []
  | n + 1 => warm n ++ [.query 0 0]

noncomputable def block (B : ℕ) (η : ℝ) (k : ℕ) : List Instruction :=
  let n := B - 1 + 4 * k
  [.query 0 (pointReg B k),
    .mix 0 ((List.range B).map (fun i => (1 / (B : ℝ), replyReg B (k + i)))),
    .sharp 0 (n + 2), .move 0 (pointReg B k) (n + 3) η]

noncomputable def code (B : ℕ) (η : ℝ) : ℕ → List Instruction
  | 0 => warm (B - 1)
  | k + 1 => code B η k ++ block B η k

noncomputable def program (B K : ℕ) (η : ℝ) : Program :=
  ⟨code B η K, 0, K - 1, fun i => pointReg B i.val⟩

noncomputable def algorithm (p : LongTails.Setups.BirchWindow.Params) :=
  let q := LongTails.Setups.BirchWindow.native p
  LongTails.Setups.BirchNonEuclidean.programAlgorithm q
    (program (LongTails.Setups.BirchWindow.batchSize p) (LongTails.Setups.BirchWindow.horizon p)
      (LongTails.Setups.BirchWindow.stepSize p))
    (LongTails.Algorithms.BirchNonEuclideanFramework.chosenLMO q)

end LongTails.Algorithms.BirchWindow
