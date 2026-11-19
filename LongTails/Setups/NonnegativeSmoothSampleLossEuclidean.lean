import LongTails.Setups.NonnegativeSmoothSampleLoss
import LongTails.TemplateLowerBound
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LongTails.Setups.NonnegativeSmoothSampleLossEuclidean

open OracleTemplate

structure Params where
  L : ℝ
  Δ : ℝ
  ε : ℝ
  extraWidth : ℕ

noncomputable def stages (q : Params) : ℕ := ⌊Real.sqrt (q.L * q.Δ) / (4294967296 * q.ε)⌋₊

def rows (n : ℕ) := (512 * (n+1)) ^ 2

def width (n extra : ℕ) := 2097152 * (2*n^3+1) * n * rows n ^ 2 + extra + 1

abbrev Block (m d : ℕ) := EuclideanSpace ℝ (Fin m × Fin d)

abbrev Space (n m d : ℕ) := PiLp 2 (fun _ : Fin n => Block m d)

instance (n m d : ℕ) : MeasurableSpace (Space n m d) := borel _

instance (n m d : ℕ) : BorelSpace (Space n m d) := ⟨rfl⟩

noncomputable abbrev parameters (q : Params) : NonnegativeSmoothSampleLoss.Params where
  E := Space (stages q) (rows (stages q)) (width (stages q) q.extraWidth)
  Ω := Fin (rows (stages q))
  x0 := 0
  L := q.L
  Δ := q.Δ
  ε := q.ε

noncomputable abbrev spec : Setup where
  Params := Params
  Public := NonnegativeSmoothSampleLoss.Params
  publicInput := parameters
  Instance := NonnegativeSmoothSampleLoss.spec.Instance
  Query := NonnegativeSmoothSampleLoss.spec.Query
  Reply := NonnegativeSmoothSampleLoss.spec.Reply
  Output := NonnegativeSmoothSampleLoss.spec.Output
  valid q := 0 < q.L ∧ 0 < q.Δ ∧ 0 < q.ε ∧ 4294967296 * q.ε ≤ Real.sqrt (q.L * q.Δ)
  admissible q := NonnegativeSmoothSampleLoss.spec.admissible (parameters q)
  successful q := NonnegativeSmoothSampleLoss.spec.successful (parameters q)

end LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
