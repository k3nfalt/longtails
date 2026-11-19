import LongTails.Algorithms.Batched
import LongTails.Algorithms.AbcSgd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Real.Sign

namespace LongTails.Algorithms.MinibatchSignSgd

open OracleTemplate

noncomputable def signVec {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => Real.sign (v i))

noncomputable def batchMean {d B : ℕ} (r : Fin B → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (1 / (B : ℝ)) • ∑ b, r b

noncomputable def minibatchSignSgd {d : ℕ} (η : ℝ) (K B : ℕ) (hB : 0 < B)
    (x0 : EuclideanSpace ℝ (Fin d)) :
    Algorithm (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  batched hB (LongTails.Algorithms.AbcSgd.sampledSgd η K x0) (fun s _ => s.2.2.1)
    (fun _ r => signVec (batchMean r)) 0

end LongTails.Algorithms.MinibatchSignSgd
