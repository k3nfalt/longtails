import LongTails.Algorithms.DistributedNormalizedProtocol
import LongTails.Algorithms.DistributedNormalizedTuning
import LongTails.Algorithms.DistributedBatchedSgd

namespace LongTails.Algorithms.DistributedNormalizedTraining

open DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex

def zeroConfig (p : Params) (T : Time) : DistributedBatchedSgd.Config p.toParams where
  iterations := 1
  batch _ := 1
  width := 1
  slack := T

noncomputable def algorithm (p : Params) (T : Time) :
    Algorithm (LongTails.Setups.DistributedSmoothNonconvex.ComputeQuery p.toParams)
      (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams)
      (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams) (Point p) (p.n + 1) :=
  if hd : 0 < p.d then
    letI : Nonempty (Fin p.d) := ⟨⟨0, hd⟩⟩
    DistributedNormalizedProtocol.algorithm p (DistributedNormalizedTuning.config p) T
  else DistributedBatchedSgd.algorithm p.toParams (zeroConfig p T)

end LongTails.Algorithms.DistributedNormalizedTraining
