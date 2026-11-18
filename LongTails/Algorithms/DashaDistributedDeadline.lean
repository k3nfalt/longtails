import LongTails.Algorithms.DashaDistributedSelection

namespace LongTails.Algorithms.DashaDistributedDeadline

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open DashaDistributed DashaScaling

noncomputable def atDeadline (p : Params) (cfg : Config p) (deadline : Time) : Config p :=
  { cfg with slack := cfg.slack + (deadline - timeBudget p cfg) }

noncomputable def tunedAtDeadline (p : Params) (deadline : Time) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) := by
  classical
  exact if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then idle p
    else algorithm (DashaDistributedNormalization.normalize p)
      (atDeadline (DashaDistributedNormalization.normalize p)
        (DashaDistributedSelection.chosenConfig (DashaDistributedNormalization.normalize p)) deadline)

end LongTails.Algorithms.DashaDistributedDeadline
