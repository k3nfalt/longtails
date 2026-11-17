import LongTails.Algorithms.DashaDistributedParameters

namespace LongTails.Algorithms.DashaDistributedNormalization

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex

noncomputable def normalize (p : Params) : Params :=
  { p with
    L := min p.L p.Lhat
    Lhat := if p.n = 1 then min p.L p.Lhat else p.Lhat
    G := if p.n = 1 then min p.G (Real.sqrt (2 * min p.L p.Lhat * p.Δ)) else p.G }

end LongTails.Algorithms.DashaDistributedNormalization
