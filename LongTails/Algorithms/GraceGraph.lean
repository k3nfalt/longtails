import LongTails.Algorithms.GraceBatch

namespace LongTails.Algorithms.GraceGraph

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex

abbrev Link (p : Params) := {e : Fin p.n × Fin p.n // e.1 < e.2 ∧ p.G.Adj e.1 e.2}

noncomputable instance (p : Params) : Fintype (Link p) := Fintype.ofFinite _

def capacity (p : Params) (e : Link p) := p.b e.val.1 e.val.2

noncomputable def cut (p : Params) (C : Finset (Fin p.n)) : Time :=
  ∑ e : Link p, if (e.val.1 ∈ C ↔ e.val.2 ∈ C) then 0 else capacity p e

def cuts (p : Params) (S : Finset (Fin p.n)) :=
  Finset.univ.filter fun C : Finset (Fin p.n) => (S ∩ C).Nonempty ∧ (S \ C).Nonempty

noncomputable def α (p : Params) (S : Finset (Fin p.n)) : Time :=
  let values := (cuts p S).image (cut p)
  if h : values.Nonempty then values.min' h else 0

end LongTails.Algorithms.GraceGraph
