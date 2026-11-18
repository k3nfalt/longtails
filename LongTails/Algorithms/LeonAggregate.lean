import LongTails.Algorithms.DashaModular
import LongTails.Algorithms.LeonTuning

namespace LongTails.Algorithms.LeonAggregate

open LongTails.Algorithms.DashaQuantization

noncomputable def localCodes {d : ℕ} (spacing : ℝ) (anchor sample : Vector d) : Fin d → ℤ :=
  indices d false spacing (sample - anchor) (fun _ => 0)

noncomputable def displacement {d : ℕ} (n : ℕ) (spacing : ℝ) (codes : Fin d → ℤ) : Vector d :=
  reconstruct (spacing / n) codes

noncomputable def decode {d : ℕ} (n width : ℕ) (spacing radius : ℝ)
    (anchor : Vector d) (received : Fin d → ℤ) : Vector d :=
  let v := displacement n spacing (fun j => DashaModular.restore width (received j))
  if ‖v‖ ≤ radius then anchor + v else anchor

end LongTails.Algorithms.LeonAggregate

namespace LongTails.Algorithms.LeonExchange

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LeonTuning

def part (p : Params) (i : Fin p.n) (codes : Fin p.d → ℤ) (k : Fin (blockSize p)) : ℤ :=
  if h : k.val * p.n + i.val < p.d then codes ⟨_, h⟩ else 0

noncomputable def scatter (p : Params) (l : ℕ) (i : Fin p.n) (codes : Fin p.d → ℤ) :
    List Bool :=
  DashaModular.encode (blockSize p) (width p l) (part p i codes)

noncomputable def gather (p : Params) (l : ℕ) (messages : Fin p.n → List Bool) : List Bool :=
  DashaModular.encode (blockSize p) (width p l) (fun k =>
    ∑ i, DashaModular.decode (blockSize p) (width p l) (messages i) k)

noncomputable def unpack (p : Params) (l : ℕ) (messages : Fin p.n → List Bool)
    (j : Fin p.d) : ℤ :=
  let owner : Fin p.n := ⟨j.val % p.n, Nat.mod_lt _ p.n.pos⟩
  if h : j.val / p.n < blockSize p then
    DashaModular.decode (blockSize p) (width p l) (messages owner) ⟨_, h⟩
  else 0

end LongTails.Algorithms.LeonExchange
