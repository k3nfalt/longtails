import LongTails.Algorithms.GraceBatch
import LongTails.Algorithms.GraceRouting

namespace LongTails.Algorithms.GraceSgd

open MeasureTheory
open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open GraceBatch GracePacket GraceRouting
open DistributedQuantization (Grid quantize reconstruct)
open DistributedBatchedSgd (Config radius spacing)
open LeonProtocol (Program)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}

noncomputable def grid (p : Params) (cfg : Config (statistical p)) (x v : Point p) :
    Grid p.d cfg.width :=
  quantize p.d cfg.width (spacing (statistical p) cfg x)
    (OracleTemplate.clip (radius (statistical p) x) v)

def indices {d w : ℕ} (t : ℕ) (z : Grid d w) (x : ℕ) : ℕ :=
  let F := limbCount w t
  if h : x / F < d then (limb t (z ⟨x / F, h⟩).val (x % F)).val else 0

def assembled {d : ℕ} (t w : ℕ) (v : Values) (j : Fin d) : ℕ :=
  let F := limbCount w t
  assemble t F (fun l => v (j.val * F + l))

noncomputable def advance (p : Params) (cfg : Config (statistical p)) (t : ℕ)
    (x : Point p) (v : Values) : Point p :=
  let code : Grid p.d cfg.width := fun j => Fin.ofNat _ (assembled t cfg.width v j)
  x - (1 / (2 * p.L)) • reconstruct (spacing (statistical p) cfg x) code

noncomputable def round (A : Routes p S r) (i : Fin p.n) (x sampleMean : Point p)
    (next : Point p → Program p.base) : Program p.base :=
  let cfg := tuning p S
  let t := limbWidth (B p)
  let q := wordWidth t (B p)
  let D := p.d * limbCount cfg.width t
  let ks := List.range (A.slots D)
  let z := grid p cfg x sampleMean
  A.frames D q .reduce i (fun totals =>
    let values := if i = r then
        let v := meanFromIndices cfg.width (B p) (spacing (statistical p) cfg x)
          (assembled t cfg.width totals)
        indices t (grid p cfg x v)
      else fun _ => 0
    A.frames D q .broadcast i
      (fun data => next (if i ∈ S then advance p cfg t x data else x)) ks values)
    ks (fun j => cfg.batch i * indices t z j)

noncomputable def program (A : Routes p S r) (i : Fin p.n) : ℕ → Point p → Program p.base
  | 0, x => .finish x
  | k + 1, x =>
    let next := fun v => round A i x v (program A i k)
    if h : 0 < batches p S i then
      .sample (x, ⟨batches p S i, h⟩) (fun values => next (LeonTrajectory.mean p.base values))
    else .send i [] (next 0)

noncomputable def algorithm (A : Routes p S r) (deadline : Time) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) p.n where
  clock _ := 0
  timer t := if t = 0 then 0 else deadline + 1
  Seed := Fin (tuning p S).iterations
  law := ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  State := LeonProtocol.State p.base
  root := r
  initial i k := ⟨program A i k.val p.x₀, fun _ => [], false⟩
  update _ s _ ev := LeonProtocol.update p.base s ev
  query _ s _ := LeonProtocol.query p.base s
  output s := match s.program with | .finish x => x | _ => p.x₀

end LongTails.Algorithms.GraceSgd
