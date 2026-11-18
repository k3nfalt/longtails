import LongTails.Algorithms.DistributedNormalizedDownlink

namespace LongTails.Algorithms.DistributedNormalizedProtocol

open DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open DistributedNormalizedDownlink

structure State (p : Params) where
  draws : Draws p
  point : Point p
  selected : Point p
  outputIndex : ℕ
  iteration : ℕ := 0
  accumulator : Point p := 0
  samples : ℕ := 0
  pending : Bool := false
  sent : Bool := false
  arrived : Finset (Fin p.n) := ∅
  outbox : Fin p.n → List Bool := fun _ => []
  targets : List (Fin p.n) := []

noncomputable def finish (p : Params) (cfg : Config) (s : State p) (aggregate : Point p) : State p :=
  let u := increment cfg ((p.n : ℝ)⁻¹ • aggregate)
  let x := s.point + u
  { s with
    point := x
    selected := if s.iteration + 1 = s.outputIndex then x else s.selected
    iteration := s.iteration + 1
    accumulator := 0
    arrived := ∅
    outbox := fun j => downlinkMessage p cfg s.draws s.iteration j x u
    targets := if s.iteration + 1 < cfg.iterations then List.finRange p.n else [] }

noncomputable def accept (p : Params) (cfg : Config) (s : State p)
    (source : Fin (p.n + 1)) (bits : List Bool) : State p :=
  Fin.cases s (fun i =>
    if i ∉ s.arrived ∧ s.iteration < cfg.iterations then
      let aggregate := s.accumulator + uplinkReceive p cfg s.draws s.iteration i bits
      let arrived := insert i s.arrived
      if arrived = Finset.univ then finish p cfg s aggregate
      else { s with accumulator := aggregate, arrived := arrived }
    else s) source

noncomputable def receive (p : Params) (cfg : Config) (s : State p)
    (i : Fin p.n) (bits : List Bool) : State p :=
  { s with
    point := downlinkReceive p cfg s.draws s.iteration i s.point bits
    iteration := s.iteration + 1
    accumulator := 0
    samples := 0
    pending := false
    sent := false }

noncomputable def algorithm (p : Params) (cfg : Config) [Nonempty (Fin p.d)] (T : Time) :
    Algorithm (LongTails.Setups.DistributedSmoothNonconvex.ComputeQuery p.toParams)
      (LongTails.Setups.DistributedSmoothNonconvex.ComputeReply p.toParams)
      (LongTails.Setups.DistributedSmoothNonconvex.CommReply p.toParams) (Point p) (p.n + 1) where
  clock _ := 0
  timer _ := T + 1
  Seed := Seed p cfg
  law := seedLaw p cfg
  State := State p
  root := 0
  initial _ seed := { draws := seed.2, point := p.x0, selected := p.x0, outputIndex := seed.1.val }
  update v s _ notification :=
    match notification with
    | .computed (.computed _ g) =>
        { s with accumulator := s.accumulator + g, samples := s.samples + 1, pending := false }
    | .received (.received source bits) =>
        Fin.cases (accept p cfg s source bits)
          (fun i => if source = 0 then receive p cfg s i bits else s) v
    | _ => s
  query v s _ :=
    let idle := (.advance 0, s)
    Fin.cases
      (match s.targets with
        | i :: rest => (.communicate (i.succ, s.outbox i), { s with targets := rest })
        | [] => idle)
      (fun i =>
        if s.iteration < cfg.iterations ∧ !s.pending then
          if s.samples < cfg.batch then
            (.compute (.evaluate s.point), { s with pending := true })
          else if !s.sent then
            (.communicate (0, uplinkMessage p cfg s.draws s.iteration i
              ((cfg.batch : ℝ)⁻¹ • s.accumulator)), { s with sent := true })
          else idle
        else idle) v
  output s := s.selected

def uplinkPayload (p : Params) (cfg : Config) : ℕ :=
  if cfg.fullUplink then p.d * cfg.uplinkWidth else cfg.uplinkCount * cfg.uplinkWidth

def downlinkPayload (p : Params) (cfg : Config) (k : ℕ) : ℕ :=
  if refresh cfg k then p.d * cfg.downlinkWidth else cfg.downlinkCount * cfg.downlinkWidth

noncomputable def roundTime (p : Params) (cfg : Config) (k : ℕ) : Time :=
  cfg.batch * Finset.univ.sup p.h + p.l + p.b * (uplinkPayload p cfg + clockBits : ℕ) +
    if k + 1 < cfg.iterations then p.l + p.b * (downlinkPayload p cfg k + clockBits : ℕ) else 0

noncomputable def executionTime (p : Params) (cfg : Config) : Time :=
  ∑ k ∈ Finset.range cfg.iterations, roundTime p cfg k

end LongTails.Algorithms.DistributedNormalizedProtocol
