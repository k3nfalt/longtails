import LongTails.Algorithms.DashaScaling
import LongTails.Algorithms.DashaPackets
import LongTails.Algorithms.DashaModular

namespace LongTails.Algorithms.DashaDistributed

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open DashaScaling

structure Config (p : Params) where
  choice : Choice p
  initializer : Option (Choice p)
  iterations : ℕ+
  exponentWidth : ℕ
  initialWidth : ℕ
  broadcastWidth : ℕ
  slack : Time := 0
  modularInitialization : Bool := false

def modularAt (p : Params) (cfg : Config p) (k : ℕ) : Bool :=
  cfg.modularInitialization && cfg.initializer.isNone && decide (k = 0)

noncomputable def finishTotal (p : Params) (cfg : Config p) (k : ℕ) (z : Fin p.d → ℤ) : Fin p.d → ℤ :=
  if modularAt p cfg k then fun j => DashaModular.restore cfg.initialWidth (z j) else z

noncomputable def computationTime (p : Params) : Time :=
  Finset.univ.sup p.h

def initialBits (p : Params) (cfg : Config p) : ℕ :=
  match cfg.initializer with
  | none => p.d * cfg.initialWidth
  | some c => (c.block.val + 1) * (c.precision + cfg.initialWidth + 3)

def roundBits (p : Params) (cfg : Config p) : ℕ :=
  (cfg.choice.block.val + 1) * (cfg.choice.precision + cfg.exponentWidth + 3)

noncomputable def timeBudget (p : Params) (cfg : Config p) : Time :=
  computationTime p + p.l + p.b * (initialBits p cfg + clockBits : ℕ) +
    (((cfg.iterations : ℕ) - 1 : ℕ) : Time) * (computationTime p + p.l + p.b * (roundBits p cfg + clockBits : ℕ)) + cfg.slack

noncomputable def roundStart (p : Params) (cfg : Config p) (k : ℕ) : Time :=
  if k = 0 then 0 else computationTime p + p.l + p.b * (initialBits p cfg + clockBits : ℕ) +
    ((k - 1 : ℕ) : Time) * (computationTime p + p.l + p.b * (roundBits p cfg + clockBits : ℕ))

noncomputable def uploadTime (p : Params) (cfg : Config p) (k : ℕ) : Time :=
  p.l + p.b * ((if k = 0 then initialBits p cfg else roundBits p cfg) + clockBits : ℕ)

noncomputable def idealInitial (p : Params) (cfg : Config p) (f : Functions p) (seed : Sample p) : Iterate p :=
  match cfg.initializer with
  | none => initialIterate p cfg.choice f seed
  | some c => sparseInitialIterate p cfg.choice c f seed

noncomputable def idealTrajectory (p : Params) (cfg : Config p) (f : Functions p)
    (seed : ℕ → Sample p) : ℕ → Iterate p
  | 0 => idealInitial p cfg f (seed 0)
  | k + 1 => nextIterate p cfg.choice f (idealTrajectory p cfg f seed k) (seed (k + 1))

noncomputable def idealOutput (p : Params) (cfg : Config p) (f : Functions p)
    (seed : Fin cfg.iterations × (ℕ → Sample p)) : Point p :=
  (idealTrajectory p cfg f seed.2 seed.1.val).point

structure State (p : Params) where
  point : Point p
  selected : Point p
  outputIndex : ℕ
  randomness : ℕ → Sample p
  iteration : ℕ := 0
  localGradient : Point p := 0
  code : Fin p.d → ℤ := 0
  accumulator : Fin p.d → ℤ := 0
  pending : Bool := false
  sent : Bool := false
  arrived : Finset (Fin p.n) := ∅
  outbox : Option (List Bool) := none
  targets : List (Fin p.n) := []

noncomputable def advance (p : Params) (cfg : Config p) (s : State p) (total : Fin p.d → ℤ) : State p :=
  let point := s.point - stepSize p cfg.choice •
    ((1 / (p.n : ℝ)) • DashaQuantization.reconstruct (spacing p cfg.choice) total)
  { s with
    point := point
    selected := if s.iteration + 1 = s.outputIndex then point else s.selected
    iteration := s.iteration + 1
    accumulator := 0
    pending := false
    sent := false
    arrived := ∅
    outbox := none
    targets := [] }

noncomputable def uplinkMessage (p : Params) (cfg : Config p) (i : Fin p.n) (s : State p)
    (h : Point p) : List Bool :=
  let seed := s.randomness s.iteration i
  if s.iteration = 0 then
    match cfg.initializer with
    | none => if cfg.modularInitialization then
        DashaModular.encode p.d cfg.initialWidth (DashaQuantization.indices p.d false (spacing p cfg.choice) h seed.2)
      else DashaQuantization.message p.d cfg.initialWidth false (spacing p cfg.choice) h seed.2
    | some c => DashaPackets.message c.block c.precision cfg.initialWidth (spacing p cfg.choice) h seed
  else
    DashaPackets.message cfg.choice.block cfg.choice.precision cfg.exponentWidth (spacing p cfg.choice)
      (h - s.localGradient - momentum p cfg.choice •
        (DashaQuantization.reconstruct (spacing p cfg.choice) s.code - s.localGradient)) seed

noncomputable def uplinkReceive (p : Params) (cfg : Config p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) (bits : List Bool) : Fin p.d → ℤ :=
  if k = 0 then
    match cfg.initializer with
    | none => if cfg.modularInitialization then DashaModular.decode p.d cfg.initialWidth bits
      else DashaQuantization.decode p.d cfg.initialWidth bits
    | some c => DashaPackets.receive c.block (seed k i).1 c.precision cfg.initialWidth bits
  else DashaPackets.receive cfg.choice.block (seed k i).1 cfg.choice.precision cfg.exponentWidth bits

noncomputable def localIncrement (p : Params) (cfg : Config p) (i : Fin p.n) (s : State p)
    (h : Point p) (bits : List Bool) : Fin p.d → ℤ :=
  if modularAt p cfg s.iteration then
    DashaQuantization.indices p.d false (spacing p cfg.choice) h (s.randomness s.iteration i).2
  else uplinkReceive p cfg s.randomness s.iteration i bits

noncomputable def computed (p : Params) (cfg : Config p) (i : Fin p.n) (s : State p) (h : Point p) : State p :=
  let bits := uplinkMessage p cfg i s h
  let increment := localIncrement p cfg i s h bits
  { s with
    localGradient := h
    code := s.code + increment
    pending := false
    outbox := some bits }

noncomputable def accept (p : Params) (cfg : Config p) (s : State p)
    (source : Fin (p.n + 1)) (bits : List Bool) : State p :=
  Fin.cases s (fun i =>
    if i ∉ s.arrived then
      let accumulator := s.accumulator + uplinkReceive p cfg s.randomness s.iteration i bits
      let arrived := insert i s.arrived
      if arrived = Finset.univ then
        let total := finishTotal p cfg s.iteration (s.code + accumulator)
        let broadcast := DashaQuantization.encode p.d cfg.broadcastWidth total
        { advance p cfg s (DashaQuantization.decode p.d cfg.broadcastWidth broadcast) with
          code := total
          outbox := some broadcast
          targets := List.finRange p.n }
      else { s with accumulator := accumulator, arrived := arrived }
    else s) source

noncomputable def algorithm (p : Params) (cfg : Config p) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) where
  clock _ := 0
  timer _ := timeBudget p cfg + 1
  Seed := Fin cfg.iterations × (ℕ → Sample p)
  law := ⟨(PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod
    (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)), inferInstance⟩
  State := State p
  root := 0
  initial _ seed :=
    { point := p.x0
      selected := p.x0
      outputIndex := seed.1.val
      randomness := seed.2 }
  update v s _ notification :=
    match notification with
    | .computed (.computed _ h) => Fin.cases s (fun i => computed p cfg i s h) v
    | .received (.received source bits) =>
        if v = 0 then accept p cfg s source bits
        else if source = 0 then advance p cfg s (DashaQuantization.decode p.d cfg.broadcastWidth bits)
        else s
    | .wake => s
  query v s _ :=
    let idle := (.advance 0, s)
    Fin.cases
      (match s.outbox, s.targets with
        | some bits, i :: rest =>
            (.communicate (i.succ, bits),
              { s with outbox := if rest.isEmpty then none else some bits, targets := rest })
        | _, _ => idle)
      (fun _ =>
        if s.iteration < cfg.iterations ∧ !s.pending ∧ !s.sent then
          match s.outbox with
          | some bits => (.communicate (0, bits), { s with outbox := none, sent := true })
          | none => (.compute (.evaluate s.point), { s with pending := true })
        else idle) v
  output s := s.selected

end LongTails.Algorithms.DashaDistributed
