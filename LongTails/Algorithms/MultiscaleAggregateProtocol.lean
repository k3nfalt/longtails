import LongTails.Algorithms.MultiscaleAggregate

namespace LongTails.Algorithms.MultiscaleAggregate

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open DistributedTemplate

structure Model (p : Params) where
  point : Point p
  estimates : ℕ → Point p

noncomputable def initialModel (p : Params) : Model p := ⟨p.x0, fun _ => 0⟩

noncomputable def advance (p : Params) (m : Model p) (k : ℕ) (z : Code p) : Model p :=
  let anchor := if k = 0 then 0 else m.estimates ((schedule p).pred k)
  let estimate := recover p k anchor z
  ⟨OracleTemplate.NormalizedStorm.stormStep (precision p / p.L) m.point estimate,
    Function.update m.estimates k estimate⟩

noncomputable def batchMean (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (i : Fin p.n) (x : Point p) : Point p :=
  (batch p i : ℝ)⁻¹ • ∑ j ∈ Finset.range (batch p i), g i x (samples i (k * batch p i + j))

noncomputable def workerMessage (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (i : Fin p.n) (x : Point p) : List Bool :=
  packet p k (localCode p (batchMean p g samples k i x))

noncomputable def rootMessage (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) (k : ℕ) (x : Point p) : List Bool :=
  packet p k (∑ i, readPacket p k (workerMessage p g samples k i x))

noncomputable def trajectory (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : Samples p) : ℕ → Model p
  | 0 => initialModel p
  | k + 1 =>
    let previous := trajectory p g samples k
    advance p previous k (readPacket p k (rootMessage p g samples k previous.point))

abbrev Indices (p : Params) := Fin (rounds p)

noncomputable def output (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (seed : Indices p × Samples p) : Point p := (trajectory p g seed.2 seed.1.val).point

structure State (p : Params) where
  model : Model p
  selected : Point p
  outputIndex : ℕ
  iteration : ℕ := 0
  accumulator : Point p := 0
  total : Code p := 0
  samples : ℕ := 0
  pending : Bool := false
  sent : Bool := false
  arrived : Finset (Fin p.n) := ∅
  outbox : List Bool := []
  targets : List (Fin p.n) := []

noncomputable def receive (p : Params) (s : State p) (bits : List Bool) : State p :=
  let m := advance p s.model s.iteration (readPacket p s.iteration bits)
  { s with
    model := m
    iteration := s.iteration + 1
    accumulator := 0
    samples := 0, pending := false, sent := false }

noncomputable def finish (p : Params) (s : State p) (z : Code p) : State p :=
  let message := packet p s.iteration z
  let m := advance p s.model s.iteration (readPacket p s.iteration message)
  { s with
    model := m
    selected := if s.iteration + 1 = s.outputIndex then m.point else s.selected
    iteration := s.iteration + 1
    total := 0
    arrived := ∅
    outbox := message
    targets := if s.iteration + 1 < rounds p then List.finRange p.n else [] }

noncomputable def accept (p : Params) (s : State p) (source : Fin (p.n + 1))
    (bits : List Bool) : State p := by
  classical
  exact Fin.cases s (fun i =>
    if i ∉ s.arrived ∧ s.iteration < rounds p then
      let z := s.total + readPacket p s.iteration bits
      let arrived := insert i s.arrived
      if arrived = Finset.univ then finish p s z
      else { s with arrived := arrived, total := z }
    else s) source

noncomputable def algorithm (p : Params) (T : Time) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) where
  clock _ := 0
  timer _ := T + 1
  Seed := Indices p
  law := by
    letI : NeZero (rounds p) := ⟨by unfold rounds; positivity⟩
    exact ⟨(PMF.uniformOfFintype (Indices p)).toMeasure, inferInstance⟩
  State := State p
  root := 0
  initial _ seed := { model := initialModel p, selected := p.x0, outputIndex := seed.val }
  update v s _ event :=
    match event with
    | .computed (.computed _ g) =>
      { s with accumulator := s.accumulator + g, samples := s.samples + 1, pending := false }
    | .received (.received source bits) =>
      Fin.cases (accept p s source bits)
        (fun _ => if source = 0 then receive p s bits else s) v
    | .wake => s
  query v s _ :=
    let idle := (.advance 0, s)
    Fin.cases
      (match s.targets with
        | i :: rest => (.communicate (i.succ, s.outbox), { s with targets := rest })
        | [] => idle)
      (fun i =>
        if s.iteration < rounds p ∧ !s.pending then
          if s.samples < batch p i then
            (.compute (.evaluate s.model.point), { s with pending := true })
          else if !s.sent then
            (.communicate (0, packet p s.iteration
              (localCode p ((batch p i : ℝ)⁻¹ • s.accumulator))), { s with sent := true })
          else idle
        else idle) v
  output s := s.selected

end LongTails.Algorithms.MultiscaleAggregate
