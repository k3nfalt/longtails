import LongTails.Algorithms.DistributedLocalExtragradientTuning
import LongTails.Algorithms.DistributedLocalExtragradientWorker
import LongTails.Algorithms.DistributedLocalExtragradientTree
import LongTails.Algorithms.DistributedLocalExtragradientMedianSearch

namespace LongTails.Algorithms.DistributedLocalExtragradientProtocol

open MeasureTheory
open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open DistributedLocalExtragradientTuning
open DistributedLocalExtragradientTree
open DistributedLocalExtragradientMedianSearch
open LocalExtragradientQuantization
open DistributedQuantization

inductive Phase where
  | baseline
  | warming
  | median (remaining : ℕ)
  | refinement (epoch : ℕ)
  | done
  deriving DecidableEq

structure State (p : Params) where
  phase : Phase
  current : Point p
  anchor : Point p
  warmCodes : Fin p.d → ℕ := fun _ => 0
  lower : Fin p.d → ℕ := fun _ => 0
  work : Option (DistributedLocalExtragradientWorker.Work p) := none
  busy : Bool := false
  own : Fin p.d → ℕ := fun _ => 0
  ready : Bool := false
  collector : Collector p.n p.d := emptyCollector (fun _ => 0)
  sent : Bool := false
  queue : List (Fin p.n × List Bool) := []

noncomputable def startMedian (p : Params) (remaining : ℕ) (s : State p) : State p :=
  { s with
    phase := .median remaining
    work := none
    busy := false
    own := fun j => if s.warmCodes j < s.lower j + 2 ^ (remaining - 1) then 1 else 0
    ready := true
    collector := emptyCollector (fun _ => 0)
    sent := false }

noncomputable def startRefinement (p : Params) (epoch : ℕ) (s : State p) : State p :=
  if epoch < refinementCount p (localDepth p) then
    { s with
      phase := .refinement epoch
      work := some (.first (localDepth p) s.current)
      busy := false
      own := fun _ => 0
      ready := false
      collector := emptyCollector (fun _ => 0)
      sent := false }
  else { s with
    phase := .done
    work := none
    busy := false
    ready := false
    collector := emptyCollector (fun _ => 0)
    sent := false }

noncomputable def finishLocal (p : Params) (s : State p) (x : Point p) : State p :=
  match s.phase with
  | .baseline => { s with phase := .done, current := x, work := none, busy := false, ready := false }
  | .warming =>
      let codes := quantize p.d (warmWidth p (localDepth p)) (warmSpacing p (localDepth p))
        (DistributedLocalExtragradient.projectBall p p.x0 p.R x - p.x0)
      let next := startMedian p (warmWidth p (localDepth p))
        { s with warmCodes := fun j => (codes j).val, lower := fun _ => 0 }
      { next with collector := s.collector }
  | .refinement _ =>
      let codes := quantize p.d (refinementWidth p (localDepth p)) (refinementSpacing p (localDepth p))
        (OracleTemplate.clip (clipRadius p (localDepth p)) (x - s.current))
      { s with work := none, busy := false, own := fun j => (codes j).val, ready := true }
  | _ => { s with work := none, busy := false }

noncomputable def upWidth (p : Params) (phase : Phase) : ℕ :=
  match phase with
  | .warming => countWidth p.n
  | .median _ => countWidth p.n
  | .refinement _ => refinementWidth p (localDepth p) + countWidth p.n
  | _ => 0

noncomputable def downWidth (p : Params) (phase : Phase) : ℕ :=
  match phase with
  | .median _ => 1
  | .refinement _ => refinementWidth p (localDepth p) + countWidth p.n
  | _ => 0

noncomputable def broadcastValues (p : Params) (phase : Phase) (totals : Fin p.d → ℕ) : Fin p.d → ℕ :=
  match phase with
  | .median _ => fun j => if (p.n : ℕ) / 2 < totals j then 1 else 0
  | _ => totals

noncomputable def finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ) : State p :=
  match s.phase with
  | .median remaining =>
      let lower := nextLower (remaining - 1) s.lower (fun j => decide (values j = 1))
      let next := { s with lower := lower }
      if 1 < remaining then startMedian p (remaining - 1) next
      else
        let center := DistributedLocalExtragradient.projectBall p p.x0 p.R
          (p.x0 + reconstruct (warmSpacing p (localDepth p))
            (packNaturals (warmWidth p (localDepth p)) lower))
        startRefinement p 0 { next with current := center, anchor := center }
  | .refinement epoch =>
      let nextPoint := DistributedLocalExtragradient.localizedOutput p s.anchor (radius p (localDepth p))
        (s.current + decodeAverage p.n (refinementWidth p (localDepth p))
          (refinementSpacing p (localDepth p)) values)
      startRefinement p (epoch + 1) { s with current := nextPoint }
  | _ => s

noncomputable def relay (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ) : State p :=
  let bits := naturalMessage (downWidth p s.phase) values
  { finishBroadcast p s values with queue := (children p v).toList.map (fun child => (child, bits)) }

noncomputable def initialState (p : Params) (v : Fin p.n) : State p :=
  if p.R ≤ p.ε then { phase := .done, current := p.x0, anchor := p.x0 }
  else if 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ) then
    { phase := .warming, current := p.x0, anchor := p.x0,
      work := some (.warm (warmCount p (localDepth p)) p.x0) }
  else if v = p.root then
    { phase := .baseline, current := p.x0, anchor := p.x0,
      work := some (.warm (baselineCount p) p.x0) }
  else { phase := .done, current := p.x0, anchor := p.x0 }

noncomputable def query (p : Params) (v : Fin p.n) (s : State p) :
    Action (Point p) p.n × State p := by
  classical
  exact match s.queue with
  | packet :: rest => (.communicate packet, { s with queue := rest })
  | [] =>
      match s.work with
      | some work =>
          if s.busy then (.advance 1, s)
          else match DistributedLocalExtragradientWorker.query work with
            | some x => (.compute x, { s with busy := true })
            | none => (.advance 0, finishLocal p s (DistributedLocalExtragradientWorker.point work))
      | none =>
          if s.ready ∧ ¬ s.sent ∧ children p v ⊆ s.collector.seen then
            let totals := fun j => s.own j + s.collector.total j
            if v = p.root then
              (.advance 0, relay p v s (broadcastValues p s.phase totals))
            else (.communicate (p.parent v, naturalMessage (upWidth p s.phase) totals), { s with sent := true })
          else (.advance 1, s)

noncomputable def update (p : Params) (v : Fin p.n) (s : State p)
    (notification : Event (Point p) (CommReply p)) : State p := by
  classical
  exact match notification with
  | .wake => s
  | .computed value =>
      match s.work with
      | some work => if s.busy then
          { s with work := some (DistributedLocalExtragradientWorker.reply p work value), busy := false }
        else s
      | none => s
  | .received message =>
      if v ≠ p.root ∧ message.source = p.parent v then
        relay p v s (receiveNaturals p.d (downWidth p s.phase) message.bits)
      else
        { s with collector := accept (children p v) s.collector message.source (receiveNaturals p.d (upWidth p s.phase) message.bits) }

noncomputable def algorithm (p : Params) (idle : Time) :
    Algorithm (Point p) (Point p) (CommReply p) (Point p) p.n where
  clock := fun _ => 0
  timer := fun code => if code = 0 then 0 else idle
  State := State p
  root := p.root
  initial := fun v _ => initialState p v
  query := fun v s _ => query p v s
  update := fun v s _ => update p v s
  output := State.current

end LongTails.Algorithms.DistributedLocalExtragradientProtocol
