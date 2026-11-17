import LongTails.Algorithms.DistributedQuantization
import LongTails.Algorithms.Clipping
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Size
import Mathlib.Data.List.MinMax

namespace LongTails.Algorithms.DistributedBatchedSgd

open DistributedTemplate
open LongTails.Setups.DistributedSmoothNonconvex

structure Config (p : Params) where
  iterations : ℕ+
  batch : Fin p.n → ℕ
  width : ℕ+
  slack : Time := 0

noncomputable def iterations (p : Params) : ℕ+ :=
  ⟨max 1 ⌈16 * p.L * p.Δ / p.ε⌉₊, by omega⟩

noncomputable def targetBatch (p : Params) : ℕ := max 1 ⌈256 * p.σ ^ 2 / p.ε⌉₊

noncomputable def throughput (p : Params) (i : Fin p.n) : Time :=
  ∑ j, if p.h j ≤ p.h i then (p.h j)⁻¹ else 0

noncomputable def candidateTime (p : Params) (i : Fin p.n) : Time :=
  2 * max (p.h i) ((targetBatch p : Time) / throughput p i)

noncomputable def batchTime (p : Params) : Time :=
  (((List.finRange p.n).argmin (candidateTime p)).map (candidateTime p)).getD 0

noncomputable def config (p : Params) : Config p where
  iterations := iterations p
  batch i := ⌊(batchTime p : ℝ) / (p.h i : ℝ)⌋₊
  width := ⟨Nat.size ⌈Real.sqrt (1 + 8192 * p.d * ((iterations p : ℕ) : ℝ) ^ 2 +
    16 * p.d * (1280 * p.L * p.Δ / p.ε + 160 + 163840 * (p.σ ^ 2 / p.ε) ^ 2 +
      2560 * (iterations p : ℕ) * p.L * p.Δ / p.ε))⌉₊ + 1, by omega⟩

def active (p : Params) (cfg : Config p) : Finset (Fin p.n) :=
  Finset.univ.filter fun i => 0 < cfg.batch i

def totalBatch (p : Params) (cfg : Config p) : ℕ := ∑ i, cfg.batch i

noncomputable def computationTime (p : Params) (cfg : Config p) : Time :=
  (List.finRange p.n).foldl (fun t i => max t (cfg.batch i * p.h i)) 0

noncomputable def roundTime (p : Params) (cfg : Config p) : Time :=
  computationTime p cfg + 2 * (p.l + p.b * (p.d * cfg.width + clockBits : ℕ))

noncomputable def timeBudget (p : Params) (cfg : Config p) : Time :=
  cfg.iterations * roundTime p cfg + cfg.slack

noncomputable def withBudget (p : Params) (T : Time) : Config p :=
  { config p with slack := T - timeBudget p (config p) }

noncomputable def radius (p : Params) (x : Point p) : ℝ :=
  2 * (Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖) + Real.sqrt p.ε + 32 * p.σ ^ 2 / Real.sqrt p.ε

noncomputable def spacing (p : Params) (cfg : Config p) (x : Point p) : ℝ :=
  2 * radius p x / ((2 ^ (cfg.width : ℕ) - 1 : ℕ) : ℝ)

noncomputable def encode (p : Params) (cfg : Config p) (x g : Point p) : List Bool :=
  DistributedQuantization.message p.d cfg.width (spacing p cfg x) (OracleTemplate.clip (radius p x) g)

noncomputable def decode (p : Params) (cfg : Config p) (x : Point p) (bits : List Bool) : Point p :=
  DistributedQuantization.receive p.d cfg.width (spacing p cfg x) (bits.take (p.d * cfg.width))

noncomputable def batchMean (p : Params) (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (k : ℕ)
    (samples : Samples p) (i : Fin p.n) : Point p :=
  (cfg.batch i : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch i),
    g i x (samples i (k * cfg.batch i + j))

noncomputable def estimate (p : Params) (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Point p) (k : ℕ)
    (samples : Samples p) : Point p :=
  let aggregate := ∑ i, ((cfg.batch i : ℝ) / totalBatch p cfg) •
    decode p cfg x (encode p cfg x (batchMean p cfg g x k samples i))
  decode p cfg x (encode p cfg x aggregate)

noncomputable def trajectory (p : Params) (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : Samples p) : ℕ → Point p
  | 0 => p.x0
  | k + 1 =>
      let x := trajectory p cfg g samples k
      x - (1 / p.L) • estimate p cfg g x k samples

noncomputable def output (p : Params) (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (seed : Fin cfg.iterations × Samples p) : Point p :=
  trajectory p cfg g seed.2 seed.1.val

structure State (p : Params) where
  point : Point p
  selected : Point p
  outputIndex : ℕ
  iteration : ℕ := 0
  accumulator : Point p := 0
  samples : ℕ := 0
  pending : Bool := false
  sent : Bool := false
  arrived : Finset (Fin p.n) := ∅
  outbox : Option (List Bool) := none
  targets : List (Fin p.n) := []
  wakeAt : Time := 0

noncomputable def advance (p : Params) (s : State p) (g : Point p) : State p :=
  let point := s.point - (1 / p.L) • g
  { s with
    point := point
    selected := if s.iteration + 1 = s.outputIndex then point else s.selected
    iteration := s.iteration + 1
    accumulator := 0
    samples := 0
    pending := false
    sent := false
    arrived := ∅ }

noncomputable def accept (p : Params) (cfg : Config p) (s : State p)
    (source : Fin (p.n + 1)) (bits : List Bool) : State p :=
  Fin.cases s (fun i =>
    if i ∈ active p cfg ∧ i ∉ s.arrived then
      let aggregate := s.accumulator +
        ((cfg.batch i : ℝ) / totalBatch p cfg) • decode p cfg s.point bits
      let arrived := insert i s.arrived
      if arrived = active p cfg then
        let broadcast := encode p cfg s.point aggregate
        { advance p s (decode p cfg s.point broadcast) with outbox := some broadcast, targets := (active p cfg).toList }
      else { s with accumulator := aggregate, arrived := arrived }
    else s) source

noncomputable def algorithm (p : Params) (cfg : Config p) :
    Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) (p.n + 1) where
  clock _ := 0
  timer _ := timeBudget p cfg + 1
  Seed := Fin cfg.iterations
  law := ⟨(PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure, inferInstance⟩
  State := State p
  root := 0
  initial _ seed := { point := p.x0, selected := p.x0, outputIndex := seed.val }
  update v s _ notification :=
    match notification with
    | .computed (.computed _ g) =>
        { s with accumulator := s.accumulator + g, samples := s.samples + 1, pending := false }
    | .received (.received source bits) =>
        if v = 0 then accept p cfg s source bits
        else if source = 0 then advance p s (decode p cfg s.point bits)
        else s
    | _ => s
  query v s _ :=
    let nextWake := timeBudget p cfg + 1
    let idle := (.advance 0, { s with wakeAt := nextWake })
    Fin.cases
      (match s.outbox, s.targets with
        | some bits, i :: rest =>
            (.communicate (i.succ, bits),
              { s with outbox := if rest.isEmpty then none else some bits, targets := rest })
        | _, _ => idle)
      (fun i =>
        if 0 < cfg.batch i ∧ s.iteration < cfg.iterations ∧ !s.pending then
          if s.samples < cfg.batch i then
            (.compute (.evaluate s.point), { s with pending := true })
          else if !s.sent then
            let bits := encode p cfg s.point ((cfg.batch i : ℝ)⁻¹ • s.accumulator)
            (.communicate (0, bits), { s with sent := true })
          else idle
        else idle) v
  output s := s.selected

end LongTails.Algorithms.DistributedBatchedSgd
