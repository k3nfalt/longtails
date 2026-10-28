import LongTails.Template
import LongTails.Algorithms.FreyaCollectors

open MeasureTheory OracleTemplate
open scoped NNReal

namespace LongTails.Algorithms.FreyaPage

open LongTails.Proofs.FreyaModel LongTails.Algorithms.FreyaInputs
open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaCollectors

inductive Phase (d m n : ℕ) where
  | full (initial : Bool) (collector : FullState d m n)
  | difference (collector : DifferenceState d m n)
  | halted

structure State (q : Raw) where
  seed : Seed q.K
  iteration : ℕ
  x : Space q.d
  g : Space q.d
  selected : Space q.d
  clock : ℝ≥0
  nextID : ℕ
  phase : Phase q.d q.m q.n

def rounds (q : Raw) : ℕ := if q.«prefix» then q.K - 1 else q.K

noncomputable def initial (q : Raw) (seed : Seed q.K) : State q where
  seed := seed
  iteration := 0
  x := q.x0
  g := 0
  selected := q.x0
  clock := 0
  nextID := q.n
  phase := if q.m = 0 ∨ q.n = 0 ∨ q.K = 0 then .halted else
    .full true (fullInitial q.n (List.ofFn id) q.x0 0 (seed.1 0))

noncomputable def advance (q : Raw) (s : State q) : State q :=
  if rounds q ≤ s.iteration then { s with phase := .halted } else
    let x := s.x - q.η • s.g
    let batch := s.iteration + 1
    let phase := if refreshAt s.seed s.iteration then
      Phase.full false (fullInitial q.n (List.ofFn id) x s.clock (s.seed.1 batch) s.nextID)
    else
      Phase.difference (differenceInitial q.n q.S x s.x s.clock (s.seed.1 batch) s.nextID)
    { s with
      iteration := batch
      x := x
      selected := if (outputIndex s.seed).val = batch then x else s.selected
      phase := phase
      nextID := s.nextID + q.n }

noncomputable def query (q : Raw) (s : State q) :
    Fin 1 × Option (Request q.d q.m q.n) :=
  (0, match s.phase with
    | .halted => none
    | .full _ c => if c.remaining.isEmpty then none else pendingRequest c.clock c.pending
    | .difference c => if c.target ≤ c.count then none else pendingRequest c.clock c.pending)

noncomputable def update (q : Raw) (s : State q) (reply : Reply q.d q.n) : State q :=
  match s.phase with
  | .halted => s
  | .full first c =>
    let c := fullUpdate c reply
    let s := { s with clock := c.clock, nextID := c.nextID, phase := .full first c }
    if c.remaining.isEmpty then advance q { s with g := fullResult c } else s
  | .difference c =>
    let c := differenceUpdate c reply
    let s := { s with clock := c.clock, nextID := c.nextID, phase := .difference c }
    if c.target ≤ c.count then advance q { s with g := s.g + differenceResult c } else s

def output (q : Raw) (s : State q) : Space q.d × ℝ≥0 := (s.selected, s.clock)

noncomputable def factory (q : Raw) :
    Algorithm (Option (Request q.d q.m q.n)) (Reply q.d q.n) (Space q.d × ℝ≥0) 1 where
  Seed := Seed q.K
  law := seedLaw q.ρ q.K
  State := State q
  initial := initial q
  query := query q
  update := update q
  output := output q

noncomputable def literal (q : Raw) :
    Algorithm (Option (Request q.d q.m q.n)) (Reply q.d q.n) (Space q.d × ℝ≥0) 1 :=
  factory { q with «prefix» := false }

noncomputable def «prefix» (q : Raw) :
    Algorithm (Option (Request q.d q.m q.n)) (Reply q.d q.n) (Space q.d × ℝ≥0) 1 :=
  factory { q with «prefix» := true }

noncomputable def pointOnly (q : Raw) :
    Algorithm (Option (Request q.d q.m q.n)) (Reply q.d q.n) (Space q.d) 1 :=
  { factory q with output := fun s => (output q s).1 }

noncomputable def trace (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) : ℕ → State q
  | 0 => initial q seed
  | k + 1 => let s := trace q O seed ω k; update q s (O.answer k (query q s) (ω k))

def eventLimit (q : Raw) : ℕ := q.n * q.m + q.K * max (q.n * q.m) q.S

def active {q : Raw} (s : State q) : Bool :=
  match s.phase with
  | .halted => false
  | _ => true

noncomputable def batchStartCall (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Option ℕ :=
  (List.range (eventLimit q + 1)).find? fun k =>
    let s := trace q O seed ω k
    decide (s.iteration = batch) && active s

noncomputable def invocation (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) :
    Option (Bool × Space q.d × Space q.d × ℝ≥0 × ℕ) :=
  (batchStartCall q O seed ω batch).bind fun k =>
    let s := trace q O seed ω k
    match s.phase with
    | .halted => none
    | .full _ c => some (true, c.point, c.point, c.clock, c.nextID - q.n)
    | .difference c => some (false, c.x, c.y, c.clock, c.nextID - q.n)

noncomputable def collectorPendingAfter (q : Raw) (s : State q) (reply : Reply q.d q.n) :
    Fin q.n → Option (Job q.d q.m) :=
  match s.phase with
  | .halted => fun _ => none
  | .full _ c => (fullUpdate c reply).pending
  | .difference c => (differenceUpdate c reply).pending

@[instance_reducible]
noncomputable def historyBefore (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) (batch : ℕ) :
    MeasurableSpace (Seed q.K × ((k : ℕ) → O.Seed k)) :=
  MeasurableSpace.comap (fun z : Seed q.K × ((k : ℕ) → O.Seed k) =>
    (invocation q O z.1 z.2 batch, fun k : ℕ =>
      if k < (batchStartCall q O z.1 z.2 batch).getD 0 then
        let s := trace q O z.1 z.2 k
        let reply := O.answer k (query q s) (z.2 k)
        some (query q s, reply, collectorPendingAfter q s reply)
      else none)) inferInstance

def batchLabels (q : Raw) (seed : Seed q.K) (batch slot : ℕ) : Option (Fin q.m) :=
  labelAt (seed.1 batch slot) q.m

noncomputable def batchJobs (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch call : ℕ) (after : Bool) :
    Fin q.n → Option (Job q.d q.m) :=
  let s := trace q O seed ω call
  if s.iteration = batch then
    if after then collectorPendingAfter q s (O.answer call (query q s) (ω call)) else
      match s.phase with
      | .halted => fun _ => none
      | .full _ c => c.pending
      | .difference c => c.pending
  else fun _ => none

noncomputable def batchClock (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ) : Option ℝ≥0 :=
  (batchStartCall q O seed ω batch).map fun k => (trace q O seed ω k).clock

end LongTails.Algorithms.FreyaPage
