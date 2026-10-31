import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.List.MinMax

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Setups.FreyaModel

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def objective {d m : ℕ} (f : Fin m → Space d → ℝ) (x : Space d) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, f i x

structure RegularObjective {d m : ℕ} (f : Fin m → Space d → ℝ)
    (x0 : Space d) (lower Lminus Lplus Lpm Δ : ℝ) : Prop where
  differentiable : ∀ i, Differentiable ℝ (f i)
  lower_bound : ∀ x, lower ≤ objective f x
  smooth : ∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤
    Lminus * ‖x - y‖
  mean_square : ∀ x y, (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
    Lplus ^ 2 * ‖x - y‖ ^ 2
  centered : ∀ x y, (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) -
    ‖gradient (objective f) x - gradient (objective f) y‖ ^ 2 ≤ Lpm ^ 2 * ‖x - y‖ ^ 2
  gap : objective f x0 - lower ≤ Δ

def JobKind (d : ℕ) := Space d ⊕ (Space d × Space d)

instance instMeasurableSpaceJobKind (d : ℕ) : MeasurableSpace (JobKind d) :=
  inferInstanceAs (MeasurableSpace (Space d ⊕ (Space d × Space d)))

instance instMeasurableSpaceOption {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  MeasurableSpace.comap (fun x => match x with
    | none => Sum.inl ()
    | some a => Sum.inr a) (inferInstance : MeasurableSpace (Unit ⊕ α))

structure Job (d m : ℕ) where
  component : Fin m
  kind : JobKind d
  started : ℝ≥0
  id : ℕ

instance instMeasurableSpaceJob (d m : ℕ) : MeasurableSpace (Job d m) :=
  MeasurableSpace.comap (fun j => (j.component, j.kind, j.started, j.id)) inferInstance

structure Request (d m n : ℕ) where
  clock : ℝ≥0
  pending : Fin n → Option (Job d m)

instance instMeasurableSpaceRequest (d m n : ℕ) : MeasurableSpace (Request d m n) :=
  MeasurableSpace.comap (fun r => (r.clock, r.pending)) inferInstance

def Reply (d n : ℕ) := Option (Fin n × ℕ × ℝ≥0 × Space d)

instance instMeasurableSpaceReply (d n : ℕ) : MeasurableSpace (Reply d n) :=
  inferInstanceAs (MeasurableSpace (Option (Fin n × ℕ × ℝ≥0 × Space d)))

abbrev HistoryAt (Query Reply : Type*) (k : ℕ) :=
  {history : List ((Fin 1 × Query) × Reply) // history.length = k}

def historyCoordinates {Query Reply : Type*} (k : ℕ) (history : HistoryAt Query Reply k) :
    Fin k → (Fin 1 × Query) × Reply :=
  fun i => history.val.get (i.cast history.property.symm)

@[instance_reducible]
instance historyAtMeasurableSpace {Query Reply : Type*} [MeasurableSpace Query]
    [MeasurableSpace Reply] (k : ℕ) : MeasurableSpace (HistoryAt Query Reply k) :=
  MeasurableSpace.comap (historyCoordinates k) inferInstance

def answerAt {Query Reply : Type*} (O : Oracle Query Reply 1) (k : ℕ)
    (history : HistoryAt Query Reply k) (query : Fin 1 × Query) (seed : O.Seed k) : Reply :=
  O.answer history.val query (cast (congrArg O.Seed history.property.symm) seed)

def HistoryOblivious {Query Reply : Type*} (O : Oracle Query Reply 1) : Prop :=
  ∀ (history other : List ((Fin 1 × Query) × Reply)) (query : Fin 1 × Query)
    (ω : (k : ℕ) → O.Seed k), history.length = other.length →
      O.answer history query (ω history.length) = O.answer other query (ω other.length)

noncomputable def jobValue {d m : ℕ} (f : Fin m → Space d → ℝ) (j : Job d m) :
    Space d :=
  match j.kind with
  | Sum.inl x => gradient (f j.component) x
  | Sum.inr (x, y) => gradient (f j.component) x - gradient (f j.component) y

def jobWork {d m : ℕ} (j : Job d m) : ℕ :=
  match j.kind with
  | Sum.inl _ => 1
  | Sum.inr _ => 2

noncomputable def deadline {d m n : ℕ} (τ : Fin n → ℝ≥0∞) (j : Job d m)
    (i : Fin n) : ℝ≥0∞ :=
  j.started + (jobWork j : ℝ≥0∞) * τ i

def legalRequest {d m n : ℕ} (τ : Fin n → ℝ≥0∞) (r : Request d m n) : Prop :=
  (∃ i j, r.pending i = some j) ∧
    ∀ i j, r.pending i = some j → j.started ≤ r.clock ∧ (r.clock : ℝ≥0∞) ≤ deadline τ j i

def PrimitiveService {d m n : ℕ} (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (O : Oracle (Option (Request d m n)) (Reply d n) 1) : Prop :=
  (HistoryOblivious O ∧
    ∀ k, Measurable (fun z : (HistoryAt (Option (Request d m n)) (Reply d n) k ×
      (Fin 1 × Option (Request d m n))) × O.Seed k => answerAt O k z.1.1 z.1.2 z.2)) ∧
  ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)),
    ∀ history : List ((Fin 1 × Option (Request d m n)) × Reply d n),
    O.answer history (0, none) (ω history.length) = none ∧
    ∀ r, legalRequest τ r → ∃ i j c,
      r.pending i = some j ∧
      O.answer history (0, some r) (ω history.length) = some (i, j.id, c, jobValue f j) ∧
      r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i'

def FreshAssignments {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (history : ℕ → MeasurableSpace Ω) (remaining : ℕ → Ω → Finset ℕ)
    (chosen : ℕ → Ω → ℕ) : Prop :=
  ∀ k, history k ≤ ‹MeasurableSpace Ω› ∧ Measurable[history k] (remaining k) ∧
    Measurable (chosen k) ∧ ∀ E, MeasurableSet[history k] E → ∀ j,
      (∫⁻ ω in E, if (remaining k ω).Nonempty ∧ chosen k ω = j
        then (1 : ℝ≥0∞) else 0 ∂(P : Measure Ω)) =
      ∫⁻ ω in E, if j ∈ remaining k ω then ((remaining k ω).card : ℝ≥0∞)⁻¹
        else 0 ∂(P : Measure Ω)

def LiveService {d m n : ℕ} (τ : Fin n → ℝ≥0∞)
    (O : Oracle (Option (Request d m n)) (Reply d n) 1) : Prop :=
  ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)),
    ∀ (history : List ((Fin 1 × Option (Request d m n)) × Reply d n)) r, legalRequest τ r →
    ∃ i j c v, r.pending i = some j ∧
      O.answer history (0, some r) (ω history.length) = some (i, j.id, c, v) ∧
      r.clock ≤ c

noncomputable def equilibriumTime {n : ℕ} (τ : Fin n → ℝ≥0∞) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ j : Fin n, (r + (j.val + 1 : ℕ)) / ∑ i ∈ Finset.Iic j, (τ i)⁻¹

def largeSample (m n : ℕ) : Prop := (n : ℝ) * Real.log n ≤ m

end LongTails.Setups.FreyaModel

open scoped ENNReal

namespace LongTails.Algorithms.FreyaInputs

open LongTails.Setups.FreyaModel

structure Base where
  d : ℕ
  m : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d

structure Serial extends Base where
  S : ℕ
  ρ : ℝ

structure Workers extends Base where
  n : ℕ

structure Family extends Workers where
  S : ℕ
  ρ : ℝ

structure Optimized extends Workers where
  τ : Fin n → ℝ≥0∞

structure Simple extends Workers

structure Raw where
  d : ℕ
  m : ℕ
  n : ℕ
  x0 : Space d
  η : ℝ
  S : ℕ
  ρ : ℝ
  K : ℕ
  «prefix» : Bool

structure SerialRaw where
  d : ℕ
  m : ℕ
  x0 : Space d
  η : ℝ
  S : ℕ
  ρ : ℝ
  K : ℕ

end LongTails.Algorithms.FreyaInputs

open MeasureTheory ProbabilityTheory

namespace LongTails.Algorithms.FreyaRandomness

abbrev ChoiceRow := (j : ℕ) → Fin (j + 1)

noncomputable def rowLaw : ProbabilityMeasure ChoiceRow :=
  ⟨Measure.infinitePi (fun j : ℕ => (PMF.uniformOfFintype (Fin (j + 1))).toMeasure),
    inferInstance⟩

noncomputable def choiceTapeLaw : ProbabilityMeasure (ℕ → ℕ → ChoiceRow) :=
  ⟨Measure.infinitePi (fun _ : ℕ =>
    Measure.infinitePi (fun _ : ℕ => (rowLaw : Measure ChoiceRow))), inferInstance⟩

noncomputable def refreshLaw (ρ : ℝ) : ProbabilityMeasure (ℕ → Bool) :=
  let p : unitInterval := Set.projIcc 0 1 zero_le_one ρ
  ⟨Measure.infinitePi (fun _ : ℕ => bernoulliMeasure true false p), inferInstance⟩

abbrev Seed (K : ℕ) := (ℕ → ℕ → ChoiceRow) × (ℕ → Bool) × Fin (max 1 K)

noncomputable def seedLaw (ρ : ℝ) (K : ℕ) : ProbabilityMeasure (Seed K) := by
  haveI : NeZero (max 1 K) := ⟨by omega⟩
  exact ⟨(choiceTapeLaw : Measure _).prod
    ((refreshLaw ρ : Measure _).prod (PMF.uniformOfFintype (Fin (max 1 K))).toMeasure),
    inferInstance⟩

def chooseRemaining {α : Type*} (row : ChoiceRow) (remaining : List α) : Option α :=
  if h : remaining.length = 0 then none
  else
    let index := row (remaining.length - 1)
    some (remaining.get ⟨index.val, by have hi := index.isLt; omega⟩)

def labelAt (row : ChoiceRow) (m : ℕ) : Option (Fin m) :=
  if h : 0 < m then
    let index := row (m - 1)
    some ⟨index.val, by have hi := index.isLt; omega⟩
  else none

def refreshAt {K : ℕ} (seed : Seed K) (batch : ℕ) : Bool := seed.2.1 batch

def outputIndex {K : ℕ} (seed : Seed K) : Fin (max 1 K) := seed.2.2

end LongTails.Algorithms.FreyaRandomness

open scoped NNReal

namespace LongTails.Algorithms.FreyaCollectors

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaRandomness

structure FullState (d m n : ℕ) where
  original : List (Fin m)
  remaining : List ℕ
  point : Space d
  sum : Space d
  pending : Fin n → Option (Job d m)
  clock : ℝ≥0
  rows : ℕ → ChoiceRow
  nextID : ℕ

structure DifferenceState (d m n : ℕ) where
  target : ℕ
  count : ℕ
  x : Space d
  y : Space d
  sum : Space d
  pending : Fin n → Option (Job d m)
  clock : ℝ≥0
  rows : ℕ → ChoiceRow
  nextID : ℕ

def dispatch {d m : ℕ} (kind : JobKind d) (clock : ℝ≥0) (id : ℕ)
    (component : Option (Fin m)) : Option (Job d m) :=
  component.map fun i => ⟨i, kind, clock, id⟩

def selectedLabel {m : ℕ} (original : List (Fin m)) (remaining : List ℕ)
    (row : ChoiceRow) : Option (Fin m) :=
  (chooseRemaining row remaining).bind fun j => original[j]?

noncomputable def pendingRequest {d m n : ℕ} (clock : ℝ≥0)
    (pending : Fin n → Option (Job d m)) : Option (Request d m n) := by
  classical
  exact if ∃ i, pending i ≠ none then some ⟨clock, pending⟩ else none

def fullInitial {d m : ℕ} (n : ℕ) (labels : List (Fin m)) (x : Space d)
    (clock : ℝ≥0) (rows : ℕ → ChoiceRow) (firstID : ℕ := 0) : FullState d m n where
  original := labels
  remaining := List.range labels.length
  point := x
  sum := 0
  pending := fun i => dispatch (Sum.inl x) clock (firstID + i.val)
    (selectedLabel labels (List.range labels.length) (rows (firstID + i.val)))
  clock := clock
  rows := rows
  nextID := firstID + n

noncomputable def fullUpdate {d m n : ℕ} (s : FullState d m n) (reply : Reply d n) :
    FullState d m n := by
  classical
  exact if s.remaining.isEmpty then s else
    match reply with
    | none => s
    | some (i, id, c, value) =>
      match s.pending i with
      | none => s
      | some job =>
        if id = job.id ∧ s.clock ≤ c then
          let found := s.remaining.find? fun a => decide (s.original[a]? = some job.component)
          let remaining := found.elim s.remaining (fun a => s.remaining.erase a)
          let sum := if found.isSome then s.sum + value else s.sum
          let next := dispatch (Sum.inl s.point) c s.nextID
            (selectedLabel s.original remaining (s.rows s.nextID))
          { s with
            remaining := remaining
            sum := sum
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID + 1 }
        else s

noncomputable def fullResult {d m n : ℕ} (s : FullState d m n) : Space d :=
  (s.original.length : ℝ)⁻¹ • s.sum

def differenceInitial {d m : ℕ} (n S : ℕ) (x y : Space d) (clock : ℝ≥0)
    (rows : ℕ → ChoiceRow) (firstID : ℕ := 0) : DifferenceState d m n where
  target := S
  count := 0
  x := x
  y := y
  sum := 0
  pending := fun i => if S = 0 then none else
    dispatch (Sum.inr (x, y)) clock (firstID + i.val) (labelAt (rows (firstID + i.val)) m)
  clock := clock
  rows := rows
  nextID := firstID + n

noncomputable def differenceUpdate {d m n : ℕ} (s : DifferenceState d m n)
    (reply : Reply d n) : DifferenceState d m n := by
  classical
  exact if s.target ≤ s.count then s else
    match reply with
    | none => s
    | some (i, id, c, value) =>
      match s.pending i with
      | none => s
      | some job =>
        if id = job.id ∧ s.clock ≤ c then
          let next := dispatch (Sum.inr (s.x, s.y)) c s.nextID (labelAt (s.rows s.nextID) m)
          { s with
            count := s.count + 1
            sum := s.sum + value
            pending := Function.update s.pending i next
            clock := c
            nextID := s.nextID + 1 }
        else s

noncomputable def differenceResult {d m n : ℕ} (s : DifferenceState d m n) : Space d :=
  (s.target : ℝ)⁻¹ • s.sum

end LongTails.Algorithms.FreyaCollectors

open MeasureTheory OracleTemplate
open scoped NNReal

namespace LongTails.Algorithms.FreyaPage

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs
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

noncomputable def run (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) :
    ℕ → State q × List ((Fin 1 × Option (Request q.d q.m q.n)) × Reply q.d q.n)
  | 0 => (initial q seed, [])
  | k + 1 =>
      let current := run q O seed ω k
      let reply := O.answer current.2 (query q current.1) (ω current.2.length)
      (update q current.1 reply, current.2 ++ [(query q current.1, reply)])

noncomputable def trace (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ) : State q :=
  (run q O seed ω k).1

noncomputable def replyAt (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (k : ℕ)
    (query : Fin 1 × Option (Request q.d q.m q.n)) : Reply q.d q.n :=
  O.answer (run q O seed ω k).2 query (ω (run q O seed ω k).2.length)

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
        let reply := replyAt q O z.1 z.2 k (query q s)
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
    if after then collectorPendingAfter q s (replyAt q O seed ω call (query q s)) else
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

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Algorithms.FreyaSerial

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs
open LongTails.Algorithms.FreyaRandomness

inductive Phase where
  | full
  | firstDifference
  | secondDifference
  | halted

structure State (q : SerialRaw) where
  seed : Seed q.K
  iteration : ℕ
  x : Space q.d
  previous : Space q.d
  g : Space q.d
  selected : Space q.d
  sum : Space q.d
  first : Space q.d
  component : ℕ
  sample : ℕ
  phase : Phase

noncomputable def initial (q : SerialRaw) (seed : Seed q.K) : State q where
  seed := seed
  iteration := 0
  x := q.x0
  previous := q.x0
  g := 0
  selected := q.x0
  sum := 0
  first := 0
  component := 0
  sample := 0
  phase := if q.m = 0 ∨ q.K = 0 then .halted else .full

noncomputable def advance (q : SerialRaw) (s : State q) : State q :=
  if q.K ≤ s.iteration then { s with phase := .halted } else
    let x := s.x - q.η • s.g
    let batch := s.iteration + 1
    { s with
      iteration := batch
      x := x
      previous := s.x
      selected := if (outputIndex s.seed).val = batch then x else s.selected
      sum := 0
      first := 0
      component := 0
      sample := 0
      phase := if refreshAt s.seed s.iteration then .full else .firstDifference }

def query (q : SerialRaw) (s : State q) : Fin 1 × Option (Fin q.m × Space q.d) :=
  (0, match s.phase with
    | .halted => none
    | .full => if h : s.component < q.m then some (⟨s.component, h⟩, s.x) else none
    | .firstDifference =>
      (labelAt (s.seed.1 s.iteration s.sample) q.m).map fun i => (i, s.x)
    | .secondDifference =>
      (labelAt (s.seed.1 s.iteration s.sample) q.m).map fun i => (i, s.previous))

noncomputable def update (q : SerialRaw) (s : State q) (reply : Space q.d) : State q :=
  match s.phase with
  | .halted => s
  | .full =>
    let total := s.sum + reply
    if s.component + 1 < q.m then { s with sum := total, component := s.component + 1 }
    else advance q { s with g := (q.m : ℝ)⁻¹ • total }
  | .firstDifference => { s with first := reply, phase := .secondDifference }
  | .secondDifference =>
    let total := s.sum + (s.first - reply)
    if s.sample + 1 < q.S then
      { s with sum := total, sample := s.sample + 1, phase := .firstDifference }
    else advance q { s with g := s.g + (q.S : ℝ)⁻¹ • total }

def output (q : SerialRaw) (s : State q) : Space q.d := s.selected

noncomputable def algorithm (q : SerialRaw) :
    Algorithm (Option (Fin q.m × Space q.d)) (Space q.d) (Space q.d) 1 where
  Seed := Seed q.K
  law := seedLaw q.ρ q.K
  State := State q
  initial := initial q
  query := query q
  update := update q
  output := output q

abbrev CanonicalSeed (q : SerialRaw) :=
  (Fin q.K → Bool) × (Fin q.K → Fin q.S → Option (Fin q.m)) × Fin (max 1 q.K)

noncomputable def componentLaw (m : ℕ) : ProbabilityMeasure (Option (Fin m)) := by
  classical
  by_cases h : 0 < m
  · haveI : NeZero m := ⟨by omega⟩
    exact ⟨((PMF.uniformOfFintype (Fin m)).map some).toMeasure, inferInstance⟩
  · exact ⟨Measure.dirac none, inferInstance⟩

noncomputable def canonicalLaw (q : SerialRaw) : ProbabilityMeasure (CanonicalSeed q) := by
  haveI : NeZero (max 1 q.K) := ⟨by omega⟩
  let p : unitInterval := Set.projIcc 0 1 zero_le_one q.ρ
  exact ⟨(Measure.pi (fun _ : Fin q.K => bernoulliMeasure true false p)).prod
    ((Measure.pi (fun _ : Fin q.K =>
      Measure.pi (fun _ : Fin q.S => (componentLaw q.m : Measure (Option (Fin q.m)))))).prod
      (PMF.uniformOfFintype (Fin (max 1 q.K))).toMeasure), inferInstance⟩

noncomputable def idealTrace (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) : ℕ → Space q.d × Space q.d
  | 0 => (q.x0, gradient (objective f) q.x0)
  | k + 1 =>
    let previous := idealTrace q f z k
    if h : k < q.K then
      let x := previous.1 - q.η • previous.2
      let g := if z.1 ⟨k, h⟩ then gradient (objective f) x else
        previous.2 + (q.S : ℝ)⁻¹ • ∑ j : Fin q.S,
          match z.2.1 ⟨k, h⟩ j with
          | none => 0
          | some i => gradient (f i) x - gradient (f i) previous.1
      (x, g)
    else previous

noncomputable def idealOutput (q : SerialRaw) (f : Fin q.m → Space q.d → ℝ)
    (z : CanonicalSeed q) : Space q.d :=
  (idealTrace q f z z.2.2.val).1

end LongTails.Algorithms.FreyaSerial

open OracleTemplate
open scoped ENNReal NNReal

namespace LongTails.Algorithms.FreyaTuning

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs

noncomputable def familyCoefficient (p : Base) (S : ℕ) (ρ : ℝ) : ℝ :=
  p.Lminus + p.Lpm * Real.sqrt ((1 - ρ) / (ρ * S))

noncomputable def familyStep (p : Base) (S : ℕ) (ρ : ℝ) : ℝ :=
  1 / familyCoefficient p S ρ

noncomputable def familyHorizon (p : Base) (S : ℕ) (ρ : ℝ) : ℕ :=
  max 1 ⌈2 * p.Δ * familyCoefficient p S ρ / p.ε⌉₊

noncomputable def simpleBatch (p : Simple) : ℕ := ⌈Real.sqrt p.m⌉₊

noncomputable def simpleProbability (p : Simple) : ℝ := 1 / Real.sqrt p.m

noncomputable def simpleStep (p : Simple) : ℝ :=
  familyStep p.toWorkers.toBase (simpleBatch p) (simpleProbability p)

noncomputable def simpleHorizon (p : Simple) : ℕ :=
  familyHorizon p.toWorkers.toBase (simpleBatch p) (simpleProbability p)

noncomputable def batchObjective (p : Optimized) (S : ℕ) : ℝ≥0∞ :=
  min (ENNReal.ofReal p.Lminus * equilibriumTime p.τ p.m)
    (ENNReal.ofReal p.Lminus * equilibriumTime p.τ S + ENNReal.ofReal p.Lpm *
      ((equilibriumTime p.τ p.m * equilibriumTime p.τ S / S) ^ (1 / (2 : ℝ))))

noncomputable def optimizedBatch (p : Optimized) : ℕ :=
  (List.minOn? (batchObjective p) (List.range' 1 p.m)).getD 1

noncomputable def optimizedProbability (p : Optimized) : ℝ :=
  let S := optimizedBatch p
  let tm := equilibriumTime p.τ p.m
  let ts := equilibriumTime p.τ S
  if tm = 0 ∨ tm = ⊤ then 1 else
    if ENNReal.ofReal p.Lminus * tm ≤ ENNReal.ofReal p.Lminus * ts +
        ENNReal.ofReal p.Lpm * ((tm * ts / S) ^ (1 / (2 : ℝ))) then 1
    else (ts / tm).toReal

noncomputable def optimizedStep (p : Optimized) : ℝ :=
  familyStep p.toWorkers.toBase (optimizedBatch p) (optimizedProbability p)

noncomputable def optimizedHorizon (p : Optimized) : ℕ :=
  familyHorizon p.toWorkers.toBase (optimizedBatch p) (optimizedProbability p)

noncomputable def constantPoint {Query Reply Output : Type} (idle : Query) (x : Output) :
    Algorithm Query Reply Output 1 where
  State := Unit
  initial := fun _ => ()
  query := fun _ => (0, idle)
  update := fun _ _ => ()
  output := fun _ => x

noncomputable def serial (p : Serial) :
    Algorithm (Option (Fin p.m × Space p.d)) (Space p.d) (Space p.d) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none p.x0 else
    FreyaSerial.algorithm
      { d := p.d, m := p.m, x0 := p.x0,
        η := familyStep p.toBase p.S p.ρ,
        S := p.S, ρ := p.ρ, K := familyHorizon p.toBase p.S p.ρ }

noncomputable def familyRaw (p : Family) (usePrefix : Bool) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := familyStep p.toWorkers.toBase p.S p.ρ
  S := p.S
  ρ := p.ρ
  K := familyHorizon p.toWorkers.toBase p.S p.ρ
  «prefix» := usePrefix

noncomputable def iterations (p : Family) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none p.x0 else
    FreyaPage.pointOnly (familyRaw p false)

noncomputable def freeTime (p : Family) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.«prefix» (familyRaw p true)

noncomputable def optimizedRaw (p : Optimized) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := optimizedStep p
  S := optimizedBatch p
  ρ := optimizedProbability p
  K := optimizedHorizon p
  «prefix» := false

noncomputable def optimized (p : Optimized) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.literal (optimizedRaw p)

noncomputable def simpleRaw (p : Simple) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := simpleStep p
  S := simpleBatch p
  ρ := simpleProbability p
  K := simpleHorizon p
  «prefix» := false

noncomputable def simple (p : Simple) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.literal (simpleRaw p)

end LongTails.Algorithms.FreyaTuning

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Setups.FreyaPageUniform

open LongTails.Setups.FreyaModel

structure Params where
  d : ℕ
  m : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d
  S : ℕ
  ρ : ℝ
  Lplus : ℝ
  lower : ℝ

def publicInput (p : Params) : LongTails.Algorithms.FreyaInputs.Serial where
  d := p.d
  m := p.m
  Lminus := p.Lminus
  Lpm := p.Lpm
  Δ := p.Δ
  ε := p.ε
  x0 := p.x0
  S := p.S
  ρ := p.ρ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := LongTails.Algorithms.FreyaInputs.Serial
  Instance p := Fin p.m → Space p.d → ℝ
  Query p := Option (Fin p.m × Space p.d)
  Reply p := Space p.d
  Output p := Space p.d
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 ≤ p.Lminus ∧ 0 ≤ p.Lplus ∧ 0 ≤ p.Lpm ∧
    0 ≤ p.Δ ∧ 0 < p.ε ∧
    0 < p.S ∧ 0 < p.ρ ∧ p.ρ ≤ 1
  admissible p f O :=
    (∀ i, Differentiable ℝ (f i)) ∧
    (∀ x, p.lower ≤ objective f x) ∧
    objective f p.x0 - p.lower ≤ p.Δ ∧
    (∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤
      p.Lminus * ‖x - y‖) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lplus ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) -
      ‖gradient (objective f) x - gradient (objective f) y‖ ^ 2 ≤
      p.Lpm ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ k, Measurable (fun z : (HistoryAt (Option (Fin p.m × Space p.d)) (Space p.d) k ×
      (Fin 1 × Option (Fin p.m × Space p.d))) × O.Seed k => answerAt O k z.1.1 z.1.2 z.2)) ∧
    ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)),
      ∀ history : List ((Fin 1 × Option (Fin p.m × Space p.d)) × Space p.d),
      O.answer history (0, none) (ω history.length) = 0 ∧
      ∀ i x, O.answer history (0, some (i, x)) (ω history.length) = gradient (f i) x
  successful p f output P :=
    Integrable (fun ω => ‖gradient (objective f) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = LongTails.Algorithms.FreyaTuning.serial q

end LongTails.Setups.FreyaPageUniform
