import LongTails.Setups.BirchNonEuclidean

namespace LongTails.Setups.BirchCollections

open OracleTemplate
open OracleTemplate.Rennala (Point Instance)

inductive Event where
  | capture (worker source size : ℕ) (refresh movement : ℝ)
  | issue (collection worker : ℕ)
  | receive (raw : ℕ)
  | finish (collection : ℕ)
  | merge (worker left right common : ℕ)
  | mark (source : ℕ)
  | discard (raw : ℕ)
  | cancel (collection : ℕ)

structure StateRecord where
  owner : ℕ := 0
  history : Finset ℕ := ∅

structure Collection where
  owner : ℕ := 0
  source : ℕ := 0
  size : ℕ := 1
  refresh : ℝ := 1
  movement : ℝ := 1
  delivered : List ℕ := []
  closed : Bool := false

structure RawRecord where
  collection : ℕ := 0
  worker : ℕ := 0

structure Direction where
  collection : ℕ := 0
  source : ℕ := 0
  target : ℕ := 0
  history : Finset ℕ := ∅
  refresh : ℝ := 1
  movement : ℝ := 1
  raw : List ℕ := []

structure TraceState where
  states : ℕ → StateRecord := fun _ => {}
  nextState : ℕ := 1
  collections : ℕ → Collection := fun _ => {}
  nextCollection : ℕ := 0
  raws : ℕ → RawRecord := fun _ => {}
  nextRaw : ℕ := 0
  retired : Finset ℕ := ∅
  directions : ℕ → Direction := fun _ => {}
  nextDirection : ℕ := 0
  markers : List ℕ := [0]

def step (s : TraceState) : Event → TraceState
  | .capture worker source size refresh movement =>
      { s with
        collections := Function.update s.collections s.nextCollection
          { owner := worker, source, size, refresh, movement }
        nextCollection := s.nextCollection + 1 }
  | .issue collection worker =>
      { s with
        raws := Function.update s.raws s.nextRaw { collection, worker }
        nextRaw := s.nextRaw + 1 }
  | .receive raw =>
      let c := (s.raws raw).collection
      { s with
        collections := Function.update s.collections c
          { s.collections c with delivered := (s.collections c).delivered ++ [raw] }
        retired := insert raw s.retired }
  | .finish collection =>
      let c := s.collections collection
      let h := (s.states c.source).history
      { s with
        states := Function.update s.states s.nextState
          { owner := c.owner, history := insert s.nextDirection h }
        nextState := s.nextState + 1
        collections := Function.update s.collections collection { c with closed := true }
        directions := Function.update s.directions s.nextDirection
          { collection, source := c.source, target := s.nextState, history := h,
            refresh := c.refresh, movement := c.movement, raw := c.delivered }
        nextDirection := s.nextDirection + 1 }
  | .merge worker left right _ =>
      { s with
        states := Function.update s.states s.nextState
          { owner := worker, history := (s.states left).history ∪ (s.states right).history }
        nextState := s.nextState + 1 }
  | .mark source => { s with markers := s.markers ++ [source] }
  | .discard raw => { s with retired := insert raw s.retired }
  | .cancel collection =>
      { s with
        collections := Function.update s.collections collection
          ({ s.collections collection with closed := true } : Collection) }

def Event.Valid (workers : ℕ) (s : TraceState) : Event → Prop
  | .capture worker source size refresh movement =>
      worker < workers ∧ source < s.nextState ∧ 0 < size ∧
        0 ≤ movement ∧ movement ≤ refresh ∧ refresh ≤ 1
  | .issue collection worker =>
      collection < s.nextCollection ∧ worker < workers ∧
        (s.collections collection).closed = false
  | .receive raw =>
      raw < s.nextRaw ∧ raw ∉ s.retired ∧
        (s.collections (s.raws raw).collection).closed = false
  | .finish collection =>
      collection < s.nextCollection ∧ (s.collections collection).closed = false ∧
        (s.collections collection).delivered.length = (s.collections collection).size
  | .merge worker left right common =>
      worker < workers ∧ left < s.nextState ∧ right < s.nextState ∧ common < s.nextState ∧
        (s.states common).history = (s.states left).history ∩ (s.states right).history
  | .mark source => source < s.nextState ∧
      (s.states (s.markers.getLast?.getD 0)).history ⊆ (s.states source).history
  | .discard raw => raw < s.nextRaw ∧ raw ∉ s.retired
  | .cancel collection => collection < s.nextCollection ∧
      (s.collections collection).closed = false

def ValidFrom (workers : ℕ) : TraceState → List Event → Prop
  | _, [] => True
  | s, e :: rest => e.Valid workers s ∧ ValidFrom workers (step s e) rest

def run (events : List Event) : TraceState := events.foldl step {}

def Event.calls : Event → ℕ
  | .issue _ _ => 1
  | _ => 0

def calls (events : List Event) : ℕ := (events.map Event.calls).sum

structure Ordering where
  labels : List ℕ
  cut : ℕ → ℕ
  frontier : ℕ → ℕ
  anchor : ℕ → ℕ
  scale : ℕ → ℕ → ℝ
  renewalFrontier : ℕ → ℕ → ℕ

def Ordering.label (o : Ordering) (n : ℕ) : ℕ := o.labels[n]?.getD 0

def Ordering.history (o : Ordering) (s : TraceState) (n : ℕ) : Finset ℕ :=
  if n < o.labels.length then
    (Finset.range o.labels.length).filter (fun j => o.label j ∈ (s.directions (o.label n)).history)
  else Finset.range n

def Ordering.refresh (o : Ordering) (s : TraceState) (n : ℕ) : ℝ :=
  if n < o.labels.length then (s.directions (o.label n)).refresh else 0

def Ordering.movement (o : Ordering) (s : TraceState) (n : ℕ) : ℝ :=
  if n < o.labels.length then (s.directions (o.label n)).movement else 0

def Ordering.raw (o : Ordering) (s : TraceState) (n : ℕ) : Finset ℕ :=
  (s.directions (o.label n)).raw.toFinset

def Ordering.Valid (o : Ordering) (s : TraceState) (K : ℕ) : Prop :=
  0 < o.labels.length ∧ o.labels.Nodup ∧ s.markers.length = K + 1 ∧
    o.cut 0 = 0 ∧ o.cut K = o.labels.length ∧
    (∀ k, k < K → o.cut k < o.cut (k + 1)) ∧
    (∀ n, n < o.labels.length → o.label n < s.nextDirection) ∧
    (∀ k, k ≤ K → (s.states (s.markers[k]?.getD 0)).history =
      (Finset.range (o.cut k)).image o.label) ∧
    (∀ n, o.history s n ⊆ Finset.range n)

structure Controls where
  lowerMass : ℝ
  upperMass : ℝ
  massRatio : ℝ
  amplification : ℝ
  initialization : ℕ
  waste : ℕ

def Controls.Valid (c : Controls) : Prop :=
  0 < c.lowerMass ∧ c.lowerMass ≤ c.upperMass ∧ c.upperMass ≤ 1 ∧
    c.upperMass ≤ c.massRatio * c.lowerMass ∧ 0 < c.amplification

def Structural (s : TraceState) (o : Ordering) (c : Controls) (K B : ℕ) : Prop :=
  o.Valid s K ∧ c.Valid ∧ o.refresh s 0 = 1 ∧
    (∀ n, n < o.labels.length → o.frontier n ≤ n ∧
      Finset.range (o.frontier n) ⊆ o.history s n ∧
      (∑ j ∈ Finset.Ico (o.frontier n) n, o.movement s j) ≤ 1 / 4) ∧
    (∀ k, k < K → c.lowerMass ≤
      ∑ j ∈ Finset.Ico (o.cut k) (o.cut (k + 1)), o.movement s j) ∧
    (∀ k, k < K →
      (∑ j ∈ Finset.Ico (o.cut k) (o.cut (k + 1)), o.movement s j) ≤ c.upperMass) ∧
    (∀ n, n < o.labels.length → o.refresh s n * B ≤ (o.raw s n).card) ∧
    (∀ n, n < o.labels.length → (n = 0 ∧ o.movement s n = 0 ∧
      (o.raw s n).card ≤ c.initialization) ∨
      (o.raw s n).card ≤ (B : ℝ) * c.amplification * o.movement s n) ∧
    s.nextRaw - ((Finset.range o.labels.length).biUnion (o.raw s)).card ≤ c.waste ∧
    (∀ n, n < o.labels.length →
      let r := o.anchor n
      r ≤ n ∧ o.refresh s r = 1 ∧
        (r < n → o.history s r = Finset.range r) ∧
        (∀ j, 0 < j → j ≤ n - r → Finset.range (r + 1) ⊆ o.history s (r + j)) ∧
        (∀ j, j ≤ n - r → 1 ≤ o.scale n j ∧ o.scale n j ≤ 2 ∧
          0 ≤ 1 - o.refresh s (r + j) * o.scale n j ∧
          o.renewalFrontier n j ≤ j ∧
          (∀ i, i < o.renewalFrontier n j → r + i ∈ o.history s (r + j)) ∧
          1 ≤ o.scale n j * ∏ i ∈ Finset.range (j - o.renewalFrontier n j),
            (1 - o.refresh s (r + (o.renewalFrontier n j + i)) *
              o.scale n (o.renewalFrontier n j + i))))

structure Params where
  d : ℕ
  N : Seminorm ℝ (Point d)
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  workers : ℕ
  κ : ℝ
  controls : Controls
  events : List Event
  ordering : Ordering

def native (p : Params) : BirchNonEuclidean.Params where
  d := p.d
  N := p.N
  L := p.L
  σ := p.σ
  ε := p.ε
  Δ := p.Δ
  x0 := p.x0
  workers := p.workers
  κ := p.κ
  protocol := ⟨fun _ _ => ⟨[], 0, 0, fun _ => 0⟩⟩
  profile := ⟨1, 0, 0, 0, 0⟩
  callCount := fun _ _ => 0

noncomputable def batchSize (p : Params) : ℕ :=
  1 + ⌈32 * p.controls.massRatio * p.κ * p.σ ^ 2 / p.ε⌉₊

noncomputable def horizon (p : Params) : ℕ :=
  1 + ⌈240 * p.L * p.Δ / (p.controls.lowerMass * p.ε)⌉₊

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput p := p
  valid p := (∀ x, p.N x = 0 → x = 0) ∧ Continuous p.N ∧
    0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 < p.workers ∧
    BirchNonEuclidean.DualRegular p.N p.κ ∧ ValidFrom p.workers {} p.events ∧
      Structural (run p.events) p.ordering p.controls (horizon p) (batchSize p)
  admissible p I O := BirchNonEuclidean.spec.admissible (native p) I O
  successful p I output P := BirchNonEuclidean.spec.successful (native p) I output P

end LongTails.Setups.BirchCollections
