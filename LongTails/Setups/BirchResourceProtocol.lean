import LongTails.Setups.BirchCollectionExecutionModel

namespace LongTails.Algorithms.BirchResourceNative

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionBatches

structure Plan where
  cut : ℕ → ℕ
  phase : ℕ → ℕ
  parent : ℕ → Option ℕ
  accepted : ℕ → ℕ
  paid : ℕ → ℕ

def Plan.source (p : Plan) (n : ℕ) : ℕ :=
  match p.parent n with
  | none => 2 * p.cut (p.phase n)
  | some j => 2 * j + 1

noncomputable def refresh (B n b : ℕ) : ℝ := if n = 0 then 1 else (b : ℝ) / (8 * B)

noncomputable def movement (B n b : ℕ) : ℝ := if n = 0 then 1 / 8 else (b : ℝ) / (8 * B)

def discardReplies (collection : ℕ) : TraceState → ℕ → List Event
  | _, 0 => []
  | s, k + 1 =>
      let e := Event.issue collection 0
      let d := Event.discard s.nextRaw
      e :: d :: discardReplies collection (step (step s e) d) k

noncomputable def packetCode (s : TraceState) (source b waste : ℕ) (β w : ℝ) : List Event :=
  let cap := Event.capture 0 source b β w
  let t := step s cap
  let accepted := batchReplies s.nextCollection t (List.replicate b 0)
  let u := accepted.foldl step t
  cap :: (accepted ++ (discardReplies s.nextCollection u waste ++
    [.finish s.nextCollection, .merge 0 (s.nextState - 1) s.nextState source]))

noncomputable def doPacket (p : Plan) (B : ℕ) (events : List Event) (n : ℕ) : List Event :=
  let b := p.accepted n
  events ++ packetCode (run events) (p.source n) b (p.paid n - b) (refresh B n b) (movement B n b)

noncomputable def code (p : Plan) (B : ℕ) : ℕ → List Event
  | 0 => []
  | k + 1 =>
      let es := (List.range' (p.cut k) (p.cut (k + 1) - p.cut k)).foldl (doPacket p B) (code p B k)
      es ++ [.mark (2 * p.cut (k + 1))]

def ordering (p : Plan) (K : ℕ) : LongTails.Setups.BirchCollections.Ordering where
  labels := List.range (p.cut K)
  cut := p.cut
  frontier n := p.cut (p.phase n)
  anchor _ := 0
  scale _ j := if j = 0 then 1 else 2
  renewalFrontier _ j := p.cut (p.phase j)

noncomputable def controls (D : ℕ) : Controls :=
  ⟨1 / 8, 1 / 8, 1, 8, 0, D⟩

structure Layout (Q : ℕ) where
  accepted : Fin Q → ℕ
  paid : Fin Q → ℕ
  parent : Fin Q → Option (Fin Q)

structure Layout.Valid {Q : ℕ} (p : Layout Q) (B : ℕ) : Prop where
  count : ∀ i, 0 < p.accepted i ∧ p.accepted i ≤ p.paid i
  quota : ∑ i, p.accepted i = B
  earlier : ∀ i j, p.parent i = some j → j.val < i.val

def offset (Q n : ℕ) : ℕ := 1 + (n - 1) / Q * Q

def slot {Q : ℕ} (hQ : 0 < Q) (n : ℕ) : Fin Q := ⟨(n - 1) % Q, Nat.mod_lt _ hQ⟩

def plan {Q : ℕ} (p : Layout Q) (hQ : 0 < Q) (B : ℕ) : Plan where
  cut k := if k = 0 then 0 else 1 + (k - 1) * Q
  phase n := if n = 0 then 0 else 1 + (n - 1) / Q
  parent n := if n = 0 then none else (p.parent (slot hQ n)).map (fun j => offset Q n + j.val)
  accepted n := if n = 0 then B else p.accepted (slot hQ n)
  paid n := if n = 0 then ∑ i, p.paid i else p.paid (slot hQ n)

noncomputable def tuned (p : Params) : Params := {p with workers := 1, controls := controls 0}

noncomputable def compiledParams {Q : ℕ} (p : Params) (l : Layout Q) (hQ : 0 < Q) : Params :=
  let q := tuned p
  let B := batchSize q
  let K := horizon q
  let a := plan l hQ B
  {q with
    controls := controls (K * ((∑ i, l.paid i) - B))
    events := code a B K
    ordering := ordering a K}

structure GeometryValid (p : Params) : Prop where
  definite : ∀ x, p.N x = 0 → x = 0
  continuous : Continuous p.N
  Lpos : 0 < p.L
  σnonneg : 0 ≤ p.σ
  εpos : 0 < p.ε
  Δnonneg : 0 ≤ p.Δ
  regular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ


def clocked {Q R O : Type} (a : OracleTemplate.Algorithm Q R O) (T : ℝ) :
    OracleTemplate.Algorithm Q R (O × ℝ) where
  Seed := a.Seed
  law := a.law
  State := a.State
  initial := a.initial
  query := a.query
  update := a.update
  output s := (a.output s, T)

end LongTails.Algorithms.BirchResourceNative
