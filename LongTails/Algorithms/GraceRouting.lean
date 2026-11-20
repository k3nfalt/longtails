import LongTails.Algorithms.GraceGraph
import LongTails.Algorithms.GraceTree
import LongTails.Algorithms.GracePacket
import LongTails.Algorithms.LeonProtocol

namespace LongTails.Algorithms.GraceRouting

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceTree
open LongTails.Algorithms.GracePacket
open LongTails.Algorithms.LeonProtocol (Program)

structure Routes (p : Params) (S : Finset (Fin p.n)) (r : Fin p.n) where
  P : ℕ+
  tree : Fin P → Tree p S r

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}

def Routes.height (A : Routes p S r) :=
  Finset.univ.sup fun a => (A.tree a).nodes.sup (A.tree a).depth

def Routes.lane (A : Routes p S r) (x : ℕ) : Fin A.P := ⟨x % A.P, Nat.mod_lt _ A.P.pos⟩

def Routes.route (A : Routes p S r) (x : ℕ) := A.tree (A.lane x)

def Routes.linkLanes (A : Routes p S r) (i j : Fin p.n) :=
  Finset.univ.filter fun a =>
    (i ∈ (A.tree a).nodes ∧ i ≠ r ∧ (A.tree a).parent i = j) ∨
      (j ∈ (A.tree a).nodes ∧ j ≠ r ∧ (A.tree a).parent j = i)

inductive Phase | reduce | broadcast
deriving DecidableEq

def source (phase : Phase) (i j : Fin p.n) :=
  match phase with | .reduce => i | .broadcast => j

def target (phase : Phase) (i j : Fin p.n) :=
  match phase with | .reduce => j | .broadcast => i

def Routes.slot (A : Routes p S r) (phase : Phase) (x : ℕ) (v : Fin p.n) :=
  x / A.P + match phase with
    | .reduce => A.height - (A.route x).depth v
    | .broadcast => (A.route x).depth v - 1

def Routes.sends (A : Routes p S r) (phase : Phase) (k x : ℕ) (i j : Fin p.n) : Bool :=
  let T := A.route x
  let v := source (p := p) phase i j
  decide (v ∈ T.nodes ∧ v ≠ r ∧ T.parent v = target (p := p) phase i j ∧
    A.slot phase x v = k)

def Routes.items (A : Routes p S r) (D : ℕ) (phase : Phase) (k : ℕ) (i j : Fin p.n) :=
  (List.range D).filter fun x => A.sends phase k x i j

def Routes.slots (A : Routes p S r) (D : ℕ) := D / A.P + 1 + A.height

noncomputable def Routes.frameTime (A : Routes p S r) (q : ℕ) : DistributedTemplate.Time :=
  Finset.univ.sup fun e : GraceGraph.Link p =>
    ((q + DistributedTemplate.clockBits : ℕ) : DistributedTemplate.Time) *
      (A.linkLanes e.val.1 e.val.2).card / GraceGraph.capacity p e

abbrev Values := ℕ → ℕ

noncomputable def pack (q : ℕ) (xs : List ℕ) (values : Values) :=
  xs.flatMap fun x => word q (values x)

noncomputable def unpack (phase : Phase) (q : ℕ) : List ℕ → List Bool → Values → Values
  | [], _, values => values
  | x :: xs, bits, values =>
    let v := readWord q bits
    let u := match phase with | .reduce => values x + v | .broadcast => v
    unpack phase q xs (bits.drop q) (Function.update values x u)

noncomputable def Routes.sendFrame (A : Routes p S r) (D q : ℕ) (phase : Phase)
    (k : ℕ) (i : Fin p.n) (values : Values) (next : Program p.base) : List (Fin p.n) → Program p.base
  | [] => next
  | j :: rest =>
    let xs := A.items D phase k i j
    let tail := A.sendFrame D q phase k i values next rest
    if xs.isEmpty then .send i [] tail else .send j (pack q xs values) tail

noncomputable def Routes.receiveFrame (A : Routes p S r) (D q : ℕ) (phase : Phase)
    (k : ℕ) (i : Fin p.n) (next : Values → Program p.base) : List (Fin p.n) → Values → Program p.base
  | [], values => next values
  | j :: rest, values =>
    let xs := A.items D phase k j i
    if xs.isEmpty then .send i [] (A.receiveFrame D q phase k i next rest values)
    else .receive j (fun bits => A.receiveFrame D q phase k i next rest (unpack phase q xs bits values))

noncomputable def Routes.frames (A : Routes p S r) (D q : ℕ) (phase : Phase) (i : Fin p.n)
    (next : Values → Program p.base) : List ℕ → Values → Program p.base
  | [], values => next values
  | k :: rest, values =>
    A.sendFrame D q phase k i values
      (A.receiveFrame D q phase k i (A.frames D q phase i next rest) (List.finRange p.n) values)
      (List.finRange p.n)

end LongTails.Algorithms.GraceRouting
