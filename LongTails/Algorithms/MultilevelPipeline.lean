import LongTails.Algorithms.MultilevelTransport
import LongTails.Algorithms.DistributedQuantization
import LongTails.Algorithms.NormalizedStorm
import LongTails.Algorithms.Clipping

namespace LongTails.Algorithms.MultilevelPipeline

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open MultilevelWorkerSchedule
open MultilevelTransport (Bits Script Selection)
open DistributedQuantization (message receive)

noncomputable def precision (p : Params) : ℝ := p.ε / 512
noncomputable def stride (p : Params) : ℝ := precision p / p.L

noncomputable def radiusUnits (p : Params) : ℕ :=
  4 * (wanted p + 2) + 32 * (height p + 1) * (fullBatch p + 4 ^ height p + 1)

noncomputable def width (p : Params) : ℕ :=
  14 + 4 * Nat.log2 (2 + p.d + wanted p + fullBatch p)

noncomputable def pointSpacing (p : Params) : ℝ := stride p / (p.d + 1)
noncomputable def valueSpacing (p : Params) : ℝ := precision p / ((height p + 1 : ℕ) * (p.d + 1 : ℕ))

noncomputable def physical (p : Params) : Params :=
  {p with h := fun i => 2 * p.h i + 2 * p.l + p.b * (129 + 3 * p.d * width p : ℕ)}

noncomputable def warmTime (p : Params) : Time := 2 * batchDuration (physical p) (fullBatch p)
noncomputable def period (p : Params) : Time := tickDuration (physical p) (height p) (fullBatch p)
noncomputable def duration (p : Params) : Time := warmTime p + wanted p * period p

abbrev Job := Option (ℕ × ℕ)
abbrev Entry (p : Params) := Job × Slot (physical p)

noncomputable def cells (p : Params) : Finset Job :=
  insert none ((((Finset.range (height p + 1)).product (Finset.range (wanted p))).filter
    (fun js => (js.2+1) * 2^js.1 ≤ wanted p)).image some)

noncomputable def reservations (p : Params) : Job → Finset (Slot (physical p))
  | none => reserve (available (physical p) 0 (warmTime p)) (fullBatch p)
  | some (j,s) =>
      (allocation (window (physical p) (warmTime p) (period p))
        (multilevelBatch (height p) (fullBatch p)) j s).2

noncomputable def start (p : Params) (e : Entry p) : Time := e.2.2 * (physical p).h e.2.1
noncomputable def finish (p : Params) (e : Entry p) : Time := (e.2.2+1 : ℕ) * (physical p).h e.2.1

noncomputable def table (p : Params) : List (Entry p) :=
  ((cells p).biUnion (fun job => (reservations p job).image (Prod.mk job))).toList.mergeSort
    (fun a b => decide (start p a ≤ start p b))

noncomputable def entry (p : Params) (k : ℕ) : Entry p := ((table p)[k]?).getD (none, ⟨0,0⟩)

noncomputable def average (p : Params) (bits : ℕ → Bits) (job : Job) : Point p :=
  let slots := reservations p job
  (slots.card : ℝ)⁻¹ • ∑ s ∈ slots, receive p.d (width p) (valueSpacing p)
    (bits ((table p).idxOf (job,s)))

def activeJob (j k : ℕ) : Job := some (j,k / 2^j - 1)

noncomputable def estimate (p : Params) (bits : ℕ → Bits) (k : ℕ) : Point p :=
  average p bits (if 2^(height p) ≤ k then activeJob (height p) k else none) +
    ∑ j ∈ Finset.range (height p), if 2^j ≤ k then average p bits (activeJob j k) else 0

noncomputable def iterate (p : Params) (bits : ℕ → Bits) : ℕ → Point p
  | 0 => p.x0
  | k+1 => OracleTemplate.NormalizedStorm.stormStep (stride p) (iterate p bits k) (estimate p bits k)

noncomputable def queryBits (p : Params) (bits : ℕ → Bits) (job : Job) : Bits :=
  let (snapshot, k, parent) := match job with
    | none => (true, 0, 0)
    | some (j,s) => (decide (j = height p), s * 2^j, parentAtRelease (2^j) s)
  snapshot :: (message p.d (width p) (pointSpacing p) (iterate p bits k - p.x0) ++
    message p.d (width p) (pointSpacing p) (iterate p bits parent - p.x0))

noncomputable def decode (p : Params) (bs : Bits) : Query p :=
  let read := fun payload => p.x0 + receive p.d (width p) (pointSpacing p) payload
  (read (bs.tail.take (p.d * width p)), read (bs.tail.drop (p.d * width p)))

noncomputable def encode (p : Params) (bs : Bits) (values : Query p) : Bits :=
  let raw := if bs.head? = some true then values.1 else values.1 - values.2
  message p.d (width p) (valueSpacing p) (OracleTemplate.clip (radiusUnits p * precision p) raw)

noncomputable def output (p : Params) (seed : Selection p) (bits : ℕ → Bits) : Point p :=
  iterate p bits (if ‖estimate p bits seed.1‖ ≤ ‖estimate p bits seed.2‖ then seed.1 else seed.2)

noncomputable def script (p : Params) : Script p where
  count := (table p).length
  worker k := (entry p k).2.1
  start k := start p (entry p k)
  finish k := finish p (entry p k)
  request k bits := queryBits p bits (entry p k).1
  decode := decode p
  encode := encode p
  output := output p

noncomputable def algorithm (p : Params) (T : Time) := MultilevelTransport.algorithm p (script p) T

end LongTails.Algorithms.MultilevelPipeline
