import LongTails.Algorithms.GuardedMetricAcceleration
import LongTails.Algorithms.QueryPlan
import LongTails.Setups.GradientOnlyThirdOrderNonconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.GradientOnlyGuarded

open OracleTemplate GuardedMetricAcceleration
open scoped RealInnerProductSpace

noncomputable section

section Quadrature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def node (a b : E) (m i : ℕ) (s : ℝ) : E :=
  a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a) + (s / Real.sqrt 3) • ((1 / (2 * (m : ℝ))) • (b - a))

def pieceValue (g : E → E) (a b : E) (m i : ℕ) : ℝ :=
  ⟪g (node a b m i 1) + g (node a b m i (-1)), (1 / (2 * (m : ℝ))) • (b - a)⟫

def surrogate (g : E → E) (a b : E) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, pieceValue g a b m i

def nodes (a b : E) (m : ℕ) : Fin m × Fin 2 → E :=
  fun j => node a b m j.1 (if j.2 = 0 then 1 else -1)

def surrogateOf (r : Fin m × Fin 2 → E) (a b : E) : ℝ :=
  ∑ i : Fin m, ⟪r (i, 0) + r (i, 1), (1 / (2 * (m : ℝ))) • (b - a)⟫

end Quadrature

section Agd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Tuning where
  α : ℝ
  L : ℝ
  μ : ℝ
  a : ℝ
  R : ℝ
  η : ℝ
  q : ℝ
  τ : ℝ
  ε : ℝ
  m : ℕ
  N : ℕ

def regGrad (α : ℝ) (c y gy : E) : E := gy + (2 * α) • (y - c)

def advance (t : Tuning) (g : E → E) (c : E) (s : E × E) : E × E :=
  let y := extrapolate t.a s.1 s.2
  let G := regGrad t.α c y (g y)
  (gradientStep t.L y G, centerStep t.a t.μ y s.2 G)

def agd (t : Tuning) (g : E → E) (c : E) (k : ℕ) : E × E := (advance t g c)^[min k t.N] (c, c)

def xs (t : Tuning) (g : E → E) (c : E) (k : ℕ) : E := (agd t g c k).1

def zs (t : Tuning) (g : E → E) (c : E) (k : ℕ) : E := (agd t g c k).2

def ys (t : Tuning) (g : E → E) (c : E) (k : ℕ) : E := extrapolate t.a (xs t g c k) (zs t g c k)

def previous (t : Tuning) (g : E → E) (c : E) (k : ℕ) : E := xs t g c (k - 1)

end Agd

section Decision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
def firstTrue (P : ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if firstTrue P n < n then firstTrue P n else if P n then n else n + 1

def pairValue (t : Tuning) (c u v G : E) (r : Fin t.m × Fin 2 → E) : ℝ :=
  surrogateOf r v u + t.α * (‖u - c‖ ^ 2 - ‖v - c‖ ^ 2) - ⟪G, u - v⟫

def passes (t : Tuning) (c u v G : E) (r : Fin t.m × Fin 2 → E) : Prop :=
  (t.μ / 2 + t.τ) * ‖u - v‖ ^ 2 ≤ pairValue t c u v G r

def stateX (states : ℕ → E × E) (k : ℕ) : E := (states k).1

def stateY (t : Tuning) (states : ℕ → E × E) (k : ℕ) : E :=
  extrapolate t.a (states k).1 (states k).2

def stateG (t : Tuning) (states : ℕ → E × E) (k : ℕ) : E :=
  t.L • (stateY t states k - stateX states (k + 1))

def exitIndex (t : Tuning) (c : E) (states : ℕ → E × E) : ℕ :=
  firstTrue (fun k => t.R < ‖stateX states k - c‖) (t.N + 1)

def horizonIndex (t : Tuning) (c : E) (states : ℕ → E × E) : ℕ := min (exitIndex t c states) t.N

def pairsA (t : Tuning) (c : E) (states : ℕ → E × E) : Fin t.N × Fin 2 → E × E :=
  fun j => (if j.2 = 0 then stateX states j.1 else c, stateY t states j.1)

def nodesA (t : Tuning) (c : E) (states : ℕ → E × E) : (Fin t.N × Fin 2) × (Fin t.m × Fin 2) → E :=
  fun j => nodes (pairsA t c states j.1).2 (pairsA t c states j.1).1 t.m j.2

def failA (t : Tuning) (c : E) (states : ℕ → E × E)
    (rA : (Fin t.N × Fin 2) × (Fin t.m × Fin 2) → E) (k : ℕ) : Prop :=
  ∃ h : k < t.N, ∃ i : Fin 2, ¬ passes t c (pairsA t c states (⟨k, h⟩, i)).1 (stateY t states k)
    (stateG t states k) (fun j => rA ((⟨k, h⟩, i), j))

open Classical in
def candidate (t : Tuning) (c : E) (states : ℕ → E × E)
    (rA : (Fin t.N × Fin 2) × (Fin t.m × Fin 2) → E) (k : ℕ) : E :=
  if ∃ h : k < t.N, ¬ passes t c (stateX states k) (stateY t states k) (stateG t states k)
    (fun j => rA ((⟨k, h⟩, 0), j)) then stateX states k else c

def stall (t : Tuning) (c : E) (states : ℕ → E × E) (gN : E) : E :=
  gradientStep t.L (stateX states t.N) (regGrad t.α c (stateX states t.N) gN)

def nodesB (t : Tuning) (c : E) (states : ℕ → E × E) (gN : E) : Fin t.N × (Fin t.m × Fin 2) → E :=
  fun j => nodes (stateY t states j.1) (stall t c states gN) t.m j.2

def failB (t : Tuning) (c : E) (states : ℕ → E × E) (gN : E)
    (rB : Fin t.N × (Fin t.m × Fin 2) → E) (k : ℕ) : Prop :=
  ∃ h : k < t.N, ¬ passes t c (stall t c states gN) (stateY t states k) (stateG t states k)
    (fun j => rB (⟨k, h⟩, j))

structure Witness (E : Type*) where
  index : ℕ
  point : E
  base : E

inductive Verdict (E : Type*)
  | finished (x : E)
  | moved (c : E)
  | witness (w : Witness E)

open Classical in
def verdict (t : Tuning) (c : E) (states : ℕ → E × E) (gN : E)
    (rA : (Fin t.N × Fin 2) × (Fin t.m × Fin 2) → E)
    (rB : Fin t.N × (Fin t.m × Fin 2) → E) : Verdict E :=
  let T := horizonIndex t c states
  let fA := firstTrue (failA t c states rA) T
  if fA < T then .witness ⟨fA, candidate t c states rA fA, stateY t states fA⟩
  else if exitIndex t c states ≤ t.N then .moved (stateX states T)
  else if ‖gN‖ ≤ t.ε then .finished (stateX states t.N)
  else if ‖regGrad t.α c (stateX states t.N) gN‖ ≤ t.ε / 10 then .moved (stateX states t.N)
  else
    let fB := firstTrue (failB t c states gN rB) t.N
    if fB < t.N then .witness ⟨fB, stall t c states gN, stateY t states fB⟩
    else .moved (stateX states t.N)

def escapeCandidates (t : Tuning) (states : ℕ → E × E) (w : Witness E) : Fin 6 → E :=
  ![(1 / 2 : ℝ) • (stateX states w.index + stateX states (w.index - 1)),
    (-2 : ℝ) • stateX states w.index + (3 : ℝ) • stateX states (w.index - 1),
    escapePoints t.η w.point w.base 0, escapePoints t.η w.point w.base 1,
    escapePoints t.η w.point w.base 2, escapePoints t.η w.point w.base 3]

def targets (t : Tuning) (states : ℕ → E × E) : Verdict E → Fin 6 → E
  | .witness w => escapeCandidates t states w
  | .finished x => fun _ => x
  | .moved x => fun _ => x

def nodesC (t : Tuning) (c : E) (states : ℕ → E × E) (v : Verdict E) : Fin 6 × (Fin t.m × Fin 2) → E :=
  fun j => nodes c (targets t states v j.1) t.m j.2

def choose (t : Tuning) (c : E) (pts : Fin 6 → E) (rC : Fin 6 × (Fin t.m × Fin 2) → E) : E :=
  ((List.finRange 6).foldl (fun (best : E × ℝ) i =>
    if surrogateOf (fun j => rC (i, j)) c (pts i) < best.2 then
      (pts i, surrogateOf (fun j => rC (i, j)) c (pts i)) else best) (c, 0)).1

end Decision

section Plans

open LongTails.Setups.GradientOnlyThirdOrderNonconvex

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Plan (E U : Type) (n : ℕ) := QueryPlan E E U n

def agdPlan (t : Tuning) (c : E) : (n : ℕ) → E × E → Plan E (ℕ → E × E) n
  | 0, s => .done (fun _ => s)
  | n + 1, s =>
    .ask (extrapolate t.a s.1 s.2) fun gy =>
      (agdPlan t c n (gradientStep t.L (extrapolate t.a s.1 s.2)
          (regGrad t.α c (extrapolate t.a s.1 s.2) gy),
        centerStep t.a t.μ (extrapolate t.a s.1 s.2) s.2
          (regGrad t.α c (extrapolate t.a s.1 s.2) gy))).map
        (fun h k => if k = 0 then s else h (k - 1))

def batch {ι : Type} [Fintype ι] (pts : ι → E) : Plan E (ι → E) (1 * Fintype.card ι) :=
  (QueryPlan.traverse (Fintype.card ι)
    (fun i => QueryPlan.ask (pts ((Fintype.equivFin ι).symm i)) fun r => QueryPlan.done r)).map
    (fun l j => l.getD (Fintype.equivFin ι j) 0)

def finalize (t : Tuning) (c : E) (states : ℕ → E × E) (v : Verdict E)
    (rC : Fin 6 × (Fin t.m × Fin 2) → E) : Verdict E :=
  match v with
  | .finished x => .finished x
  | .moved x => .moved x
  | .witness _ => .moved (choose t c (targets t states v) rC)

def epochLength (t : Tuning) : ℕ :=
  1 * Fintype.card (Fin 6 × (Fin t.m × Fin 2)) + 1 * Fintype.card (Fin t.N × (Fin t.m × Fin 2)) +
    1 * Fintype.card ((Fin t.N × Fin 2) × (Fin t.m × Fin 2)) + 1 + t.N

def epochPlan (t : Tuning) (c : E) : Plan E (Verdict E) (epochLength t) :=
  (agdPlan t c t.N (c, c)).bind fun states =>
  (QueryPlan.ask (stateX states t.N) fun gN => QueryPlan.done gN).bind fun gN =>
  (batch (nodesA t c states)).bind fun rA =>
  (batch (nodesB t c states gN)).bind fun rB =>
  (batch (nodesC t c states (verdict t c states gN rA rB))).map
    (finalize t c states (verdict t c states gN rA rB))

def pad (q : E) : (n : ℕ) → Plan E Unit n
  | 0 => .done ()
  | n + 1 => .ask q fun _ => pad q n

def step (t : Tuning) (x0 : E) : Verdict E → Plan E (Verdict E) (epochLength t)
  | .moved c => epochPlan t c
  | .finished x => (pad x0 (epochLength t)).map fun _ => .finished x
  | .witness w => (pad x0 (epochLength t)).map fun _ => .witness w

def loop (t : Tuning) (x0 : E) : (K : ℕ) → Verdict E → Plan E (Verdict E) (epochLength t * K)
  | 0, v => .done v
  | K + 1, v => (step t x0 v).bind (loop t x0 K)

def output : Verdict E → E
  | .finished x => x
  | .moved c => c
  | .witness w => w.point

end Plans

section Tuning

open LongTails.Setups.GradientOnlyThirdOrderNonconvex

def alpha (p : Params) : ℝ := 2 * p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)

def horizon (p : Params) : ℕ :=
  ⌈Real.sqrt (p.L₁ / (p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) + 4) *
    Real.log (1 + 200 * (p.L₁ + 4 * p.L₃ ^ (1 / 3 : ℝ) * p.ε ^ (2 / 3 : ℝ)) * p.Δ / p.ε ^ 2)⌉₊ + 1

def epochs (p : Params) : ℕ := ⌊2048 * p.Δ * p.L₃ ^ (1 / 3 : ℝ) / p.ε ^ (4 / 3 : ℝ)⌋₊ + 1

def tuning (p : Params) : Tuning where
  α := alpha p
  L := p.L₁ + 2 * alpha p
  μ := alpha p / 2
  a := Real.sqrt ((alpha p / 2) / (p.L₁ + 2 * alpha p))
  R := Real.sqrt (alpha p / p.L₃) / 21
  η := Real.sqrt (alpha p / p.L₃) / 4
  q := alpha p ^ 2 / (4096 * p.L₃)
  τ := alpha p / 32
  ε := p.ε
  m := 16
  N := horizon p

def plan (p : Params) : Plan p.E p.E (epochLength (tuning p) * epochs p) :=
  (loop (tuning p) p.x0 (epochs p) (.moved p.x0)).map output

def algorithm (p : Params) : Algorithm p.E p.E p.E :=
  QueryPlan.algorithm (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ :
    MeasureTheory.ProbabilityMeasure Unit) p.x0 p.x0 _ (fun _ => plan p)

end Tuning

end

end LongTails.Algorithms.GradientOnlyGuarded
