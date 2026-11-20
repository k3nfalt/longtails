import LongTails.Setups.DistributedMeanSquaredSmooth
import Mathlib.Data.Nat.Log

namespace LongTails.Algorithms.MultilevelWorkerSchedule

open DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth

noncomputable def speed (p : Params) (i : Fin p.n) : Time :=
  ∑ j, if p.h j ≤ p.h i then (p.h j)⁻¹ else 0

noncomputable def batchDuration (p : Params) (b : ℕ) : Time :=
  2 * Finset.univ.inf' Finset.univ_nonempty (fun i => max (p.h i) ((b : Time) / speed p i))

noncomputable def samples (p : Params) (b : ℕ) (i : Fin p.n) : ℕ :=
  ⌊((batchDuration p b : Time) : ℝ) / (p.h i : ℝ)⌋₊

noncomputable def fullBatch (p : Params) : ℕ :=
  max 1 ⌈(512 * p.σ / p.ε) ^ 2⌉₊

noncomputable def wanted (p : Params) : ℕ :=
  max 1 ⌈2 * p.L * p.Δ / (p.ε / 512) ^ 2⌉₊

noncomputable def height (p : Params) : ℕ :=
  min (Nat.log2 (wanted p)) (Nat.log 4 (fullBatch p / (1 + Nat.log 4 (fullBatch p))))

def edgeBatch (height level : ℕ) : ℕ :=
  (height + 1) * 4 ^ level

def anchor (width k : ℕ) : ℕ :=
  (k / width - 1) * width

def parentAtRelease (width slot : ℕ) : ℕ :=
  anchor (2 * width) ((slot + 1) * width)

abbrev Slot (p : Params) := (_ : Fin p.n) × ℕ

noncomputable def available (p : Params) (a z : Time) : Finset (Slot p) :=
  Finset.univ.sigma fun i =>
    Finset.Ico ⌈(a : ℝ) / (p.h i : ℝ)⌉₊ ⌊(z : ℝ) / (p.h i : ℝ)⌋₊

noncomputable def boundary (origin tick : Time) (j s : ℕ) : Time :=
  origin + s * (2 ^ j : Time) * tick

noncomputable def window (p : Params) (origin tick : Time) (j s : ℕ) : Finset (Slot p) :=
  available p (boundary origin tick j s) (boundary origin tick j (s+1))

def multilevelBatch (J S j : ℕ) : ℕ := if j = J then S else edgeBatch J j

noncomputable def tickDuration (p : Params) (J S : ℕ) : Time :=
  (Finset.range (J+1)).sup fun j =>
    2 * batchDuration p (demand' j) / 2^j
where
  demand' (j : ℕ) := 2 * edgeBatch J j + if j = J then S else 0

def demand (batch : ℕ → ℕ) : ℕ → ℕ
  | 0 => batch 0
  | j + 1 => 2 * demand batch j + batch (j + 1)

noncomputable def reserve {α : Type*} (choices : Finset α) (b : ℕ) : Finset α :=
  if h : ∃ t ⊆ choices, t.card = b then Classical.choose h else ∅

noncomputable def allocation {α : Type*} [DecidableEq α] (window : ℕ → ℕ → Finset α)
    (batch : ℕ → ℕ) : ℕ → ℕ → Finset α × Finset α
  | 0, s =>
    let current := reserve (window 0 s) (batch 0)
    (current, current)
  | j + 1, s =>
    let children := (allocation window batch j (2 * s)).1 ∪ (allocation window batch j (2 * s + 1)).1
    let current := reserve (window (j + 1) s \ children) (batch (j + 1))
    (children ∪ current, current)

end LongTails.Algorithms.MultilevelWorkerSchedule
