import LongTails.Algorithms.ClippedTwoPoint

namespace LongTails.Algorithms.ClippedTwoPointWork

structure Cost where
  operations : ℕ := 0
  projections : ℕ := 0
  queries : ℕ := 0
  directions : ℕ := 0
  deriving DecidableEq

def Cost.add (a b : Cost) : Cost :=
  ⟨a.operations + b.operations, a.projections + b.projections,
    a.queries + b.queries, a.directions + b.directions⟩

structure Charged (α : Type) where
  value : α
  cost : Cost

def pureWork {α : Type} (x : α) : Charged α := ⟨x, {}⟩

def bindWork {α β : Type} (x : Charged α) (f : α → Charged β) : Charged β :=
  let y := f x.value
  ⟨y.value, x.cost.add y.cost⟩

instance : Monad Charged where
  pure := pureWork
  bind := bindWork

noncomputable def realAdd (a b : ℝ) : Charged ℝ := ⟨a + b, { operations := 1 }⟩
noncomputable def realSub (a b : ℝ) : Charged ℝ := ⟨a - b, { operations := 1 }⟩
noncomputable def realMul (a b : ℝ) : Charged ℝ := ⟨a * b, { operations := 1 }⟩
noncomputable def realDiv (a b : ℝ) : Charged ℝ := ⟨a / b, { operations := 1 }⟩
noncomputable def realNorm (a : ℝ) : Charged ℝ := ⟨‖a‖, { operations := 1 }⟩
noncomputable def realSqrt (a : ℝ) : Charged ℝ := ⟨Real.sqrt a, { operations := 1 }⟩
noncomputable def realCeil (a : ℝ) : Charged ℕ := ⟨Nat.ceil a, { operations := 1 }⟩
noncomputable def realLe (a b : ℝ) : Charged Bool := ⟨decide (a ≤ b), { operations := 1 }⟩
noncomputable def natReal (a : ℕ) : Charged ℝ := ⟨a, { operations := 1 }⟩
def natAdd (a b : ℕ) : Charged ℕ := ⟨a + b, { operations := 1 }⟩
def natMul (a b : ℕ) : Charged ℕ := ⟨a * b, { operations := 1 }⟩

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def vectorAdd (a b : E) : Charged E := ⟨a + b, { operations := 1 }⟩
noncomputable def vectorSub (a b : E) : Charged E := ⟨a - b, { operations := 1 }⟩
noncomputable def vectorScale (a : ℝ) (b : E) : Charged E := ⟨a • b, { operations := 1 }⟩
noncomputable def projection (project : E → E) (x : E) : Charged E :=
  ⟨project x, { operations := 1, projections := 1 }⟩
noncomputable def query (reply : ℕ → E → ℝ) (call : ℕ) (x : E) : Charged ℝ :=
  ⟨reply call x, { operations := 1, queries := 1 }⟩
noncomputable def direction (seed : ℕ → E) (i : ℕ) : Charged E :=
  ⟨seed i, { operations := 1, directions := 1 }⟩

noncomputable def clippedScalar (τ x : ℝ) : Charged ℝ := do
  let magnitude ← realNorm x
  let keep ← realLe magnitude τ
  if keep then pure x else
    let factor ← realDiv τ magnitude
    realMul factor x

noncomputable def mix (t : ℕ) (x z : E) : Charged E := do
  let tr ← natReal t
  let denominator ← realAdd tr 2
  let a ← realDiv tr denominator
  let b ← realDiv 2 denominator
  let ax ← vectorScale a x
  let bz ← vectorScale b z
  vectorAdd ax bz

noncomputable def update (project : E → E) (h : ℝ) (t : ℕ)
    (state : E × E) (g : E) : Charged (E × E) := do
  let tr ← natReal t
  let alpha ← realAdd tr 1
  let step ← realDiv alpha h
  let scaled ← vectorScale step g
  let point ← vectorSub state.2 scaled
  let next ← projection project point
  let averaged ← mix t state.1 next
  pure (averaged, next)

noncomputable def estimator (d : ℕ) (τ γ : ℝ) (u : E) (plus minus : ℝ) : Charged E := do
  let difference ← realSub plus minus
  let denominator ← realMul 2 γ
  let secant ← realDiv difference denominator
  let clipped ← clippedScalar τ secant
  let dimension ← natReal d
  let factor ← realMul dimension clipped
  vectorScale factor u

noncomputable def pairedCall (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (index call : ℕ) : Charged E := do
  let u ← direction seed index
  let offset ← vectorScale γ u
  let plusPoint ← vectorAdd x offset
  let minusPoint ← vectorSub x offset
  let plus ← query reply call plusPoint
  let nextCall ← natAdd call 1
  let minus ← query reply nextCall minusPoint
  estimator d τ γ u plus minus

noncomputable def sumPairs (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) : ℕ → ℕ → ℕ → Charged E
  | 0, _, _ => pure 0
  | B + 1, index, call => do
    let first ← pairedCall d τ γ x seed reply index call
    let nextIndex ← natAdd index 1
    let nextCall ← natAdd call 2
    let rest ← sumPairs d τ γ x seed reply B nextIndex nextCall
    vectorAdd first rest

noncomputable def averagedBatch (d : ℕ) (τ γ : ℝ) (x : E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) (B index call : ℕ) : Charged E := do
  let total ← sumPairs d τ γ x seed reply B index call
  let size ← natReal B
  let factor ← realDiv 1 size
  vectorScale factor total

noncomputable def round (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (t : ℕ) (state : E × E) (seed : ℕ → E) (reply : ℕ → E → ℝ)
    (B index call : ℕ) : Charged (E × E) := do
  let center ← mix t state.1 state.2
  let gradient ← averagedBatch d τ γ center seed reply B index call
  update project h t state gradient

noncomputable def batchCount (T : ℕ) (A : ℝ) (t : ℕ) : Charged ℕ := do
  let total ← natReal T
  let time ← natReal t
  let alpha ← realAdd time 1
  let numerator ← realMul total alpha
  let size ← realDiv numerator A
  realCeil size

structure Registers (E : Type) where
  states : (E × E) × (E × E)
  index : ℕ
  call : ℕ

noncomputable def dualRound (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (t B : ℕ) (old : Registers E) (seed : ℕ → E)
    (reply : ℕ → E → ℝ) : Charged (Registers E) := do
  let first ← round d τ₁ γ₁ h project t old.states.1 seed reply B old.index old.call
  let middleIndex ← natAdd old.index B
  let calls ← natMul 2 B
  let middleCall ← natAdd old.call calls
  let second ← round d τ₂ γ₂ h project t old.states.2 seed reply B middleIndex middleCall
  let nextIndex ← natAdd middleIndex B
  let nextCall ← natAdd middleCall calls
  pure ⟨(first, second), nextIndex, nextCall⟩

noncomputable def dualRun (d T : ℕ) (A τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : Registers E) (seed : ℕ → E) (reply : ℕ → E → ℝ) :
    ℕ → Charged (Registers E)
  | 0 => pure initial
  | n + 1 => do
    let old ← dualRun d T A τ₁ τ₂ γ₁ γ₂ h project initial seed reply n
    let B ← batchCount T A n
    dualRound d τ₁ τ₂ γ₁ γ₂ h project n B old seed reply

noncomputable def comparisonPair (s : ℝ) (a b : E) (reply : ℕ → E → ℝ)
    (call : ℕ) : Charged ℝ := do
  let plus ← query reply call a
  let nextCall ← natAdd call 1
  let minus ← query reply nextCall b
  let difference ← realSub plus minus
  clippedScalar s difference

noncomputable def comparisonSum (s : ℝ) (a b : E) (reply : ℕ → E → ℝ) :
    ℕ → ℕ → Charged ℝ
  | 0, _ => pure 0
  | T + 1, call => do
    let first ← comparisonPair s a b reply call
    let nextCall ← natAdd call 2
    let rest ← comparisonSum s a b reply T nextCall
    realAdd first rest

noncomputable def selection (s : ℝ) (a b : E) (reply : ℕ → E → ℝ)
    (T call : ℕ) : Charged E := do
  let total ← comparisonSum s a b reply T call
  let size ← natReal T
  let factor ← realDiv 1 size
  let average ← realMul factor total
  let first ← realLe average 0
  if first then pure a else pure b

noncomputable def padding (q0 : E) (reply : ℕ → E → ℝ) (output : E) :
    ℕ → ℕ → Charged E
  | 0, _ => pure output
  | K + 1, call => do
    let _ ← query reply call q0
    let nextCall ← natAdd call 1
    padding q0 reply output K nextCall

end LongTails.Algorithms.ClippedTwoPointWork
