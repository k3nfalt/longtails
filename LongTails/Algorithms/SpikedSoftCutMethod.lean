import LongTails.Algorithms.SpikedSoftCut

open scoped BigOperators

noncomputable section

namespace LongTails.Algorithms.SpikedSoftCutMethod

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut

structure Config where
  α : ℝ
  T : ℕ
  b : ℕ
  n : ℕ
  K : ℕ
  N : ℕ → ℕ

abbrev OuterState (q : Params) := ℝ × ℝ × Space q × Bool

def center (q : Params) (s : OuterState q) : ℝ := s.1

def radius (q : Params) (s : OuterState q) : ℝ := s.2.1

def saved (q : Params) (s : OuterState q) : Space q := s.2.2.1

def frozen (q : Params) (s : OuterState q) : Bool := s.2.2.2

def initialState (q : Params) : OuterState q := (0, q.R, 0, false)

def weights (q : Params) (c : Config) (replies : ℕ → Space q) : Fin c.T → ℝ :=
  innerWeights q c.α c.T c.b c.n (fun i => tail q (replies i))

def supportPoints (q : Params) (c : Config) (replies : ℕ → Space q) : Fin c.T → InnerSpace q :=
  innerPoints q c.α c.T c.b (fun i => tail q (replies i))

def sampleCount (q : Params) (c : Config) (k : ℕ) (replies : ℕ → Space q) (i : ℕ) : ℕ :=
  if hi : i < c.T then ⌈(c.N k : ℝ) * weights q c replies ⟨i, hi⟩⌉₊ else 0

def sampleStart (q : Params) (c : Config) (k : ℕ) (replies : ℕ → Space q) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, sampleCount q c k replies j

def scalarQuery (q : Params) (c : Config) (k : ℕ) (s : OuterState q)
    (replies : ℕ → Space q) (t : ℕ) : Space q :=
  match (List.finRange c.T).find? (fun i => t < sampleStart q c k replies (i.val+1)) with
  | some i => join q (center q s) (supportPoints q c replies i)
  | none => 0

def scalarEstimate (q : Params) (c : Config) (k : ℕ) (replies : ℕ → Space q) : ℝ :=
  ∑ i : Fin c.T, weights q c replies i / sampleCount q c k replies i.val *
    ∑ j ∈ Finset.range (sampleCount q c k replies i.val),
      head q (replies (c.T*c.b + sampleStart q c k replies i.val + j))

def primalOutput (q : Params) (c : Config) (s : OuterState q) (replies : ℕ → Space q) : Space q :=
  join q (center q s) (innerOutput q c.α c.T c.b c.n (fun i => tail q (replies i)))

def nextState (q : Params) (c : Config) (k : ℕ) (s : OuterState q)
    (replies : ℕ → Space q) : OuterState q :=
  let estimate := scalarEstimate q c k replies
  let a := if 0 ≤ estimate then center q s - 3*radius q s/8 else center q s + 3*radius q s/8
  let best := if frozen q s then saved q s else primalOutput q c s replies
  let stop := frozen q s || decide (|estimate| ≤ q.ε/(2*radius q s))
  (a, 5*radius q s/8, best, stop)

def epochCost (c : Config) (k : ℕ) : ℕ := c.T*c.b+c.N k+c.T

def queryFrom (q : Params) (c : Config) :
    ℕ → ℕ → OuterState q → (ℕ → Space q) → ℕ → Space q
  | _, 0, _, _, _ => 0
  | k, remaining+1, s, replies, t =>
    if t < c.T*c.b then
      join q (center q s) (CovarianceSoftCut.generatorPoint (innerParams q c.α)
        c.α (2/c.α) c.b (t/c.b) (fun i => tail q (replies i)))
    else if t < epochCost c k then scalarQuery q c k s replies (t-c.T*c.b)
    else queryFrom q c (k+1) remaining (nextState q c k s replies)
      (fun i => replies (epochCost c k+i)) (t-epochCost c k)

def outputFrom (q : Params) (c : Config) :
    ℕ → ℕ → OuterState q → (ℕ → Space q) → Space q
  | _, 0, s, _ => saved q s
  | k, remaining+1, s, replies =>
    outputFrom q c (k+1) remaining (nextState q c k s replies)
      (fun i => replies (epochCost c k+i))

def method (q : Params) (c : Config) : OracleTemplate.Algorithm (Space q) (Space q) (Space q) where
  State := ℕ × (ℕ → Space q)
  initial _ := (0, fun _ => 0)
  query s := (0, queryFrom q c 0 c.K (initialState q) s.2 s.1)
  update s reply := (s.1+1, Function.update s.2 s.1 reply)
  output s := outputFrom q c 0 c.K (initialState q) s.2

def tunedConfig (q : Params) : Config :=
  let Q := 1+Real.log (16*(q.m+1 : ℝ)*(1+q.G*q.R/q.ε))+Real.log (confidenceFactor q)
  let T := ⌈4096*(q.m+1 : ℝ)*Q^2⌉₊
  let K := ⌈32*Q⌉₊
  { α := q.ε/8
    T := T
    b := max 1 ⌈2^31*q.vRest*q.R^2*Q/q.ε^2⌉₊
    n := ⌈256*(1+8*q.R*q.G/q.ε+T)⌉₊
    K := K
    N := fun k => max 1 ⌈8192*(K : ℝ)*q.vTop*q.R^2*(5/8 : ℝ)^(2*k)/q.ε^2⌉₊ }

def algorithm (q : Params) : OracleTemplate.Algorithm (Space q) (Space q) (Space q) :=
  if q.G*q.R ≤ q.ε then
    { State := Unit
      initial _ := ()
      query _ := (0, 0)
      update _ _ := ()
      output _ := 0 }
  else method q (tunedConfig q)

end LongTails.Algorithms.SpikedSoftCutMethod
