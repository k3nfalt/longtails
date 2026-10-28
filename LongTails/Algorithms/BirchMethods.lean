import LongTails.Algorithms.BirchSgd

namespace OracleTemplate.BirchMethods

open OracleTemplate OracleTemplate.BirchSgd

def chainAux (src : ℕ → ℕ) (cont : ℕ → Bool) (k : ℕ) : ℕ :=
  if cont k then 2 * k - 1 else 2 * src k

def chainTree (src : ℕ → ℕ) (cont : ℕ → Bool) : Tree where
  base j := if j % 2 = 0 then chainAux src cont (j / 2) else j - 1
  point j := chainAux src cont (j / 2)
  grad j := 2 * (j / 2)

def chainBranch (k : ℕ) : ℕ := 2 * k

noncomputable def chainStep (L σ ε Rt : ℝ) : ℝ :=
  min (1 / (2 * Rt * L)) (if σ = 0 then 1 / (2 * Rt * L) else ε / (4 * σ ^ 2 * L))

def localOffsets (n : ℕ) (M : ℕ → Fin n → ℕ) (r : ℕ) : Finset ℕ :=
  Finset.univ.image fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), M r j

def localSrc (B k : ℕ) : ℕ := B * (k / B)

def localCont (n B : ℕ) (M : ℕ → Fin n → ℕ) (k : ℕ) : Bool :=
  decide (k % B ∉ localOffsets n M (k / B))

def localTree (n B : ℕ) (M : ℕ → Fin n → ℕ) : Tree :=
  chainTree (localSrc B) (localCont n B M)

noncomputable def localStep (L σ ε : ℝ) (B : ℕ) : ℝ :=
  min (1 / (2 * B * L)) (if σ = 0 then 1 / (2 * B * L) else ε / (4 * σ ^ 2 * L))

noncomputable def localHorizon (L σ ε Δ : ℝ) (B : ℕ) : ℕ :=
  ⌈4 * B * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2⌉₊

def cycleGroup (n s g : ℕ) : ℕ := ((Finset.range n).filter fun i => i / s = g).card

def cycleLength (n s : ℕ) : ℕ := (n + s - 1) / s

def cycleSteps (n s t : ℕ) : ℕ := min (t + 1) (cycleLength n s)

def cyclePos (n s t : ℕ) : ℕ :=
  ∑ u ∈ Finset.range t, cycleGroup n s (u % cycleLength n s) * cycleSteps n s u

def cycleLoop (n s k : ℕ) : ℕ := Nat.findGreatest (fun t => cyclePos n s t ≤ k) k

def cycleSrc (n s k : ℕ) : ℕ :=
  if cycleLength n s ≤ cycleLoop n s k then
    cyclePos n s (cycleLoop n s k + 1 - cycleLength n s)
  else 0

def cycleCont (n s k : ℕ) : Bool :=
  decide ((k - cyclePos n s (cycleLoop n s k)) % cycleSteps n s (cycleLoop n s k) ≠ 0)

def cycleTree (n s : ℕ) : Tree := chainTree (cycleSrc n s) (cycleCont n s)

noncomputable def cycleStep (L σ ε : ℝ) (n s : ℕ) : ℝ :=
  min (s / (4 * n ^ 2 * L)) (if σ = 0 then s / (4 * n ^ 2 * L) else ε / (4 * σ ^ 2 * L))

noncomputable def cycleHorizon (L σ ε Δ : ℝ) (n s : ℕ) : ℕ :=
  ⌈8 * n ^ 2 * L * Δ / (s * ε) + 8 * σ ^ 2 * L * Δ / ε ^ 2⌉₊

def asyncSrc (M : ℕ) (δ : ℕ → ℕ) (k : ℕ) : ℕ := M * (k / M - δ (k / M))

def asyncCont (M k : ℕ) : Bool := decide (k % M ≠ 0)

def asyncTree (M : ℕ) (δ : ℕ → ℕ) : Tree := chainTree (asyncSrc M δ) (asyncCont M)

noncomputable def asyncStep (L σ ε : ℝ) (B M : ℕ) : ℝ :=
  min (1 / (2 * (B + M - 1) * L))
    (if σ = 0 then 1 / (2 * (B + M - 1) * L) else ε / (4 * σ ^ 2 * L))

noncomputable def asyncHorizon (L σ ε Δ : ℝ) (B M : ℕ) : ℕ :=
  ⌈4 * (B + M - 1) * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2⌉₊

end OracleTemplate.BirchMethods
