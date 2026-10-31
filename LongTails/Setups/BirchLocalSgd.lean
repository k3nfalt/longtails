import LongTails.Setups.BirchSgd
import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

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

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.BirchLocalSgd

open OracleTemplate OracleTemplate.BirchSgd OracleTemplate.BirchMethods
open OracleTemplate.Rennala (Instance Point)

structure Params where
  d : ℕ
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  n : ℕ
  B : ℕ
  M : ℕ → Fin n → ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  gamma := localStep p.L p.σ p.ε p.B
  x0 := p.x0
  tree := localTree p.n p.B p.M
  branch := chainBranch
  K := localHorizon p.L p.σ p.ε p.Δ p.B

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 < p.B ∧ ∀ r, ∑ i, p.M r i = p.B
  admissible p I O :=
    LongTails.Setups.BirchSgd.SmoothObjective I.f p.L ∧
    LongTails.Setups.BirchSgd.LowerBounded I.f I.lower ∧ I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (η : ℕ → Ω) => η k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        O = gradientOracle P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = birch q

end LongTails.Setups.BirchLocalSgd
