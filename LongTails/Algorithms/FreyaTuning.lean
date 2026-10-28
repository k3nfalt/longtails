import LongTails.Template
import LongTails.Algorithms.FreyaPage
import LongTails.Algorithms.FreyaSerial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.List.MinMax

open OracleTemplate
open scoped ENNReal NNReal

namespace LongTails.Algorithms.FreyaTuning

open LongTails.Proofs.FreyaModel LongTails.Algorithms.FreyaInputs

noncomputable def familyCoefficient (p : Base) (S : ℕ) (ρ : ℝ) : ℝ :=
  p.Lminus + p.Lpm * Real.sqrt ((1 - ρ) / (ρ * S))

noncomputable def familyStep (p : Base) (S : ℕ) (ρ : ℝ) : ℝ :=
  1 / familyCoefficient p S ρ

noncomputable def familyHorizon (p : Base) (S : ℕ) (ρ : ℝ) : ℕ :=
  max 1 ⌈2 * p.Δ * familyCoefficient p S ρ / p.ε⌉₊

noncomputable def simpleBatch (p : Simple) : ℕ := ⌈Real.sqrt p.m⌉₊

noncomputable def simpleProbability (p : Simple) : ℝ := 1 / Real.sqrt p.m

noncomputable def simpleStep (p : Simple) : ℝ :=
  familyStep p.toWorkers.toBase (simpleBatch p) (simpleProbability p)

noncomputable def simpleHorizon (p : Simple) : ℕ :=
  familyHorizon p.toWorkers.toBase (simpleBatch p) (simpleProbability p)

noncomputable def batchObjective (p : Optimized) (S : ℕ) : ℝ≥0∞ :=
  min (ENNReal.ofReal p.Lminus * equilibriumTime p.τ p.m)
    (ENNReal.ofReal p.Lminus * equilibriumTime p.τ S + ENNReal.ofReal p.Lpm *
      ((equilibriumTime p.τ p.m * equilibriumTime p.τ S / S) ^ (1 / (2 : ℝ))))

noncomputable def optimizedBatch (p : Optimized) : ℕ :=
  (List.minOn? (batchObjective p) (List.range' 1 p.m)).getD 1

noncomputable def optimizedProbability (p : Optimized) : ℝ :=
  let S := optimizedBatch p
  let tm := equilibriumTime p.τ p.m
  let ts := equilibriumTime p.τ S
  if tm = 0 ∨ tm = ⊤ then 1 else
    if ENNReal.ofReal p.Lminus * tm ≤ ENNReal.ofReal p.Lminus * ts +
        ENNReal.ofReal p.Lpm * ((tm * ts / S) ^ (1 / (2 : ℝ))) then 1
    else (ts / tm).toReal

noncomputable def optimizedStep (p : Optimized) : ℝ :=
  familyStep p.toWorkers.toBase (optimizedBatch p) (optimizedProbability p)

noncomputable def optimizedHorizon (p : Optimized) : ℕ :=
  familyHorizon p.toWorkers.toBase (optimizedBatch p) (optimizedProbability p)

noncomputable def constantPoint {Query Reply Output : Type} (idle : Query) (x : Output) :
    Algorithm Query Reply Output 1 where
  State := Unit
  initial := fun _ => ()
  query := fun _ => (0, idle)
  update := fun _ _ => ()
  output := fun _ => x

noncomputable def serial (p : Serial) :
    Algorithm (Option (Fin p.m × Space p.d)) (Space p.d) (Space p.d) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none p.x0 else
    FreyaSerial.algorithm
      { d := p.d, m := p.m, x0 := p.x0,
        η := familyStep p.toBase p.S p.ρ,
        S := p.S, ρ := p.ρ, K := familyHorizon p.toBase p.S p.ρ }

noncomputable def familyRaw (p : Family) (usePrefix : Bool) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := familyStep p.toWorkers.toBase p.S p.ρ
  S := p.S
  ρ := p.ρ
  K := familyHorizon p.toWorkers.toBase p.S p.ρ
  «prefix» := usePrefix

noncomputable def iterations (p : Family) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none p.x0 else
    FreyaPage.pointOnly (familyRaw p false)

noncomputable def freeTime (p : Family) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.«prefix» (familyRaw p true)

noncomputable def optimizedRaw (p : Optimized) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := optimizedStep p
  S := optimizedBatch p
  ρ := optimizedProbability p
  K := optimizedHorizon p
  «prefix» := false

noncomputable def optimized (p : Optimized) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.literal (optimizedRaw p)

noncomputable def simpleRaw (p : Simple) : Raw where
  d := p.d
  m := p.m
  n := p.n
  x0 := p.x0
  η := simpleStep p
  S := simpleBatch p
  ρ := simpleProbability p
  K := simpleHorizon p
  «prefix» := false

noncomputable def simple (p : Simple) :
    Algorithm (Option (Request p.d p.m p.n)) (Reply p.d p.n) (Space p.d × ℝ≥0) 1 :=
  if p.Δ = 0 ∨ p.Lminus = 0 then constantPoint none (p.x0, 0) else
    FreyaPage.literal (simpleRaw p)

end LongTails.Algorithms.FreyaTuning
