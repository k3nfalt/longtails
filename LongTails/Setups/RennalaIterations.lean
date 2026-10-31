import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.List.FinRange
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory

namespace OracleTemplate.Rennala

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  tau : Fin n → ℝ

structure Public where
  d : ℕ
  n : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  x0 : Point d
  horizon : ℕ

structure Instance (d : ℕ) where
  f : Point d → ℝ
  lower : ℝ

noncomputable def batchSize (v eps : ℝ) : ℕ := max ⌈v / eps⌉₊ 1

noncomputable def stepSize (L v eps : ℝ) : ℝ :=
  if v = 0 then 1 / L else min (1 / L) (eps * (batchSize v eps : ℝ) / (2 * L * v))

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  n := p.n
  L := p.L
  v := p.v
  eps := p.eps
  x0 := p.x0
  horizon := ⌊24 * p.L * p.Delta / p.eps⌋₊

structure SmoothLower (p : Params) (I : Instance p.d) : Prop where
  hasGradient : ∀ x, HasGradientAt I.f (gradient I.f x) x
  lipschitz : ∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖
  lower : ∀ x, I.lower ≤ I.f x
  gap : I.f p.x0 - I.lower = p.Delta

abbrev StochasticOracle {d : ℕ} (Ω : Type) [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (f : Point d → ℝ) (g : Point d → Ω → Point d) (v : ℝ) : Prop :=
  LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) Ω (μ : Measure Ω) f g (Real.sqrt v)

end OracleTemplate.Rennala

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.Rennala

structure Job (d : ℕ) where
  started : ℝ
  point : Point d
  tag : ℕ

abbrev Query (p : Public) := Option (Fin p.n → Job p.d)

abbrev Reply (p : Public) := Option (Fin p.n × ℝ × ℕ × Point p.d)

structure State (p : Public) where
  iteration : ℕ
  count : ℕ
  accumulator : Point p.d
  point : Point p.d
  jobs : Fin p.n → Job p.d
  clock : ℝ
  chosenIndex : Fin (p.horizon + 1)
  selected : Point p.d

noncomputable def nextWorker {n : ℕ} (tau started : Fin n → ℝ) :
    List (Fin n) → Option (Fin n)
  | [] => none
  | i :: rest =>
      match nextWorker tau started rest with
      | none => some i
      | some j => if started i + tau i ≤ started j + tau j then some i else some j

def initialState (p : Public) (j : Fin (p.horizon + 1)) : State p where
  iteration := 0
  count := 0
  accumulator := 0
  point := p.x0
  jobs := fun _ => ⟨0, p.x0, 0⟩
  clock := 0
  chosenIndex := j
  selected := p.x0

noncomputable def eventAnswer (p : Public) (tau : Fin p.n → ℝ) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (query : Query p) (seed : Ω) : Reply p :=
  match query with
  | none => none
  | some jobs =>
      match nextWorker tau (fun i => (jobs i).started) (List.finRange p.n) with
      | none => none
      | some i => some (i, (jobs i).started + tau i, (jobs i).tag, g (jobs i).point seed)

noncomputable def eventOracle (p : Public) (tau : Fin p.n → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, query) seed => eventAnswer p tau g query seed

noncomputable def updateCore (p : Public) (s : State p) (reply : Reply p) : State p :=
    match reply with
    | none => s
    | some (i, time, tag, g) =>
        let jobs := Function.update s.jobs i ⟨time, s.point, s.iteration⟩
        let count := if tag = s.iteration then s.count + 1 else s.count
        let accumulator := if tag = s.iteration then
          s.accumulator + (1 / (batchSize p.v p.eps : ℝ)) • g else s.accumulator
        if count = batchSize p.v p.eps then
          let point := s.point - stepSize p.L p.v p.eps • accumulator
          { s with
            iteration := s.iteration + 1
            count := 0
            accumulator := 0
            point := point
            jobs := jobs
            clock := time
            selected := if s.chosenIndex.val = s.iteration + 1 then point else s.selected }
        else
          { s with count := count, accumulator := accumulator, jobs := jobs, clock := time }

noncomputable def update (p : Public) (s : State p) (reply : Reply p) : State p :=
  if p.horizon ≤ s.iteration then s else updateCore p s reply

noncomputable def algorithm (p : Public) : Algorithm (Query p) (Reply p) (Point p.d × ℝ) where
  Seed := Fin (p.horizon + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.horizon + 1))).toMeasure, inferInstance⟩
  State := State p
  initial := initialState p
  query := fun s => (0, if p.horizon ≤ s.iteration then none else some s.jobs)
  update := update p
  output := fun s => (s.selected, s.clock)

noncomputable def batchEstimator {d : ℕ} {Ω : Type} (S : ℕ)
    (g : Point d → Ω → Point d) (x : Point d) (seeds : Fin S → Ω) : Point d :=
  (1 / (S : ℝ)) • ∑ i, g x (seeds i)

noncomputable def iterate {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d)
    (gamma : ℝ) (S : ℕ) (x0 : Point d) (seeds : ℕ → Ω) : ℕ → Point d
  | 0 => x0
  | k + 1 =>
      let x := iterate g gamma S x0 seeds k
      x - gamma • batchEstimator S g x (fun i => seeds (k * S + i.val))

end OracleTemplate.Rennala

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.BatchIterations

open Rennala

structure Params where
  d : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  extra : ℕ

structure SmoothLower (p : Params) (I : Rennala.Instance p.d) : Prop where
  hasGradient : ∀ x, HasGradientAt I.f (gradient I.f x) x
  lipschitz : ∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖
  lower : ∀ x, I.lower ≤ I.f x
  gap : I.f p.x0 - I.lower = p.Delta

structure Public where
  d : ℕ
  gamma : ℝ
  S : ℕ
  x0 : Point d
  N : ℕ

structure State (p : Public) where
  count : ℕ
  point : Point p.d
  selected : Point p.d
  index : Fin (p.N + 1)

noncomputable def algorithm (p : Public) : Algorithm (Point p.d) (Point p.d) (Point p.d) where
  Seed := Fin (p.N + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.N + 1))).toMeasure, inferInstance⟩
  State := State p
  initial j := ⟨0, p.x0, p.x0, j⟩
  query s := (0, s.point)
  update s reply :=
    let x := s.point - p.gamma • reply
    ⟨s.count + 1, x, if s.count + 1 = s.index.val then x else s.selected, s.index⟩
  output s := s.selected

def blocks {Ω : Type} (S : ℕ) (ξ : ℕ → Ω) : ℕ → Fin S → Ω :=
  fun k i => ξ (k * S + i.val)

noncomputable def oracle (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d) :
    Oracle (Point p.d) (Point p.d) where
  Seed := fun _ => Fin p.S → Ω
  law := P.map (blocks p.S)
  answer := fun _ (_, x) seed => batchEstimator p.S g x seed

end OracleTemplate.BatchIterations

open MeasureTheory

namespace OracleTemplate.RennalaIterations

abbrev Params := BatchIterations.Params

noncomputable def publicInput (p : Params) : BatchIterations.Public where
  d := p.d
  gamma := Rennala.stepSize p.L p.v p.eps
  S := Rennala.batchSize p.v p.eps
  x0 := p.x0
  N := (max 1 ⌈24 * p.Delta * p.L / p.eps⌉₊ + p.extra) - 1

end OracleTemplate.RennalaIterations

namespace LongTails.Setups.RennalaIterations

open OracleTemplate OracleTemplate.RennalaIterations

noncomputable abbrev spec : Setup where
  Params := Params
  Public := BatchIterations.Public
  Instance p := Rennala.Instance p.d
  Query p := Rennala.Point p.d
  Reply p := Rennala.Point p.d
  Output p := Rennala.Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧ 0 ≤ p.Delta
  admissible p I O := BatchIterations.SmoothLower p I ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Rennala.Point p.d → Ω → Rennala.Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
          (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        Rennala.StochasticOracle Ω μ I.f g p.v ∧
        O = BatchIterations.oracle (publicInput p) P g
  successful p I output P := Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.eps
  allowedAlgorithm p A := A = BatchIterations.algorithm p

end LongTails.Setups.RennalaIterations
