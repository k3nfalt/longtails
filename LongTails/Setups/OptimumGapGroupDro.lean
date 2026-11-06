import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.OptimumGapGroupDro

open OracleTemplate

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Public where
  d : ℕ
  K : ℕ
  [nonzeroK : NeZero K]
  Z : Type
  [measurableZ : MeasurableSpace Z]
  domain : Set (Space d)
  x0 : Space d
  loss : Space d → Z → ℝ
  R : ℝ
  G : ℝ
  ε : ℝ
  δ : ℝ

attribute [instance] Public.nonzeroK Public.measurableZ

structure Params where
  data : Public
  gaps : Fin data.K → ℝ

abbrev Rows (q : Public) := Fin q.K → q.Z

abbrev Reservoir (q : Public) := ℕ → Rows q

noncomputable def risk (q : Public) (p : ProbabilityMeasure (Rows q))
    (i : Fin q.K) (x : Space q.d) : ℝ :=
  ∫ z, q.loss x (z i) ∂(p : Measure (Rows q))

noncomputable def objective (q : Public) (p : ProbabilityMeasure (Rows q))
    (x : Space q.d) : ℝ :=
  ⨆ i : Fin q.K, risk q p i x

def groupCount (q : Public) (history : List ((Fin 1 × Fin q.K) × q.Z))
    (i : Fin q.K) : ℕ :=
  history.countP (fun entry => decide (entry.1.2 = i))

noncomputable def reservoirOracle (q : Public) (P : ProbabilityMeasure (Reservoir q)) :
    Oracle (Fin q.K) q.Z where
  Seed := fun _ => Reservoir q
  law := P.map (fun ω => fun _ : ℕ => ω)
  answer history query ω := ω (groupCount q history query.2) query.2

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance q := ProbabilityMeasure (Rows q)
  Query q := Fin q.K
  Reply q := q.Z
  Output q := Space q.d
  publicInput p := p.data
  valid p :=
    0 ≤ p.data.R ∧ 0 ≤ p.data.G ∧ 0 < p.data.ε ∧ p.data.ε ≤ 1 ∧
    0 < p.data.δ ∧ p.data.δ ≤ 1 / 4 ∧
    p.data.x0 ∈ p.data.domain ∧ IsCompact p.data.domain ∧
    Convex ℝ p.data.domain ∧
    (∀ x ∈ p.data.domain, ‖x - p.data.x0‖ ≤ p.data.R) ∧
    Measurable (Function.uncurry p.data.loss) ∧
    (∀ z, ConvexOn ℝ p.data.domain (fun x => p.data.loss x z)) ∧
    (∀ z, ∀ x ∈ p.data.domain, 0 ≤ p.data.loss x z ∧ p.data.loss x z ≤ 1) ∧
    (∀ z, ∀ x ∈ p.data.domain, ∀ y ∈ p.data.domain,
      |p.data.loss x z - p.data.loss y z| ≤ p.data.G * ‖x - y‖) ∧
    (∀ i, 0 ≤ p.gaps i ∧ p.gaps i ≤ 1)
  admissible p model O :=
    iIndepFun (fun i (z : Rows p.data) => z i) (model : Measure _) ∧
    (∃ P : ProbabilityMeasure (Reservoir p.data),
      StochasticGeneralizedSmoothAndConvex.IID (fun n (ω : Reservoir p.data) => ω n)
        (model : Measure _) (P : Measure _) ∧ O = reservoirOracle p.data P) ∧
    (∃ xstar ∈ p.data.domain,
      IsMinOn (objective p.data model) p.data.domain xstar ∧
      ∀ i, p.gaps i ≤ objective p.data model xstar - risk p.data model i xstar)
  successful p model output P :=
    Measurable output ∧ (∀ ω, output ω ∈ p.data.domain) ∧
    ∃ xstar ∈ p.data.domain,
      IsMinOn (objective p.data model) p.data.domain xstar ∧
      (P : Measure _) {ω | p.data.ε < objective p.data model (output ω) -
        objective p.data model xstar} ≤ ENNReal.ofReal p.data.δ

end LongTails.Setups.OptimumGapGroupDro
