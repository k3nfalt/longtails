import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory

namespace LongTails.Setups.GraphBandwidthSmoothNonconvex

open DistributedTemplate
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

structure Params where
  d : ℕ
  n : ℕ+
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  G : SimpleGraph (Fin n)
  b : Fin n → Fin n → Time
  h : Fin n → Time
  L : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  x₀ : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Params.base (p : Params) : DistributedSmoothNonconvex.Params :=
  ⟨p.d, p.n, p.Ω, p.h, 0, 0, p.L, p.Δ, p.σ, p.ε, p.x₀⟩

abbrev Point (p : Params) := DistributedSmoothNonconvex.Point p.base
abbrev Samples (p : Params) := DistributedSmoothNonconvex.Samples p.base
abbrev ComputeQuery (p : Params) := BandwidthHeterogeneousSmoothNonconvex.ComputeQuery p.base
abbrev ComputeReply (p : Params) := BandwidthHeterogeneousSmoothNonconvex.ComputeReply p.base
abbrev CommReply (p : Params) := BandwidthHeterogeneousSmoothNonconvex.CommReply p.base
abbrev Mail (p : Params) := BandwidthHeterogeneousSmoothNonconvex.Mail p.base

noncomputable def communication (p : Params) :
    CommunicationOracle (CommReply p) (Samples p) p.n where
  State := Mail p
  initial _ := fun _ => []
  submit s t i q := by
    classical
    let j := q.1
    let edge := (i, j)
    let start := max t (((s edge).getLast?.map Prod.fst).getD 0)
    exact if i = j ∨ p.G.Adj i j then
      let duration := if i = j then 0 else (q.2.length : Time) / p.b i j
      Function.update s edge (s edge ++ [(start + duration, q.2)])
    else s
  answer := (BandwidthHeterogeneousSmoothNonconvex.communication p.base).answer

noncomputable def system (p : Params) (g : Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) p.n where
  Seed := Samples p
  law := P
  computation := BandwidthHeterogeneousSmoothNonconvex.computation p.base (fun _ => g)
  communication := communication p

structure SgdTuning (p : Params) where
  K : ℕ+
  batch : Fin p.n → ℕ
  positiveBatch : 0 < ∑ i, batch i
  η : ℝ
  positiveStep : 0 < η
  width : ℕ+
  radius : Point p → ℝ
  positiveRadius : ∀ x, 0 < radius x

noncomputable def SgdTuning.quantize {p : Params} (q : SgdTuning p) (x v : Point p) : Point p :=
  let R := q.radius x
  let M : ℕ := 2 ^ (q.width : ℕ) - 1
  let δ := 2 * R / (M : ℝ)
  let z := if ‖v‖ ≤ R then v else (R / ‖v‖) • v
  WithLp.toLp 2 (fun j => δ * (((min ⌊z j / δ + (M : ℝ) / 2⌋₊ M : ℕ) : ℝ) - (M : ℝ) / 2))

noncomputable def SgdTuning.iterate {p : Params} (q : SgdTuning p)
    (g : Point p → p.Ω → Point p) (s : Samples p) : ℕ → Point p
  | 0 => p.x₀
  | k + 1 =>
      let x := q.iterate g s k
      let mean i := (q.batch i : ℝ)⁻¹ •
        ∑ j ∈ Finset.range (q.batch i), g x (s i (k * q.batch i + j))
      let B : ℕ := ∑ i, q.batch i
      x - q.η • q.quantize x (∑ i, ((q.batch i : ℝ) / B) • q.quantize x (mean i))

def IsQuantizedMinibatchSgd (p : Params)
    (A : Algorithm (ComputeQuery p) (ComputeReply p) (CommReply p) (Point p) p.n) : Prop :=
  ∃ (q : SgdTuning p) (select : A.Seed → Fin q.K) (finish : Time),
    Measurable select ∧ Measure.map select (A.law : Measure _) = (PMF.uniformOfFintype _).toMeasure ∧
    ∀ (g : Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
      (a : A.Seed) (s : Samples p),
      let O := system p g P
      let J := (select a).val
      let X := q.iterate g s
      (∀ (T : Time) (k : ℕ),
        let c := run O A k (initial O A T (a,s))
        (A.output (c.workers A.root) = p.x₀ ∨ A.output (c.workers A.root) = X J) ∧
        ∀ i, (c.oracle.computation i).used ≤ J * q.batch i ∧
          ∀ entry ∈ (c.oracle.computation i).pending, ∃ l < J,
            (c.oracle.computation i).used = l * q.batch i ∧
              entry.2.1 = X l ∧ (entry.2.2 : ℕ) = q.batch i) ∧
      ∃ k : ℕ, let c := run O A k (initial O A finish (a,s))
        step O A c = none ∧ A.output (c.workers A.root) = X J ∧
          ∀ i, (c.oracle.computation i).used = J * q.batch i

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n
  Instance p := Point p → ℝ
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output := Point
  publicInput := id
  allowedAlgorithm := IsQuantizedMinibatchSgd
  valid p := p.G.Connected ∧ (∀ i j, p.G.Adj i j → 0 < p.b i j ∧ p.b i j = p.b j i) ∧
    (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ a : ℝ, (∀ x, a ≤ f x) ∧ f p.x₀ - a ≤ p.Δ) ∧
    ∃ (g : Point p → p.Ω → Point p) (μ : ProbabilityMeasure p.Ω)
      (P : ProbabilityMeasure (Samples p)),
      O = system p g P ∧ IsStochasticGradient (Point p) p.Ω (μ : Measure _) f g p.σ ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (μ : Measure _) (P : Measure _)
  successful p f output P :=
    Measurable output ∧ Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.GraphBandwidthSmoothNonconvex
