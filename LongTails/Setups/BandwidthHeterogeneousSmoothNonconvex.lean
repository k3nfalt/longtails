import LongTails.Setups.DistributedSmoothNonconvex
import LongTails.Setups.FiniteSumSmoothAndConvex

open MeasureTheory

namespace LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex

open DistributedTemplate
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

abbrev Params := DistributedSmoothNonconvex.Params
abbrev Point := DistributedSmoothNonconvex.Point
abbrev Samples := DistributedSmoothNonconvex.Samples
abbrev Functions (p : Params) := Fin p.n → Point p → ℝ
abbrev ComputeQuery (p : Params) := Point p × ℕ+
abbrev ComputeReply (p : Params) := List (Point p)
abbrev CommReply (p : Params) := Fin p.n × List Bool

noncomputable def objective (p : Params) (f : Functions p) : Point p → ℝ :=
  FiniteSumSmoothAndConvex.objective f

structure ComputeState (p : Params) where
  samples : Samples p
  used : ℕ
  pending : Option (Time × ComputeQuery p)

noncomputable def computation (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) :
    ComputationOracle (ComputeQuery p) (ComputeReply p) (Samples p) p.n where
  State := ComputeState p
  initial _ s := ⟨s, 0, none⟩
  submit i s t q :=
    if s.pending.isSome then s else { s with pending := some (t + (q.2 : ℕ) * p.h i, q) }
  answer i s t := do
    let (finish, x, m) ← s.pending
    if finish ≤ t then
      return ((List.range m).map (fun j => g i x (s.samples i (s.used + j))),
        { s with used := s.used + m, pending := none })
    else none

abbrev Mail (p : Params) := Fin p.n × Fin p.n → List (Time × List Bool)

noncomputable def communication (p : Params) :
    CommunicationOracle (CommReply p) (Samples p) p.n where
  State := Mail p
  initial _ := fun _ => []
  submit s t i q :=
    let edge := (i, q.1)
    let start := max t (((s edge).getLast?.map Prod.fst).getD 0)
    Function.update s edge (s edge ++ [(start + p.l + p.b * q.2.length, q.2)])
  answer s t := by
    classical
    exact if h : ∃ edge : Fin p.n × Fin p.n, ∃ m ∈ (s edge).head?, m.1 ≤ t then
      let e := h.choose
      let m := h.choose_spec.choose
      some ((e.2, (e.1, m.2)), Function.update s e (s e).tail)
    else none

noncomputable def system (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) p.n where
  Seed := Samples p
  law := P
  computation := computation p g
  communication := communication p

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n
  Instance := Functions
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 ≤ p.Δ ∧ 0 ≤ p.σ ∧ 0 < p.ε
  admissible p f O :=
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ a : ℝ, (∀ x, a ≤ objective p f x) ∧ objective p f p.x0 - a ≤ p.Δ) ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p)
      (μ : Fin p.n → ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (Samples p)),
      O = system p g P ∧
      ProbabilityTheory.iIndepFun (fun i (s : Samples p) => s i) (P : Measure _) ∧
      ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) (P : Measure _) ∧
        IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (objective p f) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective p f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
