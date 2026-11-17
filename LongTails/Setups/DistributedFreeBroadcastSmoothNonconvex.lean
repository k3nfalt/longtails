import LongTails.TemplateDistributed
import LongTails.Setups.StarNetwork
import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex

open DistributedTemplate

structure Params where
  d : ℕ+
  n : ℕ+
  h : Fin n → Time
  l : Time
  b : Time
  L : ℝ
  Lhat : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)
abbrev Functions (p : Params) := Fin p.n → Point p → ℝ
abbrev ComputeQuery (p : Params) := StarNetwork.ComputeQuery (Point p)
abbrev ComputeReply (p : Params) := StarNetwork.ComputeReply (Point p) (Point p)
abbrev CommReply (p : Params) := StarNetwork.CommReply p.n

noncomputable def objective (p : Params) (f : Functions p) : Point p → ℝ :=
  FiniteSumSmoothAndConvex.objective f

noncomputable def communication (p : Params) : CommunicationOracle (CommReply p) Unit (p.n + 1) :=
  { StarNetwork.communication (Seed := Unit) ⟨p.h, p.l, p.b⟩ with
    submit := fun s time source query =>
      if source = 0 then (StarNetwork.communication (Seed := Unit) ⟨p.h, 0, 0⟩).submit s time source query
      else (StarNetwork.communication (Seed := Unit) ⟨p.h, p.l, p.b⟩).submit s time source query }

noncomputable def system (p : Params) (f : Functions p) :
    Oracle (ComputeQuery p) (ComputeReply p) (CommReply p) (p.n + 1) where
  Seed := Unit
  law := ⟨Measure.dirac (), inferInstance⟩
  computation := StarNetwork.computation ⟨p.h, p.l, p.b⟩ (fun i x (_ : Unit) _ => gradient (f i) x)
  communication := communication p

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery := ComputeQuery
  ComputeReply := ComputeReply
  CommReply := CommReply
  Output := Point
  publicInput := id
  valid p := (∀ i, 0 < p.h i) ∧ 0 < p.L ∧ 0 < p.Lhat ∧ 0 ≤ p.Δ ∧ 0 ≤ p.G ∧ 0 < p.ε
  admissible p f O :=
    O = system p f ∧
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ objective p f x) ∧ objective p f p.x0 - lower ≤ p.Δ)
  successful p f output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient (objective p f) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective p f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
