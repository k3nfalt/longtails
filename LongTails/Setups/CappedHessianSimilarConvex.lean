import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Setups.CappedHessianSimilarConvex

open OracleTemplate

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [measurableE : MeasurableSpace E]
  m : ℕ
  [nonzero : NeZero m]
  s : ℕ
  δ : ℝ
  μ : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.finiteE Params.measurableE
  Params.nonzero

inductive Operation where
  | gradient
  | prox (coefficient : {a : ℝ // 0 < a})

structure Query (p : Params) where
  clients : Finset (Fin p.m)
  cap : clients.card ≤ p.s
  request : Fin p.m → Operation × p.E

structure Instance (p : Params) where
  components : Fin p.m → p.E → ℝ
  prox : Fin p.m → ℝ → p.E → p.E

noncomputable def objective {p : Params} (inst : Instance p) : p.E → ℝ :=
  LongTails.Setups.FiniteSumSmoothAndConvex.objective inst.components

noncomputable def centeredGradient {p : Params} (inst : Instance p)
    (i : Fin p.m) (x : p.E) : p.E :=
  gradient (inst.components i) x - gradient (objective inst) x

noncomputable def reply {p : Params} (inst : Instance p) (query : Query p)
    (i : Fin p.m) : p.E :=
  if i ∈ query.clients then
    match (query.request i).1 with
    | .gradient => gradient (inst.components i) (query.request i).2
    | .prox a => inst.prox i a.val (query.request i).2
  else 0

def Assumptions (p : Params) (inst : Instance p) : Prop :=
  (∀ i, ConvexOn ℝ univ (inst.components i)) ∧
  (∀ i x, HasGradientAt (inst.components i) (gradient (inst.components i) x) x) ∧
  StrongConvexOn univ p.μ (objective inst) ∧
  (∀ x y, (1 / (p.m : ℝ)) *
    ∑ i : Fin p.m, ‖centeredGradient inst i x - centeredGradient inst i y‖ ^ 2 ≤
      p.δ ^ 2 * ‖x - y‖ ^ 2) ∧
  (∀ i a, 0 < a → ∀ z, IsMinOn
    (fun u => inst.components i u + a / 2 * ‖u - z‖ ^ 2)
    univ (inst.prox i a z)) ∧
  (∃ xstar, IsMinOn (objective inst) univ xstar ∧
    objective inst p.x0 - objective inst xstar ≤ p.Δ)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Query
  Reply p := Fin p.m → p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.s ∧ p.s ≤ p.m ∧ 0 ≤ p.δ ∧ 0 < p.μ ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p inst oracle := Assumptions p inst ∧
    (∀ history query seed, oracle.answer history (0, query) seed = reply inst query)
  successful p inst output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (objective inst) univ xstar ∧
      Integrable (fun ω => objective inst (output ω) - objective inst xstar)
        (P : Measure _) ∧
      (∫ ω, objective inst (output ω) - objective inst xstar ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.CappedHessianSimilarConvex
