import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OracleTemplate.BlockSaddle

universe u v

structure AlexState (E : Type u) (F : Type v) where
  phase : Bool
  n : ℕ
  x : E
  y : F
  v : F
  g : E
  best : E × F
  bestVal : ℝ

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def alexGda (γ δ α β : ℝ) (x0 : E) (y0 : F) :
    Algorithm ((E × F) ⊕ (E × F)) (E ⊕ F) (E × F) where
  State := AlexState E F
  initial := fun _ => ⟨false, 0, x0, y0, 0, 0, (x0, y0), 0⟩
  query :=  fun st => (0,
    if st.phase then Sum.inr (st.x - (γ * α) • st.g, st.y)
    else Sum.inl (st.x, st.y + ((δ - 1) * β) • st.v))
  update := fun st r =>
    if st.phase then
      ⟨false, st.n + 1, st.x - α • st.g, st.y + β • Sum.elim (fun _ => (0 : F)) id r,
        Sum.elim (fun _ => (0 : F)) id r, 0,
        if st.n = 0 ∨
            ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 < st.bestVal then
          (st.x, st.y) else st.best,
        if st.n = 0 ∨
            ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 < st.bestVal then
          ‖st.g‖ ^ 2 + ‖Sum.elim (fun _ => (0 : F)) id r‖ ^ 2 + ‖st.v‖ ^ 2 else st.bestVal⟩
    else ⟨true, st.n, st.x, st.y, st.v, Sum.elim id (fun _ => (0 : E)) r, st.best, st.bestVal⟩
  output := fun st => st.best

end OracleTemplate.BlockSaddle

open scoped RealInnerProductSpace

namespace LongTails.Setups.BlockSmoothConvexConcave

open OracleTemplate OracleTemplate.BlockSaddle

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  F : Type u
  [normedF : NormedAddCommGroup F]
  [linearF : InnerProductSpace ℝ F]
  [completeF : CompleteSpace F]
  Lx : ℝ
  Ly : ℝ
  Lxy : ℝ
  γ : ℝ
  δ : ℝ
  x0 : E
  y0 : F

attribute [instance] Public.normedE Public.linearE Public.completeE Public.normedF
  Public.linearF Public.completeF

structure Params extends Public where
  R : ℝ
  ε : ℝ

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := p.E → p.F → ℝ
  Query p := (p.E × p.F) ⊕ (p.E × p.F)
  Reply p := p.E ⊕ p.F
  Output p := p.E × p.F
  publicInput := Params.toPublic
  valid q :=
    0 ≤ q.Lx ∧ 0 ≤ q.Ly ∧ 0 ≤ q.Lxy ∧ 0 < q.Lx + q.Lxy ∧ 0 < q.Ly + q.Lxy ∧
    1 < q.γ ∧ q.γ ≤ 2 ∧ 1 ≤ q.δ ∧ 0 ≤ q.R ∧ 0 < q.ε
  admissible q f oracle :=
    ∃ (gx : q.E × q.F → q.E) (gy : q.E × q.F → q.F),
      (∀ k seed z, oracle.answer k (0, (Sum.inl z)) seed = Sum.inl (gx z)) ∧
      (∀ k seed z, oracle.answer k (0, (Sum.inr z)) seed = Sum.inr (gy z)) ∧
      (∀ z : q.E × q.F, HasGradientAt (fun x => f x z.2) (gx z) z.1) ∧
      (∀ z : q.E × q.F, HasGradientAt (fun y => f z.1 y) (gy z) z.2) ∧
      (∀ y, ConvexOn ℝ Set.univ (fun x => f x y)) ∧
      (∀ x, ConcaveOn ℝ Set.univ (fun y => f x y)) ∧
      (∀ x x' y, ‖gx (x, y) - gx (x', y)‖ ≤ q.Lx * ‖x - x'‖) ∧
      (∀ x y y', ‖gx (x, y) - gx (x, y')‖ ≤ q.Lxy * ‖y - y'‖) ∧
      (∀ x y y', ‖gy (x, y) - gy (x, y')‖ ≤ q.Ly * ‖y - y'‖) ∧
      (∀ x x' y, ‖gy (x, y) - gy (x', y)‖ ≤ q.Lxy * ‖x - x'‖) ∧
      (∃ xs ys, (∀ x y, f xs y ≤ f xs ys ∧ f xs ys ≤ f x ys) ∧
        ‖q.x0 - xs‖ ^ 2 + ‖q.y0 - ys‖ ^ 2 ≤ q.R ^ 2)
  successful q f output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), ∀ (vx : q.E) (vy : q.F),
      HasGradientAt (fun x => f x (output ω).2) vx (output ω).1 →
      HasGradientAt (fun y => f (output ω).1 y) vy (output ω).2 →
      ‖vx‖ ^ 2 + ‖vy‖ ^ 2 ≤ q.ε ^ 2
  allowedAlgorithm p A := ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ A = alexGda p.γ p.δ α β p.x0 p.y0

end LongTails.Setups.BlockSmoothConvexConcave
