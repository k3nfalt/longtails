import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OracleTemplate.ArrowHurwicz

universe u v

structure AHState (E : Type u) (F : Type v) where
  phase : ℕ
  x : E
  y : F
  v : E
  w : F
  sx : E
  sy : F
  n : ℕ

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def arrowHurwicz (η : ℝ) (x0 : E) (y0 : F) :
    Algorithm ((F ⊕ E) ⊕ ((E × ℝ) ⊕ (F × ℝ))) (E ⊕ F) (E × F) where
  State := AHState E F
  initial := fun _ => ⟨0, x0, y0, 0, 0, 0, 0, 0⟩
  query :=  fun st => (0,
    if st.phase = 0 then Sum.inl (Sum.inl st.y)
    else if st.phase = 1 then Sum.inr (Sum.inl (st.x - η • st.v, η))
    else if st.phase = 2 then Sum.inl (Sum.inr st.x)
    else Sum.inr (Sum.inr (st.y + η • st.w, η)))
  update := fun st r =>
    if st.phase = 0 then ⟨1, st.x, st.y, Sum.elim id (fun _ => 0) r, st.w, st.sx, st.sy, st.n⟩
    else if st.phase = 1 then ⟨2, Sum.elim id (fun _ => 0) r, st.y, st.v, st.w, st.sx, st.sy, st.n⟩
    else if st.phase = 2 then ⟨3, st.x, st.y, st.v, Sum.elim (fun _ => 0) id r, st.sx, st.sy, st.n⟩
    else ⟨0, st.x, Sum.elim (fun _ => 0) id r, st.v, st.w, st.sx + st.x,
      st.sy + Sum.elim (fun _ => 0) id r, st.n + 1⟩
  output := fun st =>
    if st.n = 0 then (st.x, st.y) else (((st.n : ℝ))⁻¹ • st.sx, ((st.n : ℝ))⁻¹ • st.sy)

end OracleTemplate.ArrowHurwicz

open scoped RealInnerProductSpace

namespace LongTails.Setups.BoundedCompositeSaddle

open OracleTemplate OracleTemplate.ArrowHurwicz

universe u

structure Public where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  F : Type u
  [normedF : NormedAddCommGroup F]
  [innerF : InnerProductSpace ℝ F]
  X : Set E
  Y : Set F
  R : ℝ
  L : ℝ
  M : ℝ
  ε : ℝ
  x0 : E
  y0 : F

attribute [instance] Public.normedE Public.innerE Public.normedF Public.innerF

structure Problem (p : Public) where
  K : p.E →L[ℝ] p.F
  g : p.E → ℝ
  h : p.F → ℝ

def objective {p : Public} (I : Problem p) (x : p.E) (y : p.F) : ℝ :=
  I.g x + ⟪y, I.K x⟫ - I.h y

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance p := Problem p
  Query p := (p.F ⊕ p.E) ⊕ ((p.E × ℝ) ⊕ (p.F × ℝ))
  Reply p := p.E ⊕ p.F
  Output p := p.E × p.F
  publicInput := id
  valid p :=
    Convex ℝ p.X ∧ Convex ℝ p.Y ∧ p.x0 ∈ p.X ∧ p.y0 ∈ p.Y ∧
      (∀ x ∈ p.X, ‖x‖ ≤ p.R) ∧ (∀ y ∈ p.Y, ‖y‖ ≤ p.R) ∧ 0 < p.R ∧ 0 < p.L ∧ 0 ≤ p.M ∧ 0 < p.ε
  admissible p I oracle :=
    ‖I.K‖ ≤ p.L ∧ ConvexOn ℝ p.X I.g ∧ ConvexOn ℝ p.Y I.h ∧
      (∀ a ∈ p.X, ∀ b ∈ p.X, |I.g a - I.g b| ≤ p.M * ‖a - b‖) ∧
      (∀ a ∈ p.Y, ∀ b ∈ p.Y, |I.h a - I.h b| ≤ p.M * ‖a - b‖) ∧
      ∃ (adj : p.F → p.E) (proxX : p.E × ℝ → p.E) (proxY : p.F × ℝ → p.F),
        (∀ y z, ⟪adj y, z⟫ = ⟪y, I.K z⟫) ∧
        (∀ q : p.E × ℝ, 0 < q.2 → proxX q ∈ p.X ∧ ∀ w ∈ p.X,
          q.2 * I.g (proxX q) + ‖proxX q - q.1‖ ^ 2 / 2 ≤ q.2 * I.g w + ‖w - q.1‖ ^ 2 / 2) ∧
        (∀ q : p.F × ℝ, 0 < q.2 → proxY q ∈ p.Y ∧ ∀ w ∈ p.Y,
          q.2 * I.h (proxY q) + ‖proxY q - q.1‖ ^ 2 / 2 ≤ q.2 * I.h w + ‖w - q.1‖ ^ 2 / 2) ∧
        (∀ k s y, oracle.answer k (0, (Sum.inl (Sum.inl y))) s = Sum.inl (adj y)) ∧
        (∀ k s x, oracle.answer k (0, (Sum.inl (Sum.inr x))) s = Sum.inr (I.K x)) ∧
        (∀ k s q, oracle.answer k (0, (Sum.inr (Sum.inl q))) s = Sum.inl (proxX q)) ∧
        (∀ k s q, oracle.answer k (0, (Sum.inr (Sum.inr q))) s = Sum.inr (proxY q))
  successful p I output P :=
    ∀ᵐ ω ∂(P : MeasureTheory.Measure _), (output ω).1 ∈ p.X ∧ (output ω).2 ∈ p.Y ∧
      ∀ x ∈ p.X, ∀ y ∈ p.Y, objective I (output ω).1 y - objective I x (output ω).2 ≤ p.ε
  allowedAlgorithm p A := ∃ η : ℝ, 0 < η ∧ A = arrowHurwicz η p.x0 p.y0

end LongTails.Setups.BoundedCompositeSaddle
