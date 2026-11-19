import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory OracleTemplate
open scoped ENNReal

namespace LongTails.Setups.CorruptedFirstOrderNonconvex

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Params where
  d : ℕ
  L : ℝ
  Δ : ℝ
  ε : ℝ
  k : ℕ
  failure : Set.Icc (0 : ℝ≥0∞) (1 / 4)
  x0 : Space d

inductive Reachable {X Y : Type} (O : Oracle X Y) : List ((Fin 1 × X) × Y) → Prop
  | nil : Reachable O []
  | snoc {h} (hh : Reachable O h) (q : Fin 1 × X) (s : O.Seed h.length) :
      Reachable O (h ++ [(q, O.answer h q s)])

noncomputable def errors {X : Type} (clean : X → ℝ × X → Prop)
    (h : List ((Fin 1 × X) × (ℝ × X))) : ℕ := by
  classical exact (h.filter fun e => ¬clean e.1.2 e.2).length

def accurate (p : Params) (f : Space p.d → ℝ) (g : Space p.d → Space p.d)
    (x : Space p.d) (r : ℝ × Space p.d) : Prop :=
  |r.1 - f x| ≤ p.ε ^ 2 / (128 * p.L) ∧ r.2 = g x

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Space p.d → ℝ
  Query p := Space p.d
  Reply p := ℝ × Space p.d
  Output p := Space p.d
  publicInput p := p
  valid p := 0 < p.L ∧ 0 < p.ε ∧ 0 ≤ p.Δ
  admissible p f O :=
    (∀ x, HasGradientAt f (gradient f x) x) ∧
    (∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) ∧
    (∃ lower : ℝ, (∀ x, lower ≤ f x) ∧ f p.x0 - lower ≤ p.Δ) ∧
    ∃ g : Space p.d → Space p.d, (∀ x, ‖g x - gradient f x‖ ≤ p.ε / 8) ∧
      ∀ h, Reachable O h → errors (accurate p f g) h ≤ p.k
  successful p f out P := (P : Measure _) {s | p.ε < ‖gradient f (out s)‖} ≤ p.failure.val

end LongTails.Setups.CorruptedFirstOrderNonconvex
