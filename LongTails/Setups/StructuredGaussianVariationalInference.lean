import LongTails.Setups.GaussianVariationalInference

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.StructuredGaussianVariationalInference

open OracleTemplate LongTails.Setups.GaussianVariationalInference

def IsPattern {d : ℕ} (S : Fin d → Finset (Fin d)) (w : ℕ) : Prop :=
  ∀ i, i ∈ S i ∧ (∀ j ∈ S i, j ≤ i) ∧ (S i).card ≤ w

def InFamily {d : ℕ} (S : Fin d → Finset (Fin d)) (C : Scale d) : Prop :=
  IsCholesky C ∧ ∀ i j, j ∉ S i → C i j = 0

structure Params where
  d : ℕ
  w : ℕ
  S : Fin d → Finset (Fin d)
  L : ℝ
  μ : ℝ
  R : ℝ
  ε : ℝ
  m0 : Location d
  C0 : Scale d

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Location p.d × Scale p.d
  publicInput p := p
  valid q := 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 ≤ q.R ∧ 0 < q.ε ∧ IsPattern q.S q.w ∧ InFamily q.S q.C0
  admissible q V O :=
    O = { answer := fun _ (_, x) _ => gradient V x } ∧
    (∀ x, HasGradientAt V (gradient V x) x) ∧
    (∀ x y, ‖gradient V x - gradient V y‖ ≤ q.L * ‖x - y‖) ∧
    (∀ x y, q.μ * ‖x - y‖ ^ 2 ≤ ⟪gradient V x - gradient V y, x - y⟫) ∧
    ∃ mstar Cstar, InFamily q.S Cstar ∧
      (∀ m C, InFamily q.S C → objective V mstar Cstar ≤ objective V m C) ∧
      sqDist q.m0 mstar q.C0 Cstar ≤ q.R ^ 2
  successful q V output P :=
    Measurable output ∧ (∀ ω, InFamily q.S (output ω).2) ∧
    ∀ mstar Cstar, InFamily q.S Cstar →
      (∀ m C, InFamily q.S C → objective V mstar Cstar ≤ objective V m C) →
      Integrable (fun ω => objective V (output ω).1 (output ω).2 - objective V mstar Cstar)
        (P : Measure _) ∧
      (∫ ω, objective V (output ω).1 (output ω).2 - objective V mstar Cstar ∂(P : Measure _))
        ≤ q.ε

end LongTails.Setups.StructuredGaussianVariationalInference
