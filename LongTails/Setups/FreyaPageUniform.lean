import LongTails.Template
import LongTails.Algorithms.FreyaTuning

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Setups.FreyaPageUniform

open LongTails.Proofs.FreyaModel

structure Params where
  d : ℕ
  m : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d
  S : ℕ
  ρ : ℝ
  Lplus : ℝ
  lower : ℝ

def publicInput (p : Params) : LongTails.Algorithms.FreyaInputs.Serial where
  d := p.d
  m := p.m
  Lminus := p.Lminus
  Lpm := p.Lpm
  Δ := p.Δ
  ε := p.ε
  x0 := p.x0
  S := p.S
  ρ := p.ρ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := LongTails.Algorithms.FreyaInputs.Serial
  Instance p := Fin p.m → Space p.d → ℝ
  Query p := Option (Fin p.m × Space p.d)
  Reply p := Space p.d
  Output p := Space p.d
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 ≤ p.Lminus ∧ 0 ≤ p.Lplus ∧ 0 ≤ p.Lpm ∧
    0 ≤ p.Δ ∧ 0 < p.ε ∧
    0 < p.S ∧ 0 < p.ρ ∧ p.ρ ≤ 1
  admissible p f O :=
    (∀ i, Differentiable ℝ (f i)) ∧
    (∀ x, p.lower ≤ objective f x) ∧
    objective f p.x0 - p.lower ≤ p.Δ ∧
    (∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤
      p.Lminus * ‖x - y‖) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lplus ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) -
      ‖gradient (objective f) x - gradient (objective f) y‖ ^ 2 ≤
      p.Lpm ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ k, Measurable (fun z : (Fin 1 × Option (Fin p.m × Space p.d)) × O.Seed k =>
      O.answer k z.1 z.2)) ∧
    ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)), ∀ k,
      O.answer k (0, none) (ω k) = 0 ∧
      ∀ i x, O.answer k (0, some (i, x)) (ω k) = gradient (f i) x
  successful p f output P :=
    Integrable (fun ω => ‖gradient (objective f) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = LongTails.Algorithms.FreyaTuning.serial q

end LongTails.Setups.FreyaPageUniform
