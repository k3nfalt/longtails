import LongTails.Template
import LongTails.Algorithms.FreyaTuning
import LongTails.Proofs.FreyaIndependence

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Setups.FreyaPageOptimizedTime

open LongTails.Proofs.FreyaModel

structure Params where
  d : ℕ
  m : ℕ
  n : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d
  τ : Fin n → ℝ≥0∞
  Lplus : ℝ
  lower : ℝ

def publicInput (p : Params) : LongTails.Algorithms.FreyaInputs.Optimized where
  d := p.d
  m := p.m
  Lminus := p.Lminus
  Lpm := p.Lpm
  Δ := p.Δ
  ε := p.ε
  x0 := p.x0
  n := p.n
  τ := p.τ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := LongTails.Algorithms.FreyaInputs.Optimized
  Instance p := Fin p.m → Space p.d → ℝ
  Query p := Option (Request p.d p.m p.n)
  Reply p := Reply p.d p.n
  Output p := Space p.d × ℝ≥0
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 ≤ p.Lminus ∧ 0 ≤ p.Lplus ∧ 0 ≤ p.Lpm ∧
    0 ≤ p.Δ ∧ 0 < p.ε ∧
    0 < p.n ∧ Monotone p.τ ∧ (p.n : ℝ) * Real.log p.n ≤ p.m
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
    PrimitiveService f p.τ O ∧
    LongTails.Proofs.FreyaIndependence.batchScheduleIndependent
      (LongTails.Algorithms.FreyaTuning.optimizedRaw (publicInput p)) f p.τ O
  successful p f output P :=
    Integrable (fun ω => ‖gradient (objective f) ((output ω).1)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective f) ((output ω).1)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ∧
    (∫⁻ ω, ((output ω).2 : ℝ≥0∞) ∂(P : Measure _)) ≤
      12 * (equilibriumTime p.τ (p.m : ℝ≥0∞))
        + ENNReal.ofReal (96 * p.Δ / p.ε) *
          (⨅ S : Fin p.m, min (ENNReal.ofReal p.Lminus * (equilibriumTime p.τ (p.m : ℝ≥0∞))) (ENNReal.ofReal p.Lminus * equilibriumTime p.τ (S.val + 1) + ENNReal.ofReal p.Lpm * (((equilibriumTime p.τ (p.m : ℝ≥0∞)) * equilibriumTime p.τ (S.val + 1) / (S.val + 1)) ^ (1 / (2 : ℝ)))))
  allowedAlgorithm q A := A = LongTails.Algorithms.FreyaTuning.optimized q

end LongTails.Setups.FreyaPageOptimizedTime
