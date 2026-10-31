import LongTails.Setups.RennalaIterations
import Mathlib.Data.Finset.Lattice.Fold

open scoped BigOperators

namespace OracleTemplate.Rennala

noncomputable def prefixRate {n : ℕ} (tau : Fin n → ℝ) (m : Fin n) : ℝ :=
  ∑ i : Fin n, if i ≤ m then 1 / tau i else 0

noncomputable def allocationTime {n : ℕ} (tau : Fin n → ℝ) (S : ℕ) (m : Fin n) : ℝ :=
  ((S : ℝ) + (m.val + 1 : ℕ)) / prefixRate tau m

noncomputable def deadline (p : Params) : ℝ :=
  if hn : 0 < p.n then
    96 * Finset.univ.inf' (show (Finset.univ : Finset (Fin p.n)).Nonempty from
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
      (fun m : Fin p.n => (prefixRate p.tau m / (m.val + 1 : ℕ))⁻¹ *
        (p.L * p.Delta / p.eps + p.v * p.L * p.Delta / ((m.val + 1 : ℕ) * p.eps ^ 2)))
  else 0

end OracleTemplate.Rennala

open MeasureTheory

namespace LongTails.Setups.RennalaTime

open OracleTemplate OracleTemplate.Rennala

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query := Query
  Reply := Reply
  Output p := Point p.d × ℝ
  publicInput := publicInput
  valid p :=
    0 < p.n ∧ 0 < p.L ∧ 0 ≤ p.v ∧ 0 < p.eps ∧ 0 ≤ p.Delta ∧
      (∀ i, 0 < p.tau i) ∧ Monotone p.tau
  admissible p I O :=
    SmoothLower p I ∧
      ∃ (Ω : Type) (m : MeasurableSpace Ω),
        letI := m
        ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
          (g : Point p.d → Ω → Point p.d),
          LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
            (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
          StochasticOracle Ω μ I.f g p.v ∧
          O = eventOracle (publicInput p) p.tau P g
  successful p I output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient I.f (output ω).1‖ ^ 2) (P : Measure _) ∧
      (∫ ω, ‖gradient I.f (output ω).1‖ ^ 2 ∂(P : Measure _)) ≤ p.eps ∧
      ∀ᵐ ω ∂(P : Measure _), (output ω).2 ≤ deadline p
  allowedAlgorithm p A := A = algorithm p

end LongTails.Setups.RennalaTime
