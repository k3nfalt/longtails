import LongTails.Setups.StochasticSmoothBanachFixedPoint
import LongTails.Proofs.SmoothBanachAccuracy
import LongTails.Proofs.SmoothBanachBudget

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.StochasticSmoothBanachFixedPoint

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open LongTails.Proofs.SmoothBanachAccuracy LongTails.Proofs.SmoothBanachBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 20 * (1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2) * (1 + Real.log (1 + 16 * q.R / q.ε)) ^ 4⌉₊

theorem result : Convergence LongTails.Setups.StochasticSmoothBanachFixedPoint.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hC, hR, hσ, hε, J, hJ, hJn, hsmooth⟩ T O
    ⟨g, p, P, hIID, rfl, hT, ⟨xstar, hstar, hdist⟩, hg⟩
  have hC0 : 0 ≤ q.C := le_trans (by norm_num) hC
  have hK := public_cost_bound q hC0 hR hε
  let K := ⌈2 ^ 20 * (1 + q.R / q.ε + q.C * q.σ ^ 2 / q.ε ^ 2) * (1 + Real.log (1 + 16 * q.R / q.ε)) ^ 4⌉₊
  let O : Oracle q.E q.E :=
    { Seed := fun _ => q.Ω
      law := P
      answer := fun _ (_, x) seed => g x seed }
  have ha := execution_accuracy q T hT hC0 hε J hsmooth p P hIID g hg xstar hstar hdist K hK
  let z := fun ξ => output q O (fun _ => K) ξ
  change Measurable (fun seed : Unit × (ℕ → q.Ω) => execute O (algorithm q) (fun _ => K) seed.1 seed.2) ∧
    Integrable (fun seed : Unit × (ℕ → q.Ω) =>
      ‖T (execute O (algorithm q) (fun _ => K) seed.1 seed.2) -
        execute O (algorithm q) (fun _ => K) seed.1 seed.2‖ ^ 2) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed : Unit × (ℕ → q.Ω),
      ‖T (execute O (algorithm q) (fun _ => K) seed.1 seed.2) -
        execute O (algorithm q) (fun _ => K) seed.1 seed.2‖ ^ 2
      ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε ^ 2
  have he (seed : Unit × (ℕ → q.Ω)) : execute O (algorithm q) (fun _ => K) seed.1 seed.2 =
      z seed.2 := by
    rcases seed with ⟨⟨⟩, ξ⟩
    rfl
  simp_rw [he]
  have hi : Integrable (fun ξ => ‖T (z ξ) - z ξ‖ ^ 2) (P : Measure (ℕ → q.Ω)) := ha.2.1
  refine ⟨ha.1.comp measurable_snd, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ())
      (ν := (P : Measure (ℕ → q.Ω)))).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ => ‖T (z ξ) - z ξ‖ ^ 2)]
    simpa using ha.2.2

end LongTails.Theorems.StochasticSmoothBanachFixedPoint
