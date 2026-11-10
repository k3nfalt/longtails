import LongTails.Setups.ParameterFreeHeavyTailedSmooth
import LongTails.Proofs.ParameterFreeNsgdmMain

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.ParameterFreeHeavyTailedNsgdm

open LongTails.Setups.ParameterFreeHeavyTailedSmooth
open LongTails.Algorithms.ParameterFreeNsgdm
open LongTails.Proofs.ParameterFreeNsgdmMain LongTails.Proofs.ParameterFreeNsgdmBudget
open LongTails.Proofs.ParameterFreeNsgdmExecution (phaseStart)

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈80 * (2 + Real.logb 2 (8000 * q.L * q.Δ / q.ε ^ 2 + q.L * q.Δ * q.σ ^ (q.p / (q.p - 1)) * (80 / q.ε) ^ ((3 * q.p - 2) / (q.p - 1)) + q.σ ^ ((5 * q.p - 2) / (2 * q.p - 2)) * (q.L * q.Δ) ^ (-(q.p / (2 * q.p - 2))) * (60 / q.ε) ^ ((3 * q.p - 2) / (2 * q.p - 2)) + (q.σ ^ 2 / (q.L * q.Δ)) ^ (q.p / (2 * q.p - 2)) + Real.sqrt (3 * q.L / q.Δ) + (q.Δ / (3 * q.L)) ^ ((1 : ℝ) / 3) + 6 ^ ((1 : ℝ) / (q.p - 1)) * (5 * q.σ / q.ε) ^ (q.p / (q.p - 1)) + 1 + (64 * (1 + 5 * q.σ / q.ε) ^ q.p * ((22 + 2 * q.p * Real.logb 2 (1 + 5 * q.σ / q.ε)) / (q.p - 1)) ^ 4) ^ ((1 : ℝ) / (q.p - 1)))) ^ 2 * (8000 * q.L * q.Δ / q.ε ^ 2 + q.L * q.Δ * q.σ ^ (q.p / (q.p - 1)) * (80 / q.ε) ^ ((3 * q.p - 2) / (q.p - 1)) + q.σ ^ ((5 * q.p - 2) / (2 * q.p - 2)) * (q.L * q.Δ) ^ (-(q.p / (2 * q.p - 2))) * (60 / q.ε) ^ ((3 * q.p - 2) / (2 * q.p - 2)) + (q.σ ^ 2 / (q.L * q.Δ)) ^ (q.p / (2 * q.p - 2)) + Real.sqrt (3 * q.L / q.Δ) + (q.Δ / (3 * q.L)) ^ ((1 : ℝ) / 3) + 6 ^ ((1 : ℝ) / (q.p - 1)) * (5 * q.σ / q.ε) ^ (q.p / (q.p - 1)) + 1 + (64 * (1 + 5 * q.σ / q.ε) ^ q.p * ((22 + 2 * q.p * Real.logb 2 (1 + 5 * q.σ / q.ε)) / (q.p - 1)) ^ 4) ^ ((1 : ℝ) / (q.p - 1)))⌉₊

lemma budget_eq (q : Params) : (budget q 0 : ℝ) = ⌈budgetReal q.L q.Δ q.σ q.p q.ε⌉₊ := by
  rfl

theorem result : Convergence LongTails.Setups.ParameterFreeHeavyTailedSmooth.spec budget := by
  refine ⟨fun d => algorithm d, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hΔ, hσ, hp, hp2, hε⟩ f O
    ⟨g, ν, P, hIID, rfl, hg, hlip, ⟨lower, hlow, hgap⟩, hmeas, hint, hunb, hmomint, hmom⟩
  have hN : phaseStart (levelStar q.L q.Δ q.σ q.p q.ε + 1) ≤ budget q 0 := by
    have h1 := phaseStart_le_budget hL hΔ hσ hp hp2 hε
    have h2 : (⌈budgetReal q.L q.Δ q.σ q.p q.ε⌉₊ : ℝ) ≥ budgetReal q.L q.Δ q.σ q.p q.ε :=
      Nat.le_ceil _
    have h3 : (phaseStart (levelStar q.L q.Δ q.σ q.p q.ε + 1) : ℝ) ≤ (budget q 0 : ℝ) := by
      rw [budget_eq]; linarith
    exact_mod_cast h3
  exact main_success hIID hg hlip hlow hgap hmeas hint hunb hmomint hmom hL hΔ hσ hp hp2 hε
    (budget q 0) hN

end LongTails.Theorems.ParameterFreeHeavyTailedNsgdm
