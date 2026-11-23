import LongTails.Setups.GeneralizedLipschitzMinty
import LongTails.Proofs.GeneralizedMintyDescent

namespace LongTails.Theorems.GeneralizedMintyExtragradient

open OracleTemplate MeasureTheory LongTails.Algorithms.GeneralizedMintyExtragradient
open LongTails.Proofs.GeneralizedMintyDescent

noncomputable def budget : (let S := LongTails.Setups.GeneralizedLipschitzMinty.spec;
    S.Params → Fin S.numOracles → ℕ) :=
  fun p _ => 2 * (1 + ⌈32 * (p.R * (p.L0 / p.ε + p.L1)) ^ 2⌉₊)

theorem result : Convergence LongTails.Setups.GeneralizedLipschitzMinty.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp F O had
  obtain ⟨hO, hc, hreg, z, _, hz, hm⟩ := had
  let n := 1 + ⌈32 * (p.R * (p.L0 / p.ε + p.L1)) ^ 2⌉₊
  let c := ‖F ((cycle p F)^[n] p.x0)‖
  have h (w : (algorithm p).Seed × ((k : ℕ) → O.Seed k)) :
      ‖F (execute O (algorithm p) (budget p) w.1 w.2)‖ = c :=
    congrArg (fun x => ‖F x‖) (output_after p F O hO n w.1 w.2)
  let μ : Measure ((algorithm p).Seed × ((k : ℕ) → O.Seed k)) :=
    ((algorithm p).law : Measure _).prod (O.law : Measure _)
  have hconst := funext h
  change Integrable _ μ ∧ (∫ w, ‖F (execute O (algorithm p) (budget p) w.1 w.2)‖ ∂μ) ≤ p.ε
  rw [hconst]
  refine ⟨integrable_const _, ?_⟩
  simpa [μ] using (show c ≤ p.ε from accuracy p hp F hc hreg z hz hm)

end LongTails.Theorems.GeneralizedMintyExtragradient
