import LongTails.Setups.HeavyTailedStrongGrowthConvex
import LongTails.Proofs.MultiplicativeAccelerationConvergence

open MeasureTheory

namespace OracleTemplate.SplitRobustHeavyTailedAcceleration

open LongTails.Setups.HeavyTailedStrongGrowthConvex
open SplitRobustAcceleration

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 130 * ⌈128 * Real.sqrt (max 1 (q.L * q.R^2 / q.ε))⌉₊ + 2 * ⌈(17179869184 * q.ρ)^(1 / (q.p - 1))⌉₊ * (130 + ⌈2 * Real.log (max 1 (q.L * q.R^2 / q.ε))⌉₊) * ⌈128 * (max 1 (q.L * q.R^2 / q.ε))^(q.p / (3 * q.p - 2))⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedStrongGrowthConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨hL, hR, hρ, hp, hp2, hε⟩
  rcases ho with ⟨g, μ, P, hIID, rfl, hc, hg, hlip, ⟨u, hm, hinit⟩, hmoment⟩
  have ha := lastIterate_accuracy q hL hR hρ hp hp2 hε hc hg hlip
    (μ : Measure _) P hIID hmoment u hm hinit
  have hB : calls q ≤ budget q 0 := calls_bound q hρ hp
  let O : Oracle q.E q.E :=
    {Seed := fun _ => q.Ω, law := P, answer := fun _ (_,x) ω => g x ω}
  have he : (fun seed : Unit × (ℕ → q.Ω) =>
      execute O (algorithm q) (fun _ => budget q 0) seed.1 seed.2) =
      fun seed => lastIterate q O seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_algorithm q P g (budget q 0) hB ξ
  change Measurable (fun seed : Unit × (ℕ → q.Ω) =>
      execute O (algorithm q) (fun _ => budget q 0) seed.1 seed.2) ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      Integrable (fun seed : Unit × (ℕ → q.Ω) =>
        f (execute O (algorithm q) (fun _ => budget q 0) seed.1 seed.2)-f xstar)
        ((Measure.dirac ()).prod (P : Measure _)) ∧
      (∫ seed : Unit × (ℕ → q.Ω),
        f (execute O (algorithm q) (fun _ => budget q 0) seed.1 seed.2)-f xstar
        ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε
  have hepoint (seed : Unit × (ℕ → q.Ω)) :
      execute O (algorithm q) (fun _ => budget q 0) seed.1 seed.2 = lastIterate q O seed.2 :=
    congrFun he seed
  simp_rw [hepoint]
  refine ⟨ha.1.comp measurable_snd, u, hm, ?_, ?_⟩
  · have hi : Integrable (fun ξ : ℕ → q.Ω => f (lastIterate q O ξ)-f u)
        (P : Measure (ℕ → q.Ω)) := ha.2.1
    exact (measurePreserving_snd (μ := Measure.dirac ())
      (ν := (P : Measure (ℕ → q.Ω)))).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ => f (lastIterate q O ξ)-f u)]
    simpa using ha.2.2

end OracleTemplate.SplitRobustHeavyTailedAcceleration
