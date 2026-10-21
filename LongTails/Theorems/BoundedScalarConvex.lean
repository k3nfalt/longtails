import LongTails.Setups.BoundedScalarConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.ScalarSgd
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈25 * q.H ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.BoundedScalarConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => scalarSgd q.lower q.upper (q.ε/(25*q.H^2)) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ha
  have hJoint := ha.2.2.2.1
  let η := q.ε/(25*q.H^2)
  let K := max 1 ⌈25*q.H^2*q.R^2/q.ε^2⌉₊
  have hη : 0 < η := by dsimp [η]; positivity [hq.2.1, hq.2.2.2.1]
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨xstar, hxstar, hmin, hi, hr⟩ :=
    scalar_sgd_rate hq ha hη K hK
  have he : (∫ ω, f (scalarIterate O q.lower q.upper η q.x0 K ω)-f xstar
      ∂(O.law : Measure _)) ≤ q.ε := hr.trans (scalar_tuning hq.2.1 hq.2.2.2.1)
  let output := fun seed : Unit × Samples O =>
      (execute O (scalarSgd q.lower q.upper η q.x0) (fun _ => K) seed.1 seed.2)
  change Measurable output ∧ (∀ ω, output ω ∈ Set.Icc q.lower q.upper) ∧
    ∃ xstar ∈ Set.Icc q.lower q.upper, IsMinOn f (Set.Icc q.lower q.upper) xstar ∧
      Integrable (fun ω => f (output ω)-f xstar)
        ((Measure.dirac ()).prod (O.law : Measure _)) ∧
      (∫ ω, f (output ω)-f xstar ∂(Measure.dirac ()).prod (O.law : Measure _)) ≤ q.ε
  have hexec : output = fun seed => scalarIterate O q.lower q.upper η q.x0 K seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_scalarSgd O q.lower q.upper η q.x0 K ξ)
  rw [hexec]
  refine ⟨(scalarIterate_measurable O _ _ _ _ hJoint K).comp measurable_snd,
    (fun ω => scalarIterate_mem O hq.1 hq.2.2.2.2 K ω.2), xstar, hxstar, hmin, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := (O.law : Measure (Samples O)))).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ => f (scalarIterate O q.lower q.upper η q.x0 K ξ)-f xstar)]
    simpa using he

end OracleTemplate.BoundedScalarConvex
