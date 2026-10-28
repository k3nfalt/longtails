import LongTails.Setups.StochasticLipschitzMonotone
import LongTails.Proofs.InertialMonotoneAccuracy

open MeasureTheory OracleTemplate

namespace LongTails.Theorems.InertialMonotoneResidual

open LongTails.Setups.StochasticLipschitzMonotone
open OracleTemplate.InertialMonotone

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 22 * (1 + q.L * q.R / q.ε + (q.σ / q.ε) ^ 2 * (Real.log (2 + q.L * q.R / q.ε)) ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.StochasticLipschitzMonotone.spec budget := by
  refine ⟨fun q => inertialExtragradient q.L q.R q.σ q.ε q.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL, hR, hσ, hε⟩ F O ⟨g, p, P, hIID, rfl, hm, hlip, ⟨xs, hxs, hdist⟩, hg⟩
  let K := budget q 0
  have hK : calls (batchSize q.σ q.ε (horizon q.L q.R q.ε)) (horizon q.L q.R q.ε) ≤ K :=
    calls_public_bound hL.le hR hε
  let O : Oracle q.E q.E :=
    { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
  have ha := execution_accuracy q hL hR hε F hm hlip p P hIID g hg xs hxs hdist K hK
  let z := fun ξ => terminalPoint q.L q.R q.σ q.ε q.x0 O K ((), ξ)
  change Measurable (fun seed : Unit × (ℕ → q.Ω) =>
      execute O (inertialExtragradient q.L q.R q.σ q.ε q.x0) (fun _ => K) seed.1 seed.2) ∧
    Integrable (fun seed : Unit × (ℕ → q.Ω) =>
      ‖F (execute O (inertialExtragradient q.L q.R q.σ q.ε q.x0) (fun _ => K) seed.1 seed.2)‖ ^ 2)
      ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed : Unit × (ℕ → q.Ω),
      ‖F (execute O (inertialExtragradient q.L q.R q.σ q.ε q.x0) (fun _ => K) seed.1 seed.2)‖ ^ 2
      ∂(Measure.dirac ()).prod (P : Measure _)) ≤ q.ε ^ 2
  have he (seed : Unit × (ℕ → q.Ω)) :
      execute O (inertialExtragradient q.L q.R q.σ q.ε q.x0) (fun _ => K) seed.1 seed.2 = z seed.2 := by
    rcases seed with ⟨⟨⟩, ξ⟩
    rfl
  simp_rw [he]
  refine ⟨ha.1.comp measurable_snd, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → q.Ω)))).integrable_comp_of_integrable ha.2.1
  · rw [integral_fun_snd (fun ξ => ‖F (z ξ)‖ ^ 2)]
    simpa using ha.2.2

end LongTails.Theorems.InertialMonotoneResidual
