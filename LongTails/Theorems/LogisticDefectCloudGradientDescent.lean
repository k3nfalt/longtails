import LongTails.Setups.LogisticDefectCloud
import LongTails.Proofs.LogisticCloudSeparation

open MeasureTheory ProbabilityTheory
open LongTails.Setups.LogisticDefectCloud
open LongTails.Algorithms.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudInitialization
open LongTails.Proofs.LogisticCloudExecution
open LongTails.Proofs.LogisticCloudEntry
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudSeparation

namespace OracleTemplate.LogisticDefectCloudGradientDescent

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  2 * (p.n : ℕ) * (⌈2^58 * (1+p.a/p.μ) * Real.log (1/(p.r*Real.sqrt p.L))⌉₊ + 1)

theorem result : Convergence LongTails.Setups.LogisticDefectCloud.spec budget := by
  refine ⟨fun p => algorithm p (rate p/p.L),?_,?_⟩
  · intro p hp D O hO
    change Params at p
    change Data p at D
    change Oracle (Query p) (Reply p.d) at O
    obtain ⟨⟨G⟩,hO⟩ := hO
    let η := rate p/p.L
    let K := ⌈2^58*(1+p.a/p.μ)*Real.log (1/radius p)⌉₊
    let P := (stdGaussian (Weights p.d)).prod (O.law : Measure ((k : ℕ) → O.Seed k))
    let bad := {g : Weights p.d | ¬Good (probes G).1 (probes G).2 p.ρ g}
    change P {ω | ¬Separates D
      (execute O (algorithm p η) (fun _ => 2*(p.n:ℕ)*(K+1)) ω.1 ω.2)} ≤ ENNReal.ofReal p.ρ
    calc
      _ ≤ P (bad ×ˢ Set.univ) := by
        apply measure_mono
        intro ω h
        refine ⟨?_,Set.mem_univ _⟩
        intro hg
        obtain ⟨k,hk,hs⟩ := reaches G hp ω.1 hg
        apply h
        rw [Nat.mul_comm (2*(p.n:ℕ)) (K+1)]
        exact hits_output D η O (fun h q ξ => hO h (0,q) ξ) ω.1 ω.2 hk hs
      _ = stdGaussian _ bad := by simp [P,Measure.prod_prod]
      _ ≤ _ := failure _ _ (unit_probes G hp).1 (unit_probes G hp).2 hp.2.2.2.2.2.2.1
  · intro p hp
    refine ⟨rate p/p.L,id,id,div_pos (scales p hp).hη hp.2.1,measurable_id,?_,
      fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩
    exact Measure.map_id

end OracleTemplate.LogisticDefectCloudGradientDescent
