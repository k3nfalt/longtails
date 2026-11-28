import LongTails.Setups.BrightnessScaledTwoTap
import LongTails.Algorithms.BrightnessScaledTwoTap
import LongTails.Proofs.BrightnessFirstFitExecution
import LongTails.Proofs.BrightnessFirstFitConvergence

open OracleTemplate
open LongTails.Setups.BrightnessScaledTwoTap

namespace LongTails.Theorems.BrightnessScaledTwoTapFirstFit

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let a := max p.P (-p.P)
  let b := max p.Q (-p.Q)
  let U := p.J*(4+a+b)
  let Γ := min 1 (b * p.γ)/4
  let κ := Γ/(32*(1+p.D)*(1+U))
  let δ := Γ/(128*(1+p.J))
  let V := 6+Real.sqrt (Real.log (1+a/δ))
  let f := p.μ*Γ/(32*p.n*V*(1+U))
  let B := 1+(1+Real.log (4*(1+a)^2*p.R^2))/(κ*f)^2
  let M := 8*(1+‖p.readout‖+(1+U)/p.μ+(1+Real.log (2*p.n)+κ*U^2)/Γ)+κ*U*B
  ⌈32*p.n*V^2*M/(κ*Γ)⌉₊+1

theorem result : Convergence LongTails.Setups.BrightnessScaledTwoTap.spec budget := by
  let A (p : Params) := Algorithms.BrightnessScaledTwoTap.algorithm p ((scales p).κ/p.R)
  refine ⟨A,?_,?_⟩
  · intro p valid x oracle adm
    obtain ⟨G,hor⟩ := adm
    have fit := Proofs.BrightnessFirstFitConvergence.hit p x valid G
    have h := Proofs.BrightnessFirstFitParameters.tuning p valid
    change ∀ seed : Unit × ((k : ℕ) → oracle.Seed k), Fitted p x
      (execute oracle (A p) (fun _ => (scales p).H+1) seed.1 seed.2)
    rintro ⟨⟨⟩,ξ⟩
    obtain ⟨k,hk,hfit⟩ := fit
    exact Proofs.BrightnessFirstFitExecution.fitted_execute p x (scales p).κ
      (by linarith only [h.Rlarge]) oracle hor ξ ((scales p).H+1)
      ⟨k,by omega,hfit⟩
  · intro p valid
    have h := Proofs.BrightnessFirstFitParameters.tuning p valid
    change family p (A p)
    exact Proofs.BrightnessFirstFitExecution.allowed p ((scales p).κ/p.R) (div_pos h.κpos (by linarith only [h.Rlarge]))

end LongTails.Theorems.BrightnessScaledTwoTapFirstFit
