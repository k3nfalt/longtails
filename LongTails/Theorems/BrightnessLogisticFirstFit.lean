import LongTails.Setups.BrightnessLogisticJoint
import LongTails.Proofs.BrightnessLogisticFirstFit
import LongTails.Proofs.FirstFitGradientExecution

open OracleTemplate
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Algorithms.FirstFitGradientDescent

namespace LongTails.Theorems.BrightnessLogisticFirstFit

noncomputable def budget : (let S := LongTails.Setups.BrightnessLogisticJoint.spec
    S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let L := 1+Real.log (2*(p.n : ℝ))
  let K := 3*L+1
  let ν := p.γ*p.g
  let P := (p.taps.1+p.taps.2)/Real.sqrt 2
  let Q := (p.taps.1-p.taps.2)/Real.sqrt 2
  let I := ‖p.a‖+Real.sqrt (P^2+Q^2+2*p.t^2+3+K)
  let M := 1+2*I/ν+4*K/ν^2
  let F := 1+3*(P^2+p.t^2)+Q^2+‖p.w‖^2
  let B := F*Real.exp ((6*L+22*p.J+5*p.J^2)*(M+1))
  1+⌈8*(p.n : ℝ)*p.R*M*(1+p.D)*(1+p.J*B)⌉₊

theorem result : Convergence LongTails.Setups.BrightnessLogisticJoint.spec budget := by
  classical
  refine ⟨fun (u : Input) => algorithm (E := LongTails.Setups.TwoSampleQuadraticPerceptron.Space .conv u.d)
    u.start u.step,?_,?_⟩
  · intro (p : Params) hp X o ho
    obtain ⟨rfl,ho⟩ := ho
    obtain ⟨k,hk,hfit⟩ := LongTails.Proofs.BrightnessLogisticFirstFit.first_fit p hp
    dsimp only
    intro ω
    have hκ := (LongTails.Proofs.BrightnessLogisticConstants.step_scale p hp).1
    have hR := zero_lt_one.trans_le hp.scale
    have hb : k ≤ budget p (0 : Fin 1) := by
      change k ≤ 1+⌈8*(p.n : ℝ)*p.R*p.M*(1+p.D)*(1+p.J*p.B)⌉₊
      rw [show 2*(p.n : ℝ)*p.M/(p.κ/p.R)=8*(p.n : ℝ)*p.R*p.M*(1+p.D)*(1+p.J*p.B) by
        rw [Params.κ]
        field_simp
        ring] at hk
      omega
    let flag := fun z => decide (fits (u := p.input) p.rows z)
    have hs := LongTails.Proofs.FirstFitGradientExecution.execute_first_fit
      (fun z => (answer (u := p.input) p.rows z).1) flag o (fun history z ξ => ho history (0,z) ξ)
      p.input.step p.input.start hb (decide_eq_true hfit) ω.2
    exact of_decide_eq_true hs
  · intro p hp
    exact ⟨p.input.step,id,(LongTails.Proofs.BrightnessLogisticConstants.step_size p hp).1,
      fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

end LongTails.Theorems.BrightnessLogisticFirstFit
