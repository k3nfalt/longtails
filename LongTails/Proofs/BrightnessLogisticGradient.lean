import LongTails.Proofs.BrightnessLogisticForces

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features Space direction)
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)

namespace LongTails.Proofs.BrightnessLogisticGradient

open ManySampleConvolutionalPerceptronDynamics (State)
open ManySampleConvolutionalPerceptronGeometry
open BrightnessLogisticModes BrightnessLogisticForces BrightnessLogisticRawDynamics

noncomputable def sumScore (p : Params) (x : State (Features p.d)) (i : Fin p.n) :=
  Real.sqrt 2*p.R*p.dc i*x.q+⟪p.plus i,x.z⟫

noncomputable def diffScore (p : Params) (x : State (Features p.d)) (i : Fin p.n) :=
  ⟪p.minus i,x.z⟫

lemma single (p : Params) (hp : Valid p) (x : State (Features p.d))
    (hz : ⟪axis p.d,x.z⟫ = 0) (i : Fin p.n) :
    direction .conv p.d (p.rows i) (decode 1 x) =
      (((sumScore p x i+diffScore p x i)/Real.sqrt 2,(sumScore p x i-diffScore p x i)/Real.sqrt 2),
      x.a • ((Real.sqrt 2*p.R*p.dc i) • axis p.d+p.plus i)+x.t • p.minus i) := by
  rw [direction_decode,plus_row,minus_row]
  simp only [decode,one_smul,inner_add_left,real_inner_smul_left,inner_add_right,
    real_inner_smul_right,plus_center p hp,minus_center p hp,
    hz,mul_zero,zero_add,add_zero,sumScore,diffScore]
  erw [ManySampleConvolutionalPerceptronGeometry.axis_inner (d := (p.d : ℕ)) p.d.property]
  simp
  ring

lemma sum_force (p : Params) (x : State (Features p.d)) :
    mean (fun i => weights p x i*sumScore p x i) =
      dcForce p x*x.q+⟪force (weights p x) p.plus,x.z⟫ := by
  rw [force_inner,dcForce]
  rw [show Real.sqrt 2*p.R*mean (fun i => p.dc i*weights p x i)*x.q =
    (Real.sqrt 2*p.R*x.q)*mean (fun i => p.dc i*weights p x i) by ring,← mean_scale,← mean_add]
  congr 1
  funext i
  unfold sumScore
  ring

lemma oriented_mean {n : ℕ+} (g a b : Fin n → ℝ) (s : ℝ) :
    mean (fun i => g i*((a i+s*b i)/Real.sqrt 2)) =
    (mean (fun i => g i*a i)+s*mean (fun i => g i*b i))/Real.sqrt 2 := by
  rw [← mean_scale,← mean_add,div_eq_inv_mul,← mean_scale]
  congr 1
  funext i
  ring

lemma vector_mean (p : Params) (x : State (Features p.d)) :
    force (weights p x) (fun i => x.a • ((Real.sqrt 2*p.R*p.dc i) • axis p.d+p.plus i)+x.t • p.minus i) =
    (dcForce p x*x.a) • axis p.d + (x.a • force (weights p x) p.plus+x.t • force (weights p x) p.minus) := by
  let g := weights p x
  have hh (i : Fin p.n) :
      g i • (x.a • ((Real.sqrt 2*p.R*p.dc i) • axis p.d+p.plus i)+x.t • p.minus i) =
      ((Real.sqrt 2*p.R*x.a)*(p.dc i*g i)) • axis p.d+
        (x.a • (g i • p.plus i)+x.t • (g i • p.minus i)) := by module
  change (p.n : ℝ)⁻¹ • ∑ i, g i • _ = _
  simp_rw [hh]
  simp only [Finset.sum_add_distrib,← Finset.sum_smul,← Finset.smul_sum,← Finset.mul_sum]
  unfold force dcForce mean
  change _ = ((Real.sqrt 2*p.R*((p.n : ℝ)⁻¹ * ∑ i, p.dc i*g i))*x.a) • axis p.d+
    (x.a • ((p.n : ℝ)⁻¹ • ∑ i, g i • p.plus i)+x.t • ((p.n : ℝ)⁻¹ • ∑ i, g i • p.minus i))
  module

lemma actual_step (p : Params) (hp : Valid p) (x : State (Features p.d))
    (hz : ⟪axis p.d,x.z⟫ = 0) :
    decode 1 (step p x) = decode 1 x+(p.κ/p.R) • (answer (u := p.input) p.rows (decode 1 x)).1 := by
  let g := weights p x
  let U := force g p.plus
  let V := force g p.minus
  let P := dcForce p x*x.q+⟪U,x.z⟫
  let Q := ⟪V,x.z⟫
  let h := p.κ/p.R
  let A := sumScore p x
  let B := diffScore p x
  have hP : mean (fun i => g i*A i)=P := sum_force p x
  have hQ : mean (fun i => g i*B i)=Q := (force_inner g p.minus x.z).symm
  have hf : mean (fun i => g i*((A i+B i)/Real.sqrt 2))=(P+Q)/Real.sqrt 2 := by
    simpa [hP,hQ] using oriented_mean g A B 1
  have hs : mean (fun i => g i*((A i-B i)/Real.sqrt 2))=(P-Q)/Real.sqrt 2 := by
    simpa [hP,hQ,sub_eq_add_neg] using oriented_mean g A B (-1)
  have hr := vector_mean p x
  simp only [answer,margin_eq p hp x hz,single p hp x hz]
  apply Prod.ext
  · apply Prod.ext
    · simp only [Prod.fst_add,Prod.smul_fst,Prod.fst_sum,smul_eq_mul]
      change ((x.a+h*P)+(x.t+h*Q))/Real.sqrt 2 =
        (x.a+x.t)/Real.sqrt 2+h*mean (fun i => g i*((A i+B i)/Real.sqrt 2))
      rw [hf]
      ring
    · simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.fst_sum,
        Prod.snd_sum,smul_eq_mul]
      change ((x.a+h*P)-(x.t+h*Q))/Real.sqrt 2 =
        (x.a-x.t)/Real.sqrt 2+h*mean (fun i => g i*((A i-B i)/Real.sqrt 2))
      rw [hs]
      ring
  · simp only [Prod.snd_add,Prod.smul_snd,Prod.snd_sum]
    change (x.q+h*dcForce p x*x.a) • axis p.d+(1:ℝ) • (x.z+h • (x.a • U+x.t • V)) =
      (x.q • axis p.d+(1:ℝ) • x.z)+h • force (weights p x) _
    rw [hr]
    change _ = (x.q • axis p.d+(1:ℝ) • x.z)+h • ((dcForce p x*x.a) • axis p.d+(x.a • U+x.t • V))
    module

end LongTails.Proofs.BrightnessLogisticGradient
