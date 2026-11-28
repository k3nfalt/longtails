import LongTails.Setups.BrightnessLogisticJoint
import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
import LongTails.Proofs.BrightnessLogisticVotes

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift Space margin direction)
open LongTails.Setups.ManySampleConvolutionalPerceptron (axis)

namespace LongTails.Proofs.BrightnessLogisticModes

open ManySampleConvolutionalPerceptronDynamics (State)
open ManySampleConvolutionalPerceptronGeometry
open TwoSampleQuadraticPerceptronEmbedding

noncomputable def scores (p : Params) (x : State (Features p.d)) (i : Fin p.n) :=
  Real.sqrt 2*p.R*p.dc i*x.a*x.q+
    x.a*⟪p.plus i,x.z⟫+x.t*⟪p.minus i,x.z⟫

noncomputable def weights (p : Params) (x : State (Features p.d)) (i : Fin p.n) :=
  vote (scores p x i)

noncomputable def force {d : ℕ} {n : ℕ+} (g : Fin n → ℝ) (Z : Fin n → Features d) :=
  (n : ℝ)⁻¹ • ∑ i, g i • Z i

noncomputable def dcForce (p : Params) (x : State (Features p.d)) :=
  Real.sqrt 2*p.R*mean (fun i => p.dc i*weights p x i)

noncomputable def step (p : Params) (x : State (Features p.d)) : State (Features p.d) :=
  let h := p.κ/p.R
  let g := weights p x
  let G := dcForce p x
  let U := force g p.plus
  let V := force g p.minus
  ⟨x.a + h*(G*x.q+⟪U,x.z⟫),x.q+h*G*x.a,x.t+h*⟪V,x.z⟫,x.z+h • (x.a • U+x.t • V)⟩

noncomputable def start (p : Params) : State (Features p.d) := ⟨p.p₀,p.t/p.R,p.q₀,p.w⟩

lemma start_decode (p : Params) : decode 1 (start p) = p.input.start := by
  change (((p.p₀+p.q₀)/Real.sqrt 2,(p.p₀-p.q₀)/Real.sqrt 2),
    (p.t/p.R) • axis p.d+(1 : ℝ) • p.w) = _
  unfold Params.p₀ Params.q₀ Params.input
  simp only [one_smul,add_comm ((p.t/p.R) • axis p.d) p.w]
  congr 2 <;> field_simp <;> rw [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)] <;> ring

lemma plus_row (p : Params) (i : Fin p.n) :
    plusFeature (p.rows i) = (Real.sqrt 2*p.R*p.dc i) • axis p.d + p.plus i := by
  simp only [plusFeature, Params.rows, Params.plus, shift_add, shift_smul, shift_axis, smul_add]
  match_scalars <;> field_simp
  simp [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  ring

lemma minus_row (p : Params) (i : Fin p.n) : minusFeature (p.rows i) = p.minus i := by
  simp only [minusFeature,Params.rows,Params.minus,shift_add,shift_smul,shift_axis]
  congr 1
  abel

lemma plus_center (p : Params) (hp : Valid p) (i : Fin p.n) :
    ⟪p.plus i,axis p.d⟫ = 0 := by
  rw [real_inner_comm]
  simp [Params.plus,inner_add_right,real_inner_smul_right,axis_shift_inner,hp.centered]

lemma minus_center (p : Params) (_hp : Valid p) (i : Fin p.n) :
    ⟪p.minus i,axis p.d⟫ = 0 := by
  rw [real_inner_comm]
  simp [Params.minus,inner_sub_right,real_inner_smul_right,axis_shift_inner]

lemma margin_eq (p : Params) (hp : Valid p) (x : State (Features p.d))
    (hz : ⟪axis p.d,x.z⟫ = 0) (i : Fin p.n) :
    margin .conv p.d (p.rows i) (decode 1 x) = scores p x i := by
  rw [margin_decode,plus_row,minus_row,inner_add_left,real_inner_smul_left]
  simp only [decode,one_smul,inner_add_right,real_inner_smul_right,plus_center p hp,minus_center p hp,
    hz,mul_zero,zero_add,add_zero,scores]
  erw [ManySampleConvolutionalPerceptronGeometry.axis_inner (d := (p.d : ℕ)) p.d.property]
  ring

lemma force_inner {d : ℕ} {n : ℕ+} (g : Fin n → ℝ) (Z : Fin n → Features d) (w : Features d) :
    ⟪force g Z,w⟫ = mean (fun i => g i*⟪Z i,w⟫) := by
  simp [force,mean,real_inner_smul_left,sum_inner]

lemma step_center (p : Params) (hp : Valid p) (x : State (Features p.d))
    (hz : ⟪axis p.d,x.z⟫ = 0) : ⟪axis p.d,(step p x).z⟫ = 0 := by
  have hu : ⟪axis p.d,force (weights p x) p.plus⟫ = 0 := by
    rw [real_inner_comm,force_inner]
    simp [mean,plus_center p hp]
  have hv : ⟪axis p.d,force (weights p x) p.minus⟫ = 0 := by
    rw [real_inner_comm,force_inner]
    simp [mean,minus_center p hp]
  simp [step,inner_add_right,real_inner_smul_right,hu,hv,hz]

end LongTails.Proofs.BrightnessLogisticModes
