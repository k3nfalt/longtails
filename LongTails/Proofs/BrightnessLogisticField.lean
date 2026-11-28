import LongTails.Proofs.BrightnessLogisticForces
import LongTails.Proofs.BrightnessLogisticConstants

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticField

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticForces BrightnessLogisticRawDynamics
open BrightnessLogisticConstants BrightnessLogisticEnergy

noncomputable def beta (p : Params) (x : State (Features p.d)) := p.κ/p.R*dcForce p x
noncomputable def tick (p : Params) (x : State (Features p.d)) := p.κ/p.R*mean (weights p x)
noncomputable def size (x : State (Features d)) := energy x.a x.t x.q x.z

lemma beta_eq (p : Params) (hp : Valid p) (x : State (Features p.d)) :
    beta p x=p.κ*Real.sqrt 2*mean (fun i => p.dc i*weights p x i) := by
  unfold beta dcForce
  field_simp [show p.R ≠ 0 from (zero_lt_one.trans_le hp.scale).ne']

lemma cap (p : Params) (hp : Valid p) (x : State (Features p.d)) :
    |beta p x| ≤ 1/(2*(1+p.J*p.B)) := by
  have hD := dc_nonneg p hp
  have hB := energy_bound p hp
  have hJ := hp.forcePos
  have hb : 0 < 1+p.J*p.B := by positivity
  have hbD : 0 < 1+p.D := by positivity
  have hd : |mean (fun i => p.dc i*weights p x i)| ≤ p.D := by
    apply mean_abs_bound
    intro i
    rw [abs_mul,weights,abs_of_nonneg (confidence _).1]
    exact (mul_le_mul_of_nonneg_left (confidence _).2 (abs_nonneg _)).trans (by simpa using hp.maxDC i)
  rw [beta_eq p hp x,abs_mul,abs_of_nonneg (mul_nonneg (step_scale p hp).1.le (Real.sqrt_nonneg 2))]
  apply (mul_le_mul_of_nonneg_left hd (mul_nonneg (step_scale p hp).1.le (Real.sqrt_nonneg 2))).trans
  have htwo : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  rw [Params.κ]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right htwo hD,hD]

lemma cap_half (p : Params) (hp : Valid p) (x : State (Features p.d)) : |beta p x| ≤ 1/2 := by
  apply (cap p hp x).trans
  have hJ := hp.forcePos
  have hB := energy_bound p hp
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [mul_nonneg (by linarith : 0 ≤ p.J) (by linarith : 0 ≤ p.B)]

lemma increments (p : Params) (hp : Valid p) (x : State (Features p.d)) :
    let h := p.κ/p.R
    let U := force (weights p x) p.plus
    let V := force (weights p x) p.minus
    let E := size x
    |h*⟪U,x.z⟫| ≤ tick p x*(p.J*Real.sqrt E) ∧
      |h*⟪V,x.z⟫| ≤ tick p x*(p.J*Real.sqrt E) ∧
      ‖h • (x.a • U+x.t • V)‖ ≤ tick p x*(p.J*Real.sqrt E) := by
  dsimp only
  let U := force (weights p x) p.plus
  let V := force (weights p x) p.minus
  let S := Real.sqrt (size x)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hn := force_budget p hp x
  change ‖U‖+‖V‖ ≤ _ at hn
  obtain ⟨hA,hq,_,hv⟩ := sizes x.a x.t x.q x.z
  change |x.a| ≤ S at hA
  change |x.t| ≤ S at hq
  change ‖x.z‖ ≤ S at hv
  have hh := (step_size p hp).1.le
  have hu : ‖U‖ ≤ p.J*mean (weights p x) := by linarith [norm_nonneg V]
  have hV : ‖V‖ ≤ p.J*mean (weights p x) := by linarith [norm_nonneg U]
  have dot (Y : Features p.d) (hy : ‖Y‖ ≤ p.J*mean (weights p x)) :
      |p.κ/p.R*⟪Y,x.z⟫| ≤ tick p x*(p.J*S) := by
    rw [abs_mul,abs_of_nonneg hh]
    have hd := (abs_real_inner_le_norm Y x.z).trans (mul_le_mul hy hv (norm_nonneg _) (hy.trans' (norm_nonneg _)))
    unfold tick
    nlinarith only [mul_le_mul_of_nonneg_left hd hh]
  refine ⟨dot U hu,dot V hV,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
  have hvv := norm_add_le (x.a • U) (x.t • V)
  simp only [norm_smul,Real.norm_eq_abs] at hvv
  have hv' : ‖x.a • U+x.t • V‖ ≤ p.J*mean (weights p x)*S := by
    nlinarith only [hvv,mul_le_mul_of_nonneg_right hA (norm_nonneg U),
      mul_le_mul_of_nonneg_right hq (norm_nonneg V),mul_le_mul_of_nonneg_right hn hS]
  unfold tick
  change _ ≤ _*(p.J*S)
  nlinarith only [mul_le_mul_of_nonneg_left hv' hh]

lemma size_one (x : State (Features d)) : 1 ≤ size x := by
  dsimp [size,energy,fast]
  linarith [sq_nonneg x.a,sq_nonneg x.q,sq_nonneg x.t,sq_nonneg ‖x.z‖,abs_nonneg (x.a^2-x.q^2)]

lemma tick_range (p : Params) (hp : Valid p) (x : State (Features p.d)) :
    0 ≤ tick p x ∧ tick p x ≤ p.κ/p.R := by
  have hh := (step_size p hp).1.le
  have hq := votes_range p x
  exact ⟨mul_nonneg hh hq.1,(mul_le_mul_of_nonneg_left hq.2 hh).trans_eq (mul_one _)⟩

lemma work (p : Params) (hp : Valid p) (x : State (Features p.d))
    (i : Fin p.n) (hi : scores p x i ≤ 0) :
    beta p x*x.a*x.q ≤ tick p x*(p.L+p.J)*size x := by
  let Q := mean (weights p x)
  let U := force (weights p x) p.plus
  let V := force (weights p x) p.minus
  let S := Real.sqrt (size x)
  have hE := size_one x
  have hS : S^2=size x := Real.sq_sqrt (zero_le_one.trans hE)
  obtain ⟨ha,ht,_,hv⟩ := sizes x.a x.t x.q x.z
  have hwork := BrightnessLogisticVotes.prefit_work (scores p x) i hi
  change mean (fun i => scores p x i*weights p x i) ≤ p.L*Q at hwork
  rw [work_identity] at hwork
  have hn := force_budget p hp x
  change ‖U‖+‖V‖ ≤ p.J*Q at hn
  have hc := (centered_work x.a x.t S U V x.z ha ht hv).trans
    (mul_le_mul_of_nonneg_right hn (sq_nonneg S))
  rw [hS] at hc
  have hneg := neg_abs_le (x.a*⟪U,x.z⟫+x.t*⟪V,x.z⟫)
  change x.a*x.q*dcForce p x+x.a*⟪U,x.z⟫+x.t*⟪V,x.z⟫ ≤ _ at hwork
  have hQ : 0 ≤ Q := (votes_range p x).1
  have hL : 0 ≤ p.L := zero_le_one.trans (log_bound p)
  have hh : x.a*x.q*dcForce p x ≤ Q*(p.L+p.J)*size x := by
    nlinarith only [hwork,hneg,hc,mul_le_mul_of_nonneg_left hE (mul_nonneg hL hQ)]
  change (p.κ/p.R*dcForce p x)*x.a*x.q ≤ (p.κ/p.R*Q)*(p.L+p.J)*size x
  nlinarith only [mul_le_mul_of_nonneg_left hh (step_size p hp).1.le]

lemma energy_step (p : Params) (hp : Valid p) (x : State (Features p.d))
    (i : Fin p.n) (hi : scores p x i ≤ 0) :
    size (BrightnessLogisticModes.step p x)+(beta p x)^2*(x.a^2+x.q^2) ≤
    (1+(6*p.L+22*p.J+5*p.J^2)*tick p x)*size x := by
  let h := p.κ/p.R
  let U := force (weights p x) p.plus
  let V := force (weights p x) p.minus
  obtain ⟨he,hf,hw⟩ := increments p hp x
  have hr := tick_range p hp x
  have hJ := zero_le_one.trans hp.forcePos
  have hL := zero_le_one.trans (log_bound p)
  have hs := BrightnessLogisticEnergy.step x.a x.t x.q (beta p x) (h*⟪U,x.z⟫) (h*⟪V,x.z⟫)
    (tick p x) p.J (p.L+p.J) x.z (h • (x.a • U+x.t • V)) (cap_half p hp x) hr.1
    (hr.2.trans (step_size p hp).2) hJ (add_nonneg hL hJ) (work p hp x i hi) he hf hw
  change energy (x.a+h*(dcForce p x*x.q+⟪U,x.z⟫)) (x.t+h*⟪V,x.z⟫)
    (x.q+beta p x*x.a) (x.z+h • (x.a • U+x.t • V))+_ ≤ _
  rw [show x.a+h*(dcForce p x*x.q+⟪U,x.z⟫) = x.a+beta p x*x.q+h*⟪U,x.z⟫ by
    dsimp [beta,h]; ring]
  unfold size
  convert hs using 1
  ring

end LongTails.Proofs.BrightnessLogisticField
