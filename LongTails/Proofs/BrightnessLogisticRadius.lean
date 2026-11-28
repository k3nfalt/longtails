import LongTails.Proofs.BrightnessLogisticImbalance
import LongTails.Proofs.BrightnessLogisticTapWork

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticRadius

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticConstants BrightnessLogisticField
open BrightnessLogisticHorizon BrightnessLogisticResidence BrightnessLogisticImbalance
open BrightnessLogisticForces

noncomputable def taps (x : State (Features d)) := x.a^2+x.t^2

lemma step_radius (p : Params) (hp : Valid p) (x : State (Features p.d)) (i : Fin p.n)
    (hi : scores p x i ≤ 0) (hE : size x ≤ p.B) :
    taps (step p x)-taps x ≤ (3*p.L+1)*tick p x+
      2*((beta p x)^2*max (-(gap x)) 0)+(3*(p.κ/p.R)*p.J^2*p.B)*tick p x := by
  let m := tick p x
  let h := p.κ/p.R
  let U := force (weights p x) p.plus
  let V := force (weights p x) p.minus
  let e := h*⟪U,x.z⟫
  let f := h*⟪V,x.z⟫
  let β := beta p x
  let b := 1/(2*(1+p.J*p.B))
  let S := Real.sqrt p.B
  let Q := mean (weights p x)
  have hJ := zero_lt_one.trans_le hp.forcePos
  have hB := zero_lt_one.trans_le (energy_bound p hp)
  have hL := zero_le_one.trans (log_bound p)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S^2=p.B := Real.sq_sqrt hB.le
  have ht := tick_range p hp x
  have hm : 0 ≤ m := ht.1
  have hh : 0 ≤ h := (step_size p hp).1.le
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb : b ≤ 1/2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [mul_nonneg hJ.le hB.le]
  have hbJ : 2*b*(p.J*p.B) ≤ 1 := by
    dsimp [b]
    have hy : 0 < 1+p.J*p.B := by positivity
    field_simp
    linarith
  obtain ⟨ha,hq,_,hz⟩ := bounded_state p hE
  have hwork := BrightnessLogisticVotes.prefit_work (scores p x) i hi
  change mean (fun j => scores p x j*weights p x j) ≤ p.L*Q at hwork
  rw [work_identity] at hwork
  change x.a*x.q*dcForce p x+x.a*⟪U,x.z⟫+x.t*⟪V,x.z⟫ ≤ _ at hwork
  have hW : β*x.a*x.q+(x.a*e+x.t*f) ≤ m*p.L := by
    change (h*dcForce p x)*x.a*x.q+(x.a*(h*⟪U,x.z⟫)+x.t*(h*⟪V,x.z⟫)) ≤ (h*Q)*p.L
    nlinarith only [mul_le_mul_of_nonneg_left hwork hh]
  have hn := force_budget p hp x
  change ‖U‖+‖V‖ ≤ p.J*Q at hn
  have hc := centered_work x.a x.t S U V x.z ha hq hz
  rw [hS2] at hc
  have hslow : |x.a*e+x.t*f| ≤ m*p.J*p.B := by
    rw [show x.a*e+x.t*f=h*(x.a*⟪U,x.z⟫+x.t*⟪V,x.z⟫) by dsimp [e,f]; ring,
      abs_mul,abs_of_nonneg hh]
    change _ ≤ h*Q*p.J*p.B
    nlinarith only [mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_right hn hB.le)) hh]
  have hchg := BrightnessLogisticTapWork.tap_change (cap p hp x) (hb.trans (by norm_num))
    (mul_nonneg hm hL) hW hslow
  have hcoeff : (2+2*b)*(m*p.L)+2*b*(m*p.J*p.B) ≤ (3*p.L+1)*m := by
    nlinarith only [mul_le_mul_of_nonneg_right hb (mul_nonneg hm hL),
      mul_le_mul_of_nonneg_right hbJ hm]
  have hs (y : ℝ) (hy : |y| ≤ m*(p.J*Real.sqrt (size x))) : y^2 ≤ h*m*p.J^2*p.B := by
    have hsmall := hy.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hE) hJ.le) hm)
    change |y| ≤ m*(p.J*S) at hsmall
    have hsq := mul_self_le_mul_self (abs_nonneg y) hsmall
    have he := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hm (mul_nonneg (sq_nonneg p.J) hB.le))
    change m*(m*(p.J^2*p.B)) ≤ h*(m*(p.J^2*p.B)) at he
    have hid : (m*(p.J*S))*(m*(p.J*S))=m*(m*(p.J^2*p.B)) := by rw [← hS2]; ring
    rw [hid] at hsq
    nlinarith only [hsq,he,sq_abs y]
  have hinc := increments p hp x
  have he := hs e hinc.1
  have hf := hs f hinc.2.1
  change (x.a+h*(dcForce p x*x.q+⟪U,x.z⟫))^2+(x.t+f)^2-(x.a^2+x.t^2) ≤ _
  rw [show x.a+h*(dcForce p x*x.q+⟪U,x.z⟫)=x.a+β*x.q+e by dsimp [e,β,beta,h]; ring]
  change _ ≤ (3*p.L+1)*m+2*(β^2*max (-(x.a^2-x.q^2)) 0)+(3*h*p.J^2*p.B)*m
  change _ ≤ (2+2*b)*(m*p.L)+2*b*(m*p.J*p.B)+2*β^2*max (-(x.a^2-x.q^2)) 0+2*e^2+f^2 at hchg
  nlinarith only [hchg,hcoeff,he,hf]

lemma radius_bound (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    taps (orbit p K) ≤ p.p₀^2+p.q₀^2+(3*p.L+1)*(p.M+1)+2*p.t^2+3 := by
  let h := p.κ/p.R
  have hh : 0 ≤ h := (step_size p hp).1.le
  have hJ := zero_le_one.trans hp.forcePos
  have hB := zero_le_one.trans (energy_bound p hp)
  have hL := zero_le_one.trans (log_bound p)
  have hpt (j : ℕ) (hj : j ∈ Finset.range K) : taps (orbit p (j+1))-taps (orbit p j) ≤
      (3*p.L+1)*tick p (orbit p j)+2*((beta p (orbit p j))^2*max (-(gap (orbit p j))) 0)+
      (3*h*p.J^2*p.B)*tick p (orbit p j) := by
    have ht := Finset.mem_range.mp hj
    obtain ⟨i,hi⟩ := hf j ht
    rw [next]
    exact step_radius p hp _ i hi ((bounds p hp K hf hm).1 j ht.le)
  have hs := Finset.sum_le_sum hpt
  rw [Finset.sum_range_sub (fun j => taps (orbit p j)),Finset.sum_add_distrib,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum] at hs
  have he := sum_error p hp K hf hm
  change taps (orbit p K)-(p.p₀^2+p.q₀^2) ≤ (3*p.L+1)*clock p K+
    2*(∑ j ∈ Finset.range K,(beta p (orbit p j))^2*max (-(gap (orbit p j))) 0)+
    (3*h*p.J^2*p.B)*clock p K at hs
  have hc := hp.kinetic.trans (min_le_left _ _)
  change (p.κ/p.R)*(3*p.J^2*p.B*(p.M+1)) ≤ 1 at hc
  change h*(3*p.J^2*p.B*(p.M+1)) ≤ 1 at hc
  nlinarith only [hs,he,hc,mul_le_mul_of_nonneg_left hm (show 0 ≤ 3*p.L+1 by positivity),
    mul_le_mul_of_nonneg_left hm (show 0 ≤ 3*h*p.J^2*p.B by positivity)]

end LongTails.Proofs.BrightnessLogisticRadius
