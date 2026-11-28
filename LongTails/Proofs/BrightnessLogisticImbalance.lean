import LongTails.Proofs.BrightnessLogisticResidence

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticImbalance

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticConstants BrightnessLogisticField
open BrightnessLogisticHorizon BrightnessLogisticResidence

noncomputable def gap (x : State (Features d)) := x.a^2-x.q^2

lemma error_step (p : Params) (hp : Valid p) (x : State (Features p.d)) (hE : size x ≤ p.B) :
    max (-(gap (step p x))) 0 ≤ (1-(beta p x)^2)*max (-(gap x)) 0+
      (2*p.J*Real.sqrt p.B)*(tick p x*smaller x+tick p x*p.δ+tick p x*velocity p x) := by
  let h := p.κ/p.R
  let e := h*⟪force (weights p x) p.plus,x.z⟫
  let S := Real.sqrt p.B
  let β := beta p x
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hJ := zero_le_one.trans hp.forcePos
  have hB := zero_le_one.trans (energy_bound p hp)
  have hsS : S^2=p.B := Real.sq_sqrt hB
  have hb := cap_half p hp x
  have htick := tick_range p hp x
  have hβ2 : β^2 ≤ 1/4 := by
    nlinarith only [mul_self_le_mul_self (abs_nonneg (beta p x)) hb,sq_abs (beta p x),
      show β=beta p x from rfl]
  have hβ : β^2 ≤ 1 := by linarith
  have he : |e| ≤ tick p x*(p.J*S) := by
    exact (increments p hp x).1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hJ) htick.1)
  obtain ⟨ha,_,hq,_⟩ := bounded_state p hE
  have hsum : |x.a+β*x.q| ≤ 2*S := by
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have hh := mul_le_mul hb hq (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    change |β| * |x.q| ≤ 1/2*S at hh
    change |x.a| ≤ S at ha
    linarith
  have he' := he.trans (mul_le_mul_of_nonneg_right htick.2 (mul_nonneg hJ hS))
  have hcost : 2*|x.a+β*x.q| * |e| ≤ (1-β^2)*p.δ^2 := by
    have hpr := mul_le_mul hsum he' (abs_nonneg _) (by positivity)
    have hlim := hp.imbalance
    change h*(8*p.J*p.B) ≤ p.δ^2 at hlim
    have hid : 2*S*(h*(p.J*S))=2*h*p.J*p.B := by rw [← hsS]; ring
    change |x.a+β*x.q| * |e| ≤ 2*S*(h*(p.J*S)) at hpr
    rw [hid] at hpr
    nlinarith only [hpr,hlim,mul_le_mul_of_nonneg_right hβ2 (sq_nonneg p.δ),sq_nonneg p.δ]
  have hh := BrightnessLogisticOccupation.imbalance_charge (radius_pos p hp).le hβ he hcost
  change max (-((x.a+h*(dcForce p x*x.q+⟪force (weights p x) p.plus,x.z⟫))^2-
    (x.q+β*x.a)^2)) 0 ≤ _
  rw [show x.a+h*(dcForce p x*x.q+⟪force (weights p x) p.plus,x.z⟫) =
    x.a+β*x.q+e by dsimp [β,beta,h,e]; ring]
  apply hh.trans
  apply le_of_eq
  dsimp only [smaller,velocity,gap,β,S]
  ring

lemma sum_error (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    ∑ j ∈ Finset.range K, (beta p (orbit p j))^2*max (-(gap (orbit p j))) 0 ≤ p.t^2+1 := by
  let S := Real.sqrt p.B
  let Z := 2*p.J*S
  let u := fun j => tick p (orbit p j)
  let lo := fun j => smaller (orbit p j)
  let v := fun j => velocity p (orbit p j)
  obtain ⟨hE,_⟩ := bounds p hp K hf hm
  have hs := BrightnessLogisticFastMode.sum_discounted_imbalance (fun j => gap (orbit p j))
    (fun j => beta p (orbit p j)) (fun j => Z*(u j*lo j+u j*p.δ+u j*v j)) K (by
      intro j hj
      rw [next]
      exact error_step p hp _ (hE j hj.le))
  have hS : 0 < S := Real.sqrt_pos.mpr (zero_lt_one.trans_le (energy_bound p hp))
  have hJ := zero_lt_one.trans_le hp.forcePos
  have hM := horizon p hp
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hδ := (radius_pos p hp).le
  have hfirst := smaller_charge p hp K hf hm
  have hlast := velocity_charge p hp K hf hm
  change (∑ j ∈ Finset.range K,u j*lo j) ≤ _ at hfirst
  change (∑ j ∈ Finset.range K,u j*v j) ≤ _ at hlast
  have hcenter := mul_le_mul_of_nonneg_right hm hδ
  change (∑ j ∈ Finset.range K,u j)*p.δ ≤ _ at hcenter
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.sum_mul] at hs
  have hsum : (∑ j ∈ Finset.range K,u j*lo j)+(∑ j ∈ Finset.range K,u j)*p.δ+
      (∑ j ∈ Finset.range K,u j*v j) ≤ 5*p.δ*(p.M+1) := by linarith
  have hprice := mul_le_mul_of_nonneg_left hsum hZ
  have hone : Z*(5*p.δ*(p.M+1)) ≤ 1 := by
    dsimp [Z,S,Params.δ]
    have hm1 : p.M+1 ≠ 0 := by linarith
    field_simp [hJ.ne',(show Real.sqrt p.B ≠ 0 from hS.ne'),hm1]
    nlinarith [hM]
  have hR := zero_lt_one.trans_le hp.scale
  have hq : |p.t/p.R| ≤ |p.t| := by
    rw [abs_div,abs_of_pos hR,div_le_iff₀ hR]
    nlinarith only [mul_le_mul_of_nonneg_left hp.scale (abs_nonneg p.t)]
  have h0 : max (-(gap (orbit p 0))) 0 ≤ p.t^2 := by
    change max (-(p.p₀^2-(p.t/p.R)^2)) 0 ≤ _
    have hh := mul_self_le_mul_self (abs_nonneg _) hq
    apply max_le _ (sq_nonneg _)
    nlinarith only [hh,sq_abs (p.t/p.R),sq_abs p.t,sq_nonneg p.p₀]
  linarith only [hs,h0,hprice,hone,le_max_right (-(gap (orbit p K))) 0]

end LongTails.Proofs.BrightnessLogisticImbalance
