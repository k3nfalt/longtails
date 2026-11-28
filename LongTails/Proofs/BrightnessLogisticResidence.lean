import LongTails.Proofs.BrightnessLogisticHorizon
import LongTails.Proofs.BrightnessLogisticSaturation
import LongTails.Proofs.BrightnessLogisticOccupation

open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticResidence

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticHorizon BrightnessLogisticField
open BrightnessLogisticConstants BrightnessLogisticSaturation BrightnessLogisticOccupation

noncomputable def smaller (x : State (Features d)) := min (|x.a|) (|x.q|)

noncomputable def velocity (p : Params) (x : State (Features p.d)) := |beta p x*x.q|

lemma bounded_state (p : Params) {x : State (Features p.d)} (hs : size x ≤ p.B) :
    let S := Real.sqrt p.B
    |x.a| ≤ S ∧ |x.t| ≤ S ∧ |x.q| ≤ S ∧ ‖x.z‖ ≤ S := by
  obtain ⟨ha,ht,hq,hz⟩ := BrightnessLogisticEnergy.sizes x.a x.t x.q x.z
  have hh := Real.sqrt_le_sqrt hs
  exact ⟨ha.trans hh,ht.trans hh,hq.trans hh,hz.trans hh⟩

lemma smaller_charge (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    ∑ j ∈ Finset.range K, tick p (orbit p j)*smaller (orbit p j) ≤ 2*p.δ*(p.M+1) := by
  let h := p.κ/p.R
  let S := Real.sqrt p.B
  let b := p.κ*p.μ/2
  have hδ := radius_pos p hp
  have hκ := (step_scale p hp).1
  have hμ := hp.massPos
  have hb : 0 < b := by dsimp [b]; positivity
  have hden : 0 < b^2*p.δ^2 := by positivity
  have hh : 0 ≤ h := (step_size p hp).1.le
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  obtain ⟨hE,hK⟩ := bounds p hp K hf hm
  have hpoint (j : ℕ) (hj : j ∈ Finset.range K) :
      tick p (orbit p j)*smaller (orbit p j) ≤ tick p (orbit p j)*p.δ+
        (h*S/(b^2*p.δ^2))*((beta p (orbit p j))^2*((orbit p j).a^2+(orbit p j).q^2)) := by
    let x := orbit p j
    have hsize := hE j (Finset.mem_range.mp hj).le
    obtain ⟨ha,_,_,_⟩ := bounded_state p hsize
    have htime := tick_range p hp x
    exact charge_large hδ hb htime.1 htime.2 ((min_le_left _ _).trans ha)
      (beta_lower p hp x hsize)
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum] at hs
  change _ ≤ clock p K*p.δ+(h*S/(b^2*p.δ^2))*spending p K at hs
  have hpay : (h*S/(b^2*p.δ^2))*p.B ≤ p.δ := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have hh := hp.occupation
    change h*S*p.B ≤ b^2*p.δ^3 at hh
    nlinarith only [hh]
  have hm' := mul_le_mul_of_nonneg_right hm hδ.le
  have hc := mul_le_mul_of_nonneg_left hK (show 0 ≤ h*S/(b^2*p.δ^2) by positivity)
  nlinarith only [hs,hpay,hm',hc,mul_nonneg hδ.le (zero_le_one.trans (horizon p hp))]

lemma velocity_charge (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1) :
    ∑ j ∈ Finset.range K, tick p (orbit p j)*velocity p (orbit p j) ≤ 2*p.δ*(p.M+1) := by
  let h := p.κ/p.R
  have hh : 0 ≤ h := (step_size p hp).1.le
  have hδ := radius_pos p hp
  have ho := hp.imbalance
  have hB := energy_bound p hp
  have hJ := hp.forcePos
  have hcost : (h/p.δ)*p.B ≤ p.δ := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hδ]
    change h*(8*p.J*p.B) ≤ p.δ^2 at ho
    nlinarith only [ho,mul_le_mul_of_nonneg_right hJ (mul_nonneg hh (zero_le_one.trans hB)),
      mul_nonneg hh (zero_le_one.trans hB)]
  have hpoint (j : ℕ) (_hj : j ∈ Finset.range K) :
      tick p (orbit p j)*velocity p (orbit p j) ≤ tick p (orbit p j)*p.δ+
        (h/p.δ)*((beta p (orbit p j))^2*((orbit p j).a^2+(orbit p j).q^2)) := by
    let x := orbit p j
    have ht := tick_range p hp x
    apply (charge_velocity (x := beta p x*x.q) hδ ht.1 ht.2).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hh hδ.le)
    nlinarith only [mul_nonneg (sq_nonneg (beta p x)) (sq_nonneg x.a)]
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum] at hs
  change _ ≤ clock p K*p.δ+(h/p.δ)*spending p K at hs
  have hsp := (bounds p hp K hf hm).2
  nlinarith only [hs,hcost,mul_le_mul_of_nonneg_left hsp (div_nonneg hh hδ.le),
    mul_le_mul_of_nonneg_right hm hδ.le,mul_nonneg hδ.le (zero_le_one.trans (horizon p hp))]

end LongTails.Proofs.BrightnessLogisticResidence
