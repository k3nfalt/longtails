import LongTails.Proofs.BrightnessLogisticField

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticSaturation

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticForces BrightnessLogisticRawDynamics
open BrightnessLogisticConstants BrightnessLogisticField BrightnessLogisticEnergy

lemma mass_bound (p : Params) (hp : Valid p) : p.μ ≤ p.D := by
  apply hp.positiveMass.trans
  rw [← mean_const (n := p.n) p.D]
  apply mean_mono
  intro i
  split
  · exact (le_abs_self _).trans (hp.maxDC i)
  · exact dc_nonneg p hp

lemma saturated_gap (p : Params) (hp : Valid p) (x : State (Features p.d)) (hE : size x ≤ p.B)
    (hδ : p.δ < min (|x.a|) (|x.q|)) (i : Fin p.n) :
    |p.dc i*weights p x i-(if p.dc i*(x.a*x.q)<0 then p.dc i else 0)| ≤ p.μ/2 := by
  by_cases hz : p.dc i = 0
  · simp [hz]
    linarith [hp.massPos]
  let y := Real.sqrt 2*p.R*p.dc i*x.a*x.q
  have hR := zero_lt_one.trans_le hp.scale
  have hμ := hp.massPos
  have hD := hp.massPos.trans_le (mass_bound p hp)
  have hL : 0 ≤ Real.log (2*p.D/p.μ) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hp.massPos).mpr
    linarith [mass_bound p hp]
  have hJ := zero_le_one.trans hp.forcePos
  have hB := zero_le_one.trans (energy_bound p hp)
  have htwo : (1:ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hrad := (radius_pos p hp).le
  have hy : p.R*p.m*p.δ^2 ≤ |y| := by
    have h1 := mul_le_mul (hδ.le.trans (min_le_left _ _)) (hδ.le.trans (min_le_right _ _))
      hrad (abs_nonneg x.a)
    have h2 := mul_le_mul (hp.minDC i hz) h1 (mul_nonneg hrad hrad) (abs_nonneg _)
    have h3 := mul_le_mul (show p.R ≤ Real.sqrt 2*p.R by nlinarith [mul_le_mul_of_nonneg_right htwo hR.le])
      h2 (mul_nonneg hp.dcPos.le (mul_nonneg hrad hrad)) (mul_nonneg (Real.sqrt_nonneg _) hR.le)
    simp only [y,abs_mul,abs_of_pos hR,abs_of_nonneg (Real.sqrt_nonneg 2)]
    nlinarith only [h3]
  obtain ⟨ha,ht,_,hv⟩ := sizes x.a x.t x.q x.z
  have hc := centered_work x.a x.t (Real.sqrt (size x)) (p.plus i) (p.minus i) x.z ha ht hv
  rw [Real.sq_sqrt (zero_le_one.trans (size_one x))] at hc
  have hslow := hc.trans (mul_le_mul (hp.radius i) hE (zero_le_one.trans (size_one x)) hJ)
  have hclose : |scores p x i-y| ≤ |y|/2 := by
    rw [show scores p x i-y=x.a*⟪p.plus i,x.z⟫+x.t*⟪p.minus i,x.z⟫ by dsimp [scores,y]; ring]
    linarith [hp.saturation]
  have hh := soft_hard_gap (η := 1) zero_lt_one (y := y) (le_refl |y|) hclose
  have hfactor : 0 < Real.sqrt 2*p.R := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR
  have hym : y < 0 ↔ p.dc i*(x.a*x.q)<0 := by
    rw [show y=(Real.sqrt 2*p.R)*(p.dc i*(x.a*x.q)) by dsimp [y]; ring]
    simp [mul_neg_iff,hfactor,not_lt_of_gt hfactor]
  simp only [one_mul,hym] at hh
  have hex : Real.exp (-(|y|/2)) ≤ p.μ/(2*p.D) := by
    apply (Real.exp_le_exp.mpr (show -(|y|/2) ≤ -Real.log (2*p.D/p.μ) by
      linarith [hp.saturation,mul_nonneg hJ hB])).trans
    rw [Real.exp_neg,Real.exp_log (by positivity : 0 < 2*p.D/p.μ)]
    simp
  have hmask := hh.trans hex
  rw [show (if p.dc i*(x.a*x.q)<0 then p.dc i else 0)=p.dc i*(if p.dc i*(x.a*x.q)<0 then 1 else 0)
    by split <;> simp,← mul_sub,abs_mul]
  apply (mul_le_mul (hp.maxDC i) hmask (abs_nonneg _) hD.le).trans
  apply le_of_eq
  field_simp

lemma beta_lower (p : Params) (hp : Valid p) (x : State (Features p.d)) (hE : size x ≤ p.B)
    (hδ : p.δ < min (|x.a|) (|x.q|)) : p.κ*p.μ/2 ≤ |beta p x| := by
  let y := x.a*x.q
  let G := mean (fun i => p.dc i*weights p x i)
  let H := mean (fun i => if p.dc i*y < 0 then p.dc i else 0)
  have hgap : |G-H| ≤ p.μ/2 := by
    unfold G H
    rw [mean_sub]
    exact mean_abs_bound _ (saturated_gap p hp x hE hδ)
  have hpos := radius_pos p hp
  have h1 := hδ.trans_le (min_le_left _ _)
  have h2 := hδ.trans_le (min_le_right _ _)
  have hne : y ≠ 0 := mul_ne_zero (abs_pos.mp (hpos.trans h1)) (abs_pos.mp (hpos.trans h2))
  have hbig : p.μ ≤ |H| := by
    rcases lt_or_gt_of_ne hne with hy | hy
    · have he : H=mean (fun i => if 0 < p.dc i then p.dc i else 0) := by
        simp only [H,mul_neg_iff,hy,not_lt_of_gt hy,and_true,and_false,or_false]
      rw [he]
      exact hp.positiveMass.trans (le_abs_self _)
    · have he : -H=mean (fun i => if p.dc i < 0 then -p.dc i else 0) := by
        simp only [H,mul_neg_iff,hy,not_lt_of_gt hy,and_true,and_false,false_or,mean]
        rw [← mul_neg,← Finset.sum_neg_distrib]
        congr 2
        funext i
        split <;> simp
      exact (he ▸ hp.negativeMass).trans (neg_le_abs H)
  have haux := abs_sub_abs_le_abs_sub H G
  rw [abs_sub_comm H G] at haux
  have hG : p.μ/2 ≤ |G| := by linarith
  rw [beta_eq p hp x,abs_mul,abs_of_nonneg (mul_nonneg (step_scale p hp).1.le (Real.sqrt_nonneg _))]
  have htwo : 1 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hh := mul_le_mul (show p.κ ≤ p.κ*Real.sqrt 2 by
    nlinarith [mul_le_mul_of_nonneg_left htwo (step_scale p hp).1.le]) hG
    (by linarith [hp.massPos]) (mul_nonneg (step_scale p hp).1.le (Real.sqrt_nonneg _))
  change p.κ*p.μ/2 ≤ p.κ*Real.sqrt 2*|G|
  linarith

end LongTails.Proofs.BrightnessLogisticSaturation
