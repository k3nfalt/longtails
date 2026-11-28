import LongTails.Proofs.BrightnessLogisticHorizon
import LongTails.Proofs.BrightnessLogisticResidence
import LongTails.Proofs.BrightnessLogisticInteraction

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean vote)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticDifference

open ManySampleConvolutionalPerceptronDynamics (State)
open BrightnessLogisticModes BrightnessLogisticField BrightnessLogisticHorizon
open BrightnessLogisticConstants BrightnessLogisticForces BrightnessLogisticResidence
open BrightnessLogisticInteraction BrightnessLogisticRawDynamics

noncomputable def part (p : Params) : ℕ → Features p.d
  | 0 => p.a
  | k+1 => let x := orbit p k
           part p k+(p.κ/p.R) • (x.t • force (weights p x) p.minus)

noncomputable def rest (p : Params) (k : ℕ) := (orbit p k).z-part p k

noncomputable def χ (p : Params) := p.g^2/(2*p.B*(p.M+1)^2)

noncomputable def penalty (p : Params) := 2*χ p*p.B*(p.M+1)+(p.κ/p.R)*p.J^2*p.B

lemma rest_update (p : Params) (k : ℕ) : rest p (k+1)=rest p k+
    (p.κ/p.R) • ((orbit p k).a • force (weights p (orbit p k)) p.plus) := by
  unfold rest
  rw [BrightnessLogisticHorizon.next]
  simp only [step,part,smul_add]
  abel

lemma penalty_cost (p : Params) (hp : Valid p) : penalty p*(p.M+1) ≤ 2*p.g^2 := by
  have hB := zero_lt_one.trans_le (energy_bound p hp)
  have hT : 0 < p.M+1 := by linarith [horizon p hp]
  have h1 : 2*χ p*p.B*(p.M+1)*(p.M+1)=p.g^2 := by
    dsimp [χ]
    field_simp
  have hk := hp.kinetic.trans (min_le_right _ _)
  have h2 := mul_nonneg (step_size p hp).1.le (mul_nonneg (sq_nonneg p.J) (mul_nonneg hB.le hT.le))
  dsimp [penalty]
  nlinarith only [h1,hk,h2]

lemma nonneg_penalty (p : Params) (hp : Valid p) : 0 ≤ penalty p := by
  have hB := energy_bound p hp
  have hM := horizon p hp
  have hh := (step_size p hp).1.le
  dsimp [penalty,χ]
  positivity

lemma rest_lower (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1)
    (j : ℕ) (hj : j ≤ K) :
    -(χ p * Real.sqrt p.B*(p.M+1))*mean (weights p (orbit p j)) ≤
      ⟪rest p j,force (weights p (orbit p j)) p.minus⟫ := by
  let S := Real.sqrt p.B
  have hB := zero_lt_one.trans_le (energy_bound p hp)
  have hχ : 0 ≤ χ p := by dsimp [χ]; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hden : 0 < 2*p.B*(p.M+1)^2 := by have hM := horizon p hp; positivity
  apply support_force _ (fun i => (confidence _).1)
  intro i
  have h := cross_prefix (fun k => weights p (orbit p k)) p.plus p.minus (rest p)
    (fun k => (orbit p k).a) (step_size p hp).1.le j (fun k i => (confidence _).1)
    (fun k hk => (bounded_state p ((bounds p hp K hf hm).1 k (hk.le.trans hj))).1)
    (rest_update p) (χ := χ p) (by
      intro l r
      rw [real_inner_comm,χ,le_div_iff₀ hden]
      nlinarith only [hp.cross r l])
    (by intro l; exact hp.initialCross l) i
  change -(χ p*S*clock p j) ≤ _ at h
  exact (neg_le_neg (mul_le_mul_of_nonneg_left ((clock_mono p hp hj).trans hm)
    (mul_nonneg hχ hS))).trans h

lemma balance_step (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K) (hm : clock p K ≤ p.M+1)
    (j : ℕ) (hj : j < K) (hsign : 0 ≤ (orbit p j).t) :
    -(penalty p*tick p (orbit p j)) ≤
      ((orbit p (j+1)).t^2-‖part p (j+1)‖^2)-((orbit p j).t^2-‖part p j‖^2) := by
  let x := orbit p j
  let h := p.κ/p.R
  let S := Real.sqrt p.B
  let Q := mean (weights p x)
  let m := tick p x
  let V := force (weights p x) p.minus
  let w := part p j
  let b := rest p j
  have hz : w+b=x.z := by dsimp [w,b,rest,x]; abel
  have hB := zero_lt_one.trans_le (energy_bound p hp)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S^2=p.B := Real.sq_sqrt hB.le
  have hQ : 0 ≤ Q := (votes_range p x).1
  have hχ : 0 ≤ χ p := by dsimp [χ]; positivity
  have hJ := zero_le_one.trans hp.forcePos
  have hT : 0 ≤ p.M+1 := by linarith [horizon p hp]
  have hh : 0 ≤ h := (step_size p hp).1.le
  have ht := tick_range p hp x
  have hm0 : 0 ≤ m := ht.1
  have hE := (bounds p hp K hf hm).1 j hj.le
  have hq := (bounded_state p hE).2.1
  have hqS : x.t ≤ S := (le_abs_self _).trans hq
  have hrest := rest_lower p hp K hf hm j hj.le
  change -(χ p*S*(p.M+1))*Q ≤ ⟪b,V⟫ at hrest
  have hprod : -(χ p*p.B*(p.M+1)*Q) ≤ x.t*⟪b,V⟫ := by
    have hc := mul_le_mul_of_nonneg_left hrest hsign
    have hc' := mul_le_mul_of_nonneg_right hqS (mul_nonneg (mul_nonneg (mul_nonneg hχ hS) hT) hQ)
    have hid : S*(χ p*S*(p.M+1)*Q)=χ p*p.B*(p.M+1)*Q := by rw [← hS2]; ring
    rw [hid] at hc'
    nlinarith only [hc,hc']
  have hV : ‖V‖ ≤ p.J*Q := by
    have hc := force_budget p hp x
    change ‖_‖+‖V‖ ≤ _ at hc
    linarith [norm_nonneg (force (weights p x) p.plus)]
  have h1 : h*(x.t*‖V‖) ≤ m*(p.J*S) := by
    change _ ≤ (h*Q)*(p.J*S)
    have hc := mul_le_mul hqS hV (norm_nonneg _) hS
    nlinarith only [mul_le_mul_of_nonneg_left hc hh]
  have h2 : (h*(x.t*‖V‖))^2 ≤ h*m*p.J^2*p.B := by
    have hh' := mul_self_le_mul_self (mul_nonneg hh (mul_nonneg hsign (norm_nonneg V))) h1
    have htime : m ≤ h := ht.2
    have price := mul_le_mul_of_nonneg_right htime (mul_nonneg hm0 (mul_nonneg (sq_nonneg p.J) hB.le))
    have hid : (m*(p.J*S))*(m*(p.J*S))=m*(m*(p.J^2*p.B)) := by rw [← hS2]; ring
    rw [hid] at hh'
    nlinarith only [hh',price]
  have hs := balance x.t h w b V
  dsimp only at hs
  rw [hz] at hs
  rw [BrightnessLogisticHorizon.next]
  change -(penalty p*m) ≤ (x.t+h*⟪V,x.z⟫)^2-‖w+h • (x.t • V)‖^2-(x.t^2-‖w‖^2)
  rw [hs]
  change -((2*χ p*p.B*(p.M+1)+h*p.J^2*p.B)*(h*Q)) ≤ _
  change _ ≤ h*(h*Q)*p.J^2*p.B at h2
  nlinarith only [mul_le_mul_of_nonneg_left hprod hh,h2,mul_nonneg (sq_nonneg h) (sq_nonneg ⟪V,x.z⟫)]

end LongTails.Proofs.BrightnessLogisticDifference
