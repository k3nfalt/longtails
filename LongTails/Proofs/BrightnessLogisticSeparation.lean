import LongTails.Proofs.BrightnessLogisticDifference
import LongTails.Proofs.BrightnessLogisticRadius

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticJoint
open LongTails.Setups.BrightnessLogisticRaw (mean)
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

namespace LongTails.Proofs.BrightnessLogisticSeparation

open BrightnessLogisticModes BrightnessLogisticField BrightnessLogisticHorizon
open BrightnessLogisticConstants BrightnessLogisticForces BrightnessLogisticResidence
open BrightnessLogisticInteraction BrightnessLogisticRawDynamics BrightnessLogisticDifference
open BrightnessLogisticRadius

lemma floor_and_balance (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K)
    (hm : clock p K ≤ p.M+1) : ∀ j ≤ K, p.g ≤ (orbit p j).t ∧
    4*p.g^2-penalty p*clock p j ≤ (orbit p j).t^2-‖part p j‖^2 := by
  intro j
  induction j with
  | zero =>
    intro _
    change p.g ≤ p.q₀ ∧ 4*p.g^2-penalty p*(∑ j ∈ Finset.range 0,_) ≤ p.q₀^2-‖p.a‖^2
    simp only [Finset.sum_range_zero,mul_zero,sub_zero]
    exact ⟨by nlinarith [hp.gap,hp.tap,hp.floorPos,sq_nonneg ‖p.a‖],hp.gap⟩
  | succ j ih =>
    intro hj
    have hj' := Nat.le_of_succ_le hj
    obtain ⟨hprev,hd⟩ := ih hj'
    have hx := balance_step p hp K hf hm j hj (hp.floorPos.le.trans hprev)
    have hclock : clock p (j+1)=clock p j+tick p (orbit p j) := Finset.sum_range_succ _ _
    have hnew : 4*p.g^2-penalty p*clock p (j+1) ≤ (orbit p (j+1)).t^2-‖part p (j+1)‖^2 := by
      rw [hclock]
      nlinarith only [hd,hx]
    have hpayed := (mul_le_mul_of_nonneg_left ((clock_mono p hp hj).trans hm)
      (nonneg_penalty p hp)).trans (penalty_cost p hp)
    let x := orbit p j
    let f := (p.κ/p.R)*⟪force (weights p x) p.minus,x.z⟫
    have hE := (bounds p hp K hf hm).1 j hj'
    have hJ := zero_le_one.trans hp.forcePos
    have hvel : |f| ≤ p.g := by
      apply (increments p hp x).2.1.trans
      apply le_trans _ hp.sign
      have hh := mul_le_mul (tick_range p hp x).2
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hJ)
        (mul_nonneg hJ (Real.sqrt_nonneg _)) (step_size p hp).1.le
      nlinarith only [hh]
    have hn : 0 ≤ (orbit p (j+1)).t := by
      rw [BrightnessLogisticHorizon.next]
      change 0 ≤ x.t+f
      change p.g ≤ x.t at hprev
      linarith [neg_abs_le f]
    exact ⟨by nlinarith [hnew,hpayed,hn,hp.floorPos,sq_nonneg ‖part p (j+1)‖],hnew⟩

lemma progress (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K)
    (hm : clock p K ≤ p.M+1) :
    p.γ*p.g*clock p K ≤ ⟪p.u,part p K⟫-⟪p.u,p.a⟫ := by
  have hδ := floor_and_balance p hp K hf hm
  have hh := (step_size p hp).1.le
  have hstep (j : ℕ) (hj : j ∈ Finset.range K) :
      p.γ*p.g*tick p (orbit p j) ≤ ⟪p.u,part p (j+1)⟫-⟪p.u,part p j⟫ := by
    let x := orbit p j
    let Q := mean (weights p x)
    let h := p.κ/p.R
    have hQ : 0 ≤ Q := (votes_range p x).1
    have hq := (hδ j (Finset.mem_range.mp hj).le).1
    have hc := support_force (weights p x) (fun i => (confidence _).1) p.minus p.u hp.separator.2
    have ht := mul_le_mul hq hc (mul_nonneg hp.marginPos.le hQ) (hp.floorPos.le.trans hq)
    rw [part,inner_add_right,real_inner_smul_right,real_inner_smul_right]
    change p.γ*p.g*(h*Q) ≤ ⟪p.u,part p j⟫+h*(x.t*⟪p.u,force (weights p x) p.minus⟫)-⟪p.u,part p j⟫
    change p.g*(p.γ*Q) ≤ x.t*⟪p.u,force (weights p x) p.minus⟫ at ht
    nlinarith only [mul_le_mul_of_nonneg_left ht hh]
  have hs := Finset.sum_le_sum hstep
  rw [← Finset.mul_sum,Finset.sum_range_sub (fun j => ⟪p.u,part p j⟫) K] at hs
  exact hs

lemma before_collision (p : Params) (hp : Valid p) (K : ℕ) (hf : Prefit p K)
    (hm : clock p K ≤ p.M+1) : clock p K < p.M := by
  have hr := radius_bound p hp K hf hm
  have hprog := progress p hp K hf hm
  obtain ⟨_,hb⟩ := floor_and_balance p hp K hf hm K le_rfl
  have hpay := (mul_le_mul_of_nonneg_left hm (nonneg_penalty p hp)).trans (penalty_cost p hp)
  have hnorm : ‖part p K‖^2 ≤ taps (orbit p K) := by
    unfold taps
    nlinarith only [hb,hpay,sq_nonneg p.g,sq_nonneg (orbit p K).a]
  have hs := Real.le_sqrt_of_sq_le (hnorm.trans hr)
  have hinner := (real_inner_le_norm p.u (part p K)).trans
    (mul_le_mul_of_nonneg_right hp.separator.1 (norm_nonneg _))
  have hinner' := (abs_real_inner_le_norm p.u p.a).trans
    (mul_le_mul_of_nonneg_right hp.separator.1 (norm_nonneg _))
  have hinit := neg_abs_le ⟪p.u,p.a⟫
  by_contra! hlate
  have hν := mul_le_mul_of_nonneg_left hlate (mul_nonneg hp.marginPos.le hp.floorPos.le)
  have hc := BrightnessLogisticConstants.collision p hp
  rw [show p.p₀^2+p.q₀^2+(3*p.L+1)*(p.M+1)+2*p.t^2+3 =
    p.p₀^2+p.q₀^2+2*p.t^2+3+(3*p.L+1)*(p.M+1) by ring] at hs
  linarith

end LongTails.Proofs.BrightnessLogisticSeparation
