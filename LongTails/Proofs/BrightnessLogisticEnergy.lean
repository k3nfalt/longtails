import LongTails.Proofs.BrightnessLogisticFastMode

open scoped RealInnerProductSpace

namespace LongTails.Proofs.BrightnessLogisticEnergy

open BrightnessLogisticFastMode

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fast (p t : ℝ) : ℝ := p^2+t^2+2*|p^2-t^2|

noncomputable def energy (p q t : ℝ) (v : E) : ℝ := 1+fast p t+q^2+‖v‖^2

lemma square_change {x u X Y m : ℝ} (hx : |x| ≤ X) (hu : |u| ≤ m*Y)
    (hY : 0 ≤ Y) (hm : m ≤ 1) : |(x+u)^2-x^2| ≤ m*((2*X+Y)*Y) := by
  have haux : |u| ≤ Y := hu.trans (by nlinarith [mul_le_mul_of_nonneg_right hm hY])
  rw [show (x+u)^2-x^2 = (2*x+u)*u by ring,abs_mul]
  have hr : |2*x+u| ≤ 2*X+Y := by
    have h := abs_add_le (2*x) u
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    linarith
  have hX := (abs_nonneg _).trans hx
  nlinarith only [mul_le_mul hr hu (abs_nonneg _) (show 0 ≤ 2*X+Y by positivity)]

omit [InnerProductSpace ℝ E] in
lemma vector_change {v w : E} {X Y m : ℝ} (hv : ‖v‖ ≤ X) (hw : ‖w‖ ≤ m*Y)
    (hY : 0 ≤ Y) (hm : m ≤ 1) : ‖v+w‖^2-‖v‖^2 ≤ m*((2*X+Y)*Y) := by
  have hh := square_change (x := ‖v‖) (u := ‖w‖)
    (by simpa [abs_of_nonneg (norm_nonneg v)] using hv)
    (by simpa [abs_of_nonneg (norm_nonneg w)] using hw) hY hm
  have hn := norm_add_le v w
  have hs := mul_self_le_mul_self (norm_nonneg (v+w)) hn
  nlinarith [le_abs_self ((‖v‖+‖w‖)^2-‖v‖^2)]

lemma fast_forcing (p t u : ℝ) : fast (p+u) t-fast p t ≤ 3*|(p+u)^2-p^2| := by
  have he := abs_sub_abs_le_abs_sub ((p+u)^2-t^2) (p^2-t^2)
  rw [sub_sub_sub_cancel_right] at he
  unfold fast
  linarith [le_abs_self ((p+u)^2-p^2)]

lemma fast_work {p t β W : ℝ} (hb : |β| ≤ 1/2) (hwork : β*p*t ≤ W) (hW : 0 ≤ W) :
    fast (p+β*t) (t+β*p) - fast p t + β^2*(p^2+t^2) ≤ 6*W := by
  have hsq : 0 ≤ 1-β^2 := by
    nlinarith only [mul_self_le_mul_self (abs_nonneg β) hb,sq_abs β]
  have hh := kinetic_dissipation p t β (1/2) hb
  rw [abs_of_nonneg hsq] at hh
  unfold fast
  rcases le_total 0 (β*p*t) with h | h
  · rw [abs_of_nonneg h] at hh
    linarith
  · rw [abs_of_nonpos h] at hh
    linarith

omit [InnerProductSpace ℝ E] in
lemma sizes (p q t : ℝ) (v : E) :
    let S := Real.sqrt (energy p q t v)
    |p| ≤ S ∧ |q| ≤ S ∧ |t| ≤ S ∧ ‖v‖ ≤ S := by
  dsimp only
  unfold energy fast
  have h := abs_nonneg (p^2-t^2)
  refine ⟨Real.le_sqrt_of_sq_le ?_,Real.le_sqrt_of_sq_le ?_,Real.le_sqrt_of_sq_le ?_,
    Real.le_sqrt_of_sq_le ?_⟩ <;>
    nlinarith only [h,sq_abs p,sq_abs q,sq_abs t,sq_nonneg p,sq_nonneg q,sq_nonneg t,sq_nonneg ‖v‖]

omit [InnerProductSpace ℝ E] in
lemma step (p q t β e f m J L : ℝ) (v w : E) (hb : |β| ≤ 1/2)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hwork : β*p*t ≤ m*L*energy p q t v)
    (he : |e| ≤ m*(J*Real.sqrt (energy p q t v)))
    (hf : |f| ≤ m*(J*Real.sqrt (energy p q t v)))
    (hw : ‖w‖ ≤ m*(J*Real.sqrt (energy p q t v))) :
    energy (p+β*t+e) (q+f) (t+β*p) (v+w) + β^2*(p^2+t^2) ≤
    (1+(6*L+16*J+5*J^2)*m)*energy p q t v := by
  let F := energy p q t v
  let S := Real.sqrt F
  have hF : 0 ≤ F := by dsimp [F,energy,fast]; positivity
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hs : S^2=F := Real.sq_sqrt hF
  obtain ⟨hp,hq,ht,hv⟩ := sizes p q t v
  have hy : 0 ≤ J*S := mul_nonneg hJ hS
  have hpt : |p+β*t| ≤ 2*S := by
    apply (abs_add_le ..).trans
    rw [abs_mul]
    have ha := mul_le_mul hb ht (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    change |p| ≤ S at hp
    change |β| * |t| ≤ 1/2*S at ha
    linarith
  have hbase := fast_work hb hwork (mul_nonneg (mul_nonneg hm hL) hF)
  have hforce := (fast_forcing (p+β*t) (t+β*p) e).trans
    (mul_le_mul_of_nonneg_left (square_change hpt he hy hm1) (by norm_num))
  have hslow := (le_abs_self _).trans (square_change hq hf hy hm1)
  have hvv := vector_change hv hw hy hm1
  change _ ≤ (1+(6*L+16*J+5*J^2)*m)*F
  change _ ≤ 6*(m*L*F) at hbase
  change _ ≤ 3*(m*((2*(2*S)+J*S)*(J*S))) at hforce
  change _ ≤ m*((2*S+J*S)*(J*S)) at hslow hvv
  have hsum := add_le_add (add_le_add hbase hforce) (add_le_add hslow hvv)
  have hcoef : 6*(m*L*F)+3*(m*((2*(2*S)+J*S)*(J*S)))+
      (m*((2*S+J*S)*(J*S))+m*((2*S+J*S)*(J*S))) =
      (6*L+16*J+5*J^2)*m*F := by
    conv_rhs => rw [← hs]
    rw [← hs]
    ring
  rw [hcoef] at hsum
  change 1+fast (p+β*t+e) (t+β*p)+(q+f)^2+‖v+w‖^2+β^2*(p^2+t^2) ≤ _
  have hinit : F = 1+fast p t+q^2+‖v‖^2 := rfl
  nlinarith only [hsum,hinit]

end LongTails.Proofs.BrightnessLogisticEnergy
